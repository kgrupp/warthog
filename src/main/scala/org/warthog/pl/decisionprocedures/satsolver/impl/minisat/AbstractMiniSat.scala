/*
 * Copyright (c) 2011-2014, Andreas J. Kuebler & Christoph Zengler & Rouven Walter & Konstantin Grupp
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this
 * list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package org.warthog.pl.decisionprocedures.satsolver.impl.minisat

import scala.collection.mutable.Map
import scala.collection.JavaConverters._
import org.warthog.pl.formulas.{ PLAtom, PL }
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.prover.core.MSJCoreProver
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.collections.nativeType.IntVec
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.prover.datastructures.LBool
import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.decisionprocedures.satsolver.{ Model, Solver }

/**
 * Abstract class for a Adapter to MSJCoreProver
 */
abstract class AbstractMiniSat extends Solver {
  protected var miniSatJavaInstance = new MSJCoreProver()
  protected var lastState = Solver.UNKNOWN
  private val varToID = Map[PLAtom, Int]()
  private val idToVar = Map[Int, PLAtom]()

  override def reset() {
    miniSatJavaInstance = new MSJCoreProver
    lastState = Solver.UNKNOWN
    varToID.clear()
    idToVar.clear()
  }
  
  protected def getVariableOrElseUpdate(variable: PLAtom): Int = {
    varToID.getOrElseUpdate(variable, {
        val nextID = miniSatJavaInstance.newVar()
        idToVar += (nextID -> variable)
        nextID
      })
  }

  override def getModel(): Option[Model] = {
    require(lastState == Solver.SAT || lastState == Solver.UNSAT, "getModel(): Solver needs to be in SAT or UNSAT state!")

    lastState match {
      case Solver.UNSAT => None
      case Solver.SAT => {
        val worker = (lit: Int, phase: Boolean => Boolean, tail: List[PLAtom]) => {
          if (phase(MSJCoreProver.sign(lit))) {
            val variable = idToVar.get(MSJCoreProver.`var`(lit))
            if (variable.isDefined) {
              variable.get :: tail
            } else tail
          } else tail
        }
        
        val map: List[Integer] = miniSatJavaInstance.getModel().asScala.toList
        val positiveVariables = map.foldRight(Nil: List[PLAtom])((f, l) => worker(f, (b) => !b, l))
        val negativeVariables = map.foldRight(Nil: List[PLAtom])((f, l) => worker(f, identity, l))
        Some(Model(positiveVariables, negativeVariables))
      }
    }
  }

  override def getVarState(variable: PLAtom): Option[Boolean] =
    varToID.get(variable) match {
      case None => None
      case Some(v) => Option(miniSatJavaInstance.getVarState(v)) match {
        case None => None
        case Some(b) => b match {
          case LBool.TRUE  => Some(true)
          case LBool.FALSE => Some(false)
          case LBool.UNDEF => None
        }
      }
    }

}

object AbstractMiniSat {
  def miniSatJavaStateToSolverState(miniSatJavaState: Boolean) = miniSatJavaState match {
    case false => Solver.UNSAT
    case true  => Solver.SAT
  }
}