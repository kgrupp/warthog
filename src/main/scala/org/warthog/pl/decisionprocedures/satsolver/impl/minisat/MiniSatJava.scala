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
 * Solver Wrapper for MiniSatJava.
 */
class MiniSatJava extends AbstractMiniSat {
  private var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil
  private var clausesStack: List[ClauseLike[PL, PLLiteral]] = Nil
  private var marks: List[Int] = Nil

  override def name = "MiniSatJava"

  override def reset() {
    super.reset()
    hardClauses = Nil
    clausesStack = Nil
    marks = Nil
  }

  override def add(clause: ClauseLike[PL, PLLiteral]) {
    clausesStack = (clause :: clausesStack)
    addClauseToSolver(clause)

    /* an unsatisfiable formula doesn't get satisfiable by adding clauses */
    if (lastState != Solver.UNSAT)
      lastState = Solver.UNKNOWN
  }

  override def addHard(clause: ClauseLike[PL, PLLiteral]) {
    hardClauses = (clause :: hardClauses)
    addClauseToSolver(clause)

    /* an unsatisfiable formula doesn't get satisfiable by adding clauses */
    if (lastState != Solver.UNSAT)
      lastState = Solver.UNKNOWN
  }

  private def addClauseToSolver(clause: ClauseLike[PL, PLLiteral]) {
    val clauseAsIntVec = new IntVec(clause.literals.map(literal => {
      val (variable, phase) = (literal.variable, literal.phase)
      val id = getVariableOrElseUpdate(variable)
      MSJCoreProver.mkLit(id, !phase)
    }).toArray)

    miniSatJavaInstance.newClause(clauseAsIntVec, false)
  }

  override def mark() {
    marks = clausesStack.length :: marks
  }

  override def undo() {
    marks match {
      case head :: tail => {
        marks = tail
        super.reset()
        clausesStack = clausesStack.drop(clausesStack.length - head)
        hardClauses.foreach(addClauseToSolver(_))
        clausesStack.foreach(addClauseToSolver(_))
      }
      case _ => // No mark, then ignore undo
    }
  }

  override def forgetLastMark() {
    marks match {
      case head :: tail => {
        val (newClausesStack, newHardClauses) = clausesStack.splitAt(clausesStack.length - head)
        newHardClauses.foreach(clause => hardClauses = clause :: hardClauses)
        clausesStack = newClausesStack
        marks = tail
      }
      case _ => // No mark, then ignore forgetLastMark
    }

  }

  override def sat(): Int = {
    if (lastState == Solver.UNKNOWN)
      /* call sat only if solver is in unknown state */
      lastState = AbstractMiniSat.miniSatJavaStateToSolverState(miniSatJavaInstance.solve())
    lastState
  }

}