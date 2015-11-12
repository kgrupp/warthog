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

import scala.collection.JavaConverters._
import scala.collection.mutable.Map
import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.decisionprocedures.satsolver.Model
import org.warthog.pl.decisionprocedures.satsolver.Solver
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.collections.nativeType.IntVec
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.prover.core.MSJCoreProver
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.prover.datastructures.LBool
import org.warthog.pl.formulas.PL
import org.warthog.pl.formulas.PLAtom
import scala.collection.mutable.HashMap
import scala.util.control.Breaks.{ break, breakable }

/**
 * Solver Wrapper for Minisat (uses MSJCoreProver)
 *
 * @author Konstantin Grupp
 */
class MiniSatAssumptionAllowDoubles(callsUntilFullReset: Int, assumptionsUntilFullReset: Int) extends Solver {

  def this() = this(Int.MaxValue, Int.MaxValue)

  private var miniSatJavaInstance = new MSJCoreProver()
  private val varToID = HashMap[PLAtom, Int]()
  private val idToVar = HashMap[Int, PLAtom]()
  //private val clauseToVar = HashMap[ClauseLike[PL, PLLiteral], Int]()
  //private val clauseToID = HashMap[ClauseLike[PL, PLLiteral], Int]()
  private val assumptions: IntVec = new IntVec()
  private var lastState = Solver.UNKNOWN

  // AutoReset functionality to hold assumption vars small  
  private var fullResetCounter = 0
  private val CALLSUNTILFULLRESET = callsUntilFullReset
  private val ASSUMPTIONSUNTILFULLRESET = assumptionsUntilFullReset

  // for dimacs output
  private var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil
  private var assumptionClauses: List[List[(ClauseLike[PL, PLLiteral], Int, Int)]] = Nil

  // no extra init necessary

  override def name = {
    var option = callsUntilFullReset + "-" + assumptionsUntilFullReset
    if (Int.MaxValue == callsUntilFullReset && Int.MaxValue == assumptionsUntilFullReset) {
      option = "noReset"
    }
    "MiniSatAssumptionAllowDoubles-" + option
  }

  override def reset() {
    assumptions.clear()
    assumptionClauses = Nil
    hardClauses = Nil
    //clauseToVar.clear()
    //clauseToID.clear()
    miniSatJavaInstance = new MSJCoreProver()
    varToID.clear()
    idToVar.clear()
    lastState = Solver.UNKNOWN

    fullResetCounter = 0
  }

  override def add(clause: ClauseLike[PL, PLLiteral]) {
    // add clause to solver

    // Add clause without assumption variable if no mark is set (aka a hard clause)
    if (assumptionClauses.isEmpty) {
      addHard(clause)
    } else {

      // add variable to disable clause if needed (for mark()/undo() needed)
      val (intVarIndex, assumptionVar) = newAssupmtionVar(clause)

      // converts ClauseLike to Set[Int]
      // and adds variables to miniSatJavaInstance, varToID, idToVar
      val clauseWithIDs = getIDsWithPhase(clause)

      // Add clause to miniSatJavaInstance
      val resClause = new IntVec()
      clauseWithIDs.foreach { x => resClause.push(x) }
      resClause.push(getMSJLit(assumptionVar, true))
      miniSatJavaInstance.newClause(resClause, false)

      assumptionClauses = ((clause, intVarIndex, assumptionVar) :: assumptionClauses.head) :: assumptionClauses.tail

      if (lastState != Solver.UNSAT)
        lastState = Solver.UNKNOWN
    }
  }

  override def addHard(clause: ClauseLike[PL, PLLiteral]) {
    // converts ClauseLike to Set[Int]
    // and adds variables to miniSatJavaInstance, varToID, idToVar
    val clauseWithIDs = getIDsWithPhase(clause)

    // Add clause to miniSatJavaInstance
    val resClause = new IntVec()
    clauseWithIDs.foreach { x => resClause.push(x) }
    miniSatJavaInstance.newClause(resClause, false)
    hardClauses = clause :: hardClauses

    if (lastState != Solver.UNSAT)
      lastState = Solver.UNKNOWN
  }

  /**
   * converts ClauseLike[PL, PLLiteral] to Set[Int]
   * and adds variables to miniSatJavaInstance, varToID, idToVar
   */
  private def getIDsWithPhase(clause: ClauseLike[PL, PLLiteral]): Set[Int] = {
    clause.literals.map(literal => {
      val (v, phaseFactor) = (literal.variable, literal.phase)
      getMSJLit(varToID.getOrElseUpdate(v, {
        val nextID = miniSatJavaInstance.newVar()
        idToVar += (nextID -> v)
        nextID
      }), phaseFactor)
    }).toSet
  }

  private def newAssupmtionVar(clause: ClauseLike[PL, PLLiteral]) = {
    val variable = new PLAtom("AssumptionVar for: " + clause.toString())
    val nextID = miniSatJavaInstance.newVar()
    val intVarIndex = assumptions.size()
    assumptions.push(getMSJLit(nextID, false))
    idToVar += (nextID -> variable)
    varToID += (variable -> nextID)
    //clauseToVar += (clause -> nextID)
    //clauseToID += (clause -> intVarIndex)
    (intVarIndex, nextID)
  }

  private def getMSJLit(variable: Int, phase: Boolean) = MSJCoreProver.mkLit(variable, !phase)

  override def mark() {
    assumptionClauses = List() :: assumptionClauses
  }

  override def undo() {
    // TODO bei undo assumption variablen vergessen
    lastState = Solver.UNKNOWN
    if (!assumptionClauses.isEmpty) {
      if (fullResetCounter < CALLSUNTILFULLRESET || assumptions.size() < ASSUMPTIONSUNTILFULLRESET) {
        for ((_, intVarIndex, assumptionVar) <- assumptionClauses.head) {
          assumptions.set(intVarIndex, getMSJLit(assumptionVar, true))
        }
        assumptionClauses = assumptionClauses.tail
        fullResetCounter += 1
      } else {
        // reset solver completly
        val tempAssumptionClauses = assumptionClauses.tail
        val tempHardClauses = hardClauses
        reset()
        val addHardWrapper = (clause: ClauseLike[PL, PLLiteral]) => add(clause)
        tempHardClauses.foreach(addHardWrapper)
        val addSoftWrapper = Function.tupled((clause: ClauseLike[PL, PLLiteral], intVarIndex: Int, assumptionVar: Int) => add(clause))
        // remember clauses are added in reversed order to satsolver
        tempAssumptionClauses.foreach(_.foreach(addSoftWrapper))
      }
    } // else no mark, then ignore undo
  }

  override def forgetAllMarks() {
    val addHardWrapper = Function.tupled((clause: ClauseLike[PL, PLLiteral], intVarIndex: Int, assumptionVar: Int) => addHard(clause))
    assumptionClauses.foreach(_.foreach(addHardWrapper))
    assumptionClauses = Nil
  }

  override def sat(): Int = {
    if (lastState == Solver.UNKNOWN) {
      /* call sat only if solver is in unknown state */
      lastState = MiniSatAssumptionAllowDoubles.minisatStateToSolverState(miniSatJavaInstance.solve(assumptions))
    }
    lastState
  }

  override def getModel(): Option[Model] = {
    require(lastState == Solver.SAT || lastState == Solver.UNSAT, "getModel(): Solver needs to be in SAT or UNSAT state!")

    lastState match {
      case Solver.UNSAT => None
      case Solver.SAT => {
        val map: List[Integer] = miniSatJavaInstance.getModel().asScala.toList
        val positiveVariables = map.filter { lit => !MSJCoreProver.sign(lit) }
          .map { lit => idToVar(MSJCoreProver.`var`(lit)) }.toList
        val negativeVariables = map.filter { lit => MSJCoreProver.sign(lit) }
          .map { lit => idToVar(MSJCoreProver.`var`(lit)) }.toList
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

object MiniSatAssumptionAllowDoubles {

  private def minisatStateToSolverState(minisatState: Boolean) = minisatState match {
    case false => Solver.UNSAT
    case true  => Solver.SAT
  }
}