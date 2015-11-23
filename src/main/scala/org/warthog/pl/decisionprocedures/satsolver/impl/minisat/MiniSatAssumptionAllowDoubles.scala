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
import scala.collection.mutable.HashMap
import scala.util.control.Breaks.break
import scala.util.control.Breaks.breakable

import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.decisionprocedures.satsolver.Model
import org.warthog.pl.decisionprocedures.satsolver.Solver
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.collections.nativeType.IntVec
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.prover.core.MSJCoreProver
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.prover.datastructures.LBool
import org.warthog.pl.formulas.PL
import org.warthog.pl.formulas.PLAtom

/**
 * Solver Wrapper for Minisat (uses MSJCoreProver)
 *
 * @author Konstantin Grupp
 */
class MiniSatAssumptionAllowDoubles(callsUntilFullReset: Int, assumptionsUntilFullReset: Int) extends AbstractMiniSat {

  def this() = this(Int.MaxValue, Int.MaxValue)

  private val assumptions: IntVec = new IntVec()

  // AutoReset functionality to hold assumption vars small  
  private var fullResetCounter = 0
  private val CALLSUNTILFULLRESET = callsUntilFullReset
  private val ASSUMPTIONSUNTILFULLRESET = assumptionsUntilFullReset

  // for dimacs output
  private var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil
  private var assumptionClauses: List[List[ClauseLike[PL, PLLiteral]]] = Nil

  // no extra init necessary

  override def name = {
    var option = "-" + callsUntilFullReset + "-" + assumptionsUntilFullReset
    if (Int.MaxValue == callsUntilFullReset && Int.MaxValue == assumptionsUntilFullReset) {
      option = ""
    }
    "MiniSatAssumptionAllowDoubles" + option
  }

  override def reset() {
    super.reset()
    assumptions.clear()
    assumptionClauses = Nil
    hardClauses = Nil

    fullResetCounter = 0
  }

  override def add(clause: ClauseLike[PL, PLLiteral]) {
    // add clause to solver

    // Add clause without assumption variable if no mark is set (aka a hard clause)
    if (assumptionClauses.isEmpty) {
      addHard(clause)
    } else {

      // add variable to disable clause if needed (for mark()/undo() needed)
      //val (intVarIndex, assumptionVar) = newAssupmtionVar(clause)

      // converts ClauseLike to Set[Int]
      // and adds variables to miniSatJavaInstance, varToID, idToVar
      val clauseWithIDs = getIDsWithPhase(clause)

      // Add clause to miniSatJavaInstance
      val resClause = new IntVec()
      clauseWithIDs.foreach { x => resClause.push(x) }
      val assumptionVar = MSJCoreProver.`var`(assumptions.last())
      resClause.push(getMSJLit(assumptionVar, true))
      miniSatJavaInstance.newClause(resClause, false)

      assumptionClauses = (clause :: assumptionClauses.head) :: assumptionClauses.tail

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
      val (variable, phaseFactor) = (literal.variable, literal.phase)
      getMSJLit(getVariableOrElseUpdate(variable), phaseFactor)
    }).toSet
  }

  private def newAssupmtionVar() = {
    val variable = new PLAtom("AssumptionVar LVL " + assumptions.size())
    val nextID = miniSatJavaInstance.newVar()
    val intVarIndex = assumptions.size()
    assumptions.push(getMSJLit(nextID, false))
    //idToVar += (nextID -> variable)
    (intVarIndex, nextID)
  }

  private def getMSJLit(variable: Int, phase: Boolean) = MSJCoreProver.mkLit(variable, !phase)

  override def mark() {
    assumptionClauses = List() :: assumptionClauses
    newAssupmtionVar()
  }

  override def undo() {
    // bei undo assumption variablen vergessen
    lastState = Solver.UNKNOWN
    if (!assumptionClauses.isEmpty) {
      if (fullResetCounter < CALLSUNTILFULLRESET || assumptions.size() < ASSUMPTIONSUNTILFULLRESET) {
        val assumptionVar = MSJCoreProver.`var`(assumptions.last())
        // assumption variable als unit clause hinzufügen
        val unitClause = new IntVec(1)
        unitClause.push(getMSJLit(assumptionVar, true))
        miniSatJavaInstance.newClause(unitClause, false)

        assumptions.shrink(1)
        assumptionClauses = assumptionClauses.tail
        fullResetCounter += 1
      } else {
        // reset solver completly
        val tempAssumptionClauses = assumptionClauses.tail
        val tempHardClauses = hardClauses
        reset()
        val addHardWrapper = (clause: ClauseLike[PL, PLLiteral]) => add(clause)
        tempHardClauses.foreach(addHardWrapper)
        val addSoftWrapper = (clause: ClauseLike[PL, PLLiteral]) => add(clause)
        // remember clauses are added in reversed order to satsolver
        tempAssumptionClauses.foreach(_.foreach(addSoftWrapper))
      }
    } // else no mark, then ignore undo
  }

  override def forgetLastMark() {
    assumptionClauses match {
      case head :: tail => {
        val addHardWrapper = (clause: ClauseLike[PL, PLLiteral]) => {
          hardClauses = clause :: hardClauses
        }

        // assumption variable als unit clause hinzufügen
        val unitClause = new IntVec(1)
        val assumptionVar = MSJCoreProver.`var`(assumptions.last())
        unitClause.push(getMSJLit(assumptionVar, false))
        miniSatJavaInstance.newClause(unitClause, false)

        head.foreach(addHardWrapper)
        assumptionClauses = tail
        assumptions.shrink(1)
      }
      case _ => // else no mark, then ignore forgetLastMark
    }

  }

  override def sat(): Int = {
    if (lastState == Solver.UNKNOWN) {
      /* call sat only if solver is in unknown state */
      lastState = AbstractMiniSat.miniSatJavaStateToSolverState(miniSatJavaInstance.solve(assumptions))
    }
    lastState
  }

}