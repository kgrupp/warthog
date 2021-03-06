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
class MiniSatAssumption(callsUntilFullReset: Int) extends AbstractMiniSat {

  def this() = this(Int.MaxValue)

  private val clauseToVar = HashMap[ClauseLike[PL, PLLiteral], Int]()
  private val clauseToID = HashMap[ClauseLike[PL, PLLiteral], Int]()
  private val assumptions: IntVec = new IntVec()

  // AutoReset functionality to hold assumption vars small  
  private var fullResetCounter = 0
  private val CALLSUNTILFULLRESET = callsUntilFullReset

  // for dimacs output
  private var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil
  private var assumptionClauses: List[List[ClauseLike[PL, PLLiteral]]] = Nil
  private var assumptionClausesChecker: List[Map[ClauseLike[PL, PLLiteral], Boolean]] = Nil

  // no extra init necessary

  override def name = {
    var option = "-" + callsUntilFullReset
    if (Int.MaxValue == callsUntilFullReset) {
      option = ""
    }
    "MiniSatAssumption" + option
  }

  override def reset() {
    super.reset()
    assumptions.clear()
    assumptionClauses = Nil
    assumptionClausesChecker = Nil
    hardClauses = Nil
    clauseToVar.clear()
    clauseToID.clear()

    fullResetCounter = 0
  }

  override def add(clause: ClauseLike[PL, PLLiteral]) = addInternal(clause, false, false)
  override def addHard(clause: ClauseLike[PL, PLLiteral]) = addInternal(clause, false, true)

  private def addInternal(clause: ClauseLike[PL, PLLiteral], keepAssumptionClauses: Boolean, isHard: Boolean) {
    // add clause to solver

    // Add clause without assumption variable if no mark is set
    if (isHard || assumptionClauses.isEmpty) {
      // converts ClauseLike to Set[Int]
      // and adds variables to miniSatJavaInstance, varToID, idToVar
      val clauseWithIDs = getIDsWithPhase(clause)

      // Add clause to miniSatJavaInstance
      val resClause = new IntVec()
      clauseWithIDs.foreach { x => resClause.push(x) }
      miniSatJavaInstance.newClause(resClause, false)
      hardClauses = clause :: hardClauses
    } else {

      // add variable to disable clause if needed (for mark()/undo() needed)
      val assumptionVarTest = clauseToVar.get(clause)
      var assumptionVar = 0
      if (assumptionVarTest == None) {
        assumptionVar = newAssupmtionVar(clause)

        // converts ClauseLike to Set[Int]
        // and adds variables to miniSatJavaInstance, varToID, idToVar
        val clauseWithIDs = getIDsWithPhase(clause)

        // Add clause to miniSatJavaInstance
        val resClause = new IntVec()
        clauseWithIDs.foreach { x => resClause.push(x) }
        resClause.push(getMSJLit(assumptionVar, true))
        miniSatJavaInstance.newClause(resClause, false)

      } else {
        assumptionVar = assumptionVarTest.get
        val intVecIndex = clauseToID.get(clause).get

        assumptions.set(intVecIndex, getMSJLit(assumptionVar, false))
      }

      if (!keepAssumptionClauses) {
        assumptionClauses = (clause :: assumptionClauses.head) :: assumptionClauses.tail
        assumptionClausesChecker = (assumptionClausesChecker.head + (clause -> true)) :: assumptionClausesChecker.tail
      }
    }

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

  private def newAssupmtionVar(clause: ClauseLike[PL, PLLiteral]) = {
    val nextID = miniSatJavaInstance.newVar()
    val intVarIndex = assumptions.size()
    assumptions.push(getMSJLit(nextID, false))
    clauseToVar += (clause -> nextID)
    clauseToID += (clause -> intVarIndex)
    nextID
  }

  private def getMSJLit(variable: Int, phase: Boolean) = MSJCoreProver.mkLit(variable, !phase)

  override def mark() {
    assumptionClauses = List() :: assumptionClauses
    assumptionClausesChecker = Map[ClauseLike[PL, PLLiteral], Boolean]() :: assumptionClausesChecker
  }

  override def undo() {
    // TODO bei undo assumption variablen vergessen
    lastState = Solver.UNKNOWN
    if (!assumptionClauses.isEmpty) {
      if (fullResetCounter < CALLSUNTILFULLRESET) {
        for (clause <- assumptionClauses.head) {
          if (!clauseToID.contains(clause)) {
            println(clause)
          } else {

            val intVarIndex = clauseToID.get(clause).get
            val assumptionVar = clauseToVar.get(clause).get
            var clauseNeedToStay = false
            breakable {
              for (checkerMap <- assumptionClausesChecker.tail) {
                if (checkerMap.contains(clause)) {
                  clauseNeedToStay = true
                  break
                }
              }
            }
            if (!clauseNeedToStay) {
              assumptions.set(intVarIndex, getMSJLit(assumptionVar, true))
            }
          }
        }
        assumptionClauses = assumptionClauses.tail
        assumptionClausesChecker = assumptionClausesChecker.tail
        fullResetCounter += 1
      } else {
        // reset solver completly
        val tempAssumptionClauses = assumptionClauses.tail
        val tempAssumptionClausesChecker = assumptionClausesChecker.tail
        val tempHardClauses = hardClauses
        reset()
        assumptionClauses = tempAssumptionClauses
        assumptionClausesChecker = tempAssumptionClausesChecker
        val addHardWrapper = (clause: ClauseLike[PL, PLLiteral]) => addInternal(clause, true, true)
        tempHardClauses.foreach(addHardWrapper)
        val addSoftWrapper = (clause: ClauseLike[PL, PLLiteral]) => addInternal(clause, true, false)
        // remember clauses are added in reversed order to satsolver
        assumptionClauses.foreach(_.foreach(addSoftWrapper))
      }
    } // else no mark, then ignore undo
  }
  
  override def forgetLastMark() {
    assumptionClauses match {
      case head :: tail => {
        head.foreach(addHard)
        assumptionClauses = tail
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