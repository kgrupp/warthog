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
import java.util.HashMap
import scala.util.control.Breaks.{ break, breakable }

/**
 * Solver Wrapper for Minisat (uses MSJCoreProver)
 *
 * @author Konstantin Grupp
 */
class MiniSatAssumptionJavaMaps(callsUntilFullReset: Int, assumptionsUntilFullReset: Int) extends Solver {

  def this() = this(50, 100)

  private var miniSatJavaInstance = new MSJCoreProver()
  private val varToID = new HashMap[PLAtom, Int]()
  private val idToVar = new HashMap[Int, PLAtom]()
  private val clauseToVar = new HashMap[ClauseLike[PL, PLLiteral], Int]()
  private val clauseToID = new HashMap[ClauseLike[PL, PLLiteral], Int]()
  private val assumptions: IntVec = new IntVec()
  private var lastState = Solver.UNKNOWN

  // AutoReset functionality to hold assumption vars small  
  private var fullResetCounter = 0
  private val CALLSUNTILFULLRESET = callsUntilFullReset
  private val ASSUMPTIONSUNTILFULLRESET = assumptionsUntilFullReset

  // for dimacs output
  private var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil
  private var assumptionClauses: List[List[ClauseLike[PL, PLLiteral]]] = Nil
  private var assumptionClausesChecker: List[Map[ClauseLike[PL, PLLiteral], Boolean]] = Nil

  // no extra init necessary

  override def name = "MinisatAssumptionJavaMaps-" + callsUntilFullReset + "-" + assumptionsUntilFullReset

  override def reset() {
    assumptions.clear()
    assumptionClauses = Nil
    assumptionClausesChecker = Nil
    hardClauses = Nil
    clauseToVar.clear()
    clauseToID.clear()
    miniSatJavaInstance = new MSJCoreProver()
    varToID.clear()
    idToVar.clear()
    lastState = Solver.UNKNOWN

    fullResetCounter = 0
  }

  override def add(clause: ClauseLike[PL, PLLiteral]) = addInternal(clause, false, false)

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
      val assumptionVarTest = Option(clauseToVar.get(clause))
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
        val intVecIndex = Option(clauseToID.get(clause)).get

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
      val (v, phaseFactor) = (literal.variable, literal.phase)
      var nextIDtest = Option(varToID.get(v))
      var nextID = -1
      if (nextIDtest == None) {
        nextID = miniSatJavaInstance.newVar()
        idToVar.put(nextID, v)
        varToID.put(v, nextID)
      } else {
        nextID = nextIDtest.get
      }
      getMSJLit(nextID, phaseFactor)
    }).toSet
  }

  private def newAssupmtionVar(clause: ClauseLike[PL, PLLiteral]) = {
    val variable = new PLAtom("AssumptionVar for: " + clause.toString())
    val nextID = miniSatJavaInstance.newVar()
    val intVarIndex = assumptions.size()
    assumptions.push(getMSJLit(nextID, false))
    idToVar.put(nextID, variable)
    varToID.put(variable, nextID)
    clauseToVar.put(clause, nextID)
    clauseToID.put(clause, intVarIndex)
    nextID
  }

  private def getMSJLit(variable: Int, phase: Boolean) = MSJCoreProver.mkLit(variable, !phase)

  override def mark() {
    assumptionClauses = List() :: assumptionClauses
    assumptionClausesChecker = Map[ClauseLike[PL, PLLiteral], Boolean]() :: assumptionClausesChecker
  }

  override def undo() {
    lastState = Solver.UNKNOWN
    if (!assumptionClauses.isEmpty) {
      if (fullResetCounter < CALLSUNTILFULLRESET || assumptions.size() < ASSUMPTIONSUNTILFULLRESET) {
        for (clause <- assumptionClauses.head) {
          if (!clauseToID.containsKey(clause)) {
            println(clause)
          } else {

            val intVarIndex = Option(clauseToID.get(clause)).get
            val assumptionVar = Option(clauseToVar.get(clause)).get
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
        val addHard = (clause: ClauseLike[PL, PLLiteral]) => addInternal(clause, true, true)
        tempHardClauses.foreach(addHard)
        val addSoft = (clause: ClauseLike[PL, PLLiteral]) => addInternal(clause, true, false)
        // remember clauses are added in reversed order to satsolver
        assumptionClauses.foreach(_.foreach(addSoft))
      }
    } // else no mark, then ignore undo
  }

  override def sat(): Int = {
    if (lastState == Solver.UNKNOWN) {
      /* call sat only if solver is in unknown state */
      lastState = MiniSatAssumptionJavaMaps.minisatStateToSolverState(miniSatJavaInstance.solve(assumptions))
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
          .map { lit => idToVar.get(MSJCoreProver.`var`(lit)) }.toList
        val negativeVariables = map.filter { lit => MSJCoreProver.sign(lit) }
          .map { lit => idToVar.get(MSJCoreProver.`var`(lit)) }.toList
        Some(Model(positiveVariables, negativeVariables))
      }
    }
  }

  override def getVarState(variable: PLAtom): Option[Boolean] =
    Option(varToID.get(variable)) match {
      case Some(v) => miniSatJavaInstance.getVarState(v) match {
        case LBool.TRUE  => Some(true)
        case LBool.FALSE => Some(false)
        case LBool.UNDEF => None
      }
      case None   => None
    }
}

object MiniSatAssumptionJavaMaps {

  private def minisatStateToSolverState(minisatState: Boolean) = minisatState match {
    case false => Solver.UNSAT
    case true  => Solver.SAT
  }
}