/*
 * Copyright (c) 2011-2014, Andreas J. Kuebler & Christoph Zengler & Rouven Walter
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

package org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava

import scala.collection.JavaConverters._
import scala.collection.mutable.Map
import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.decisionprocedures.satsolver.Model
import org.warthog.pl.decisionprocedures.satsolver.Solver
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.collections.nativeType.IntVec
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.prover.core.MSJCoreProver
import org.warthog.pl.formulas.PL
import org.warthog.pl.formulas.PLAtom
import scala.collection.mutable.HashMap

/**
 * Solver Wrapper for Minisat (uses MSJCoreProver)
 */
class MinisatRework1 extends Solver {
  private var minisatInstance = new MSJCoreProver()
  private val varToID = HashMap[PLAtom, Int]()
  private val idToVar = HashMap[Int, PLAtom]()
  private val clauseToVar = HashMap[ClauseLike[PL, PLLiteral], Int]()
  private val clauseToID = HashMap[ClauseLike[PL, PLLiteral], Int]()
  private val assumptions:IntVec = new IntVec()
  private var assumptionClauses:List[List[ClauseLike[PL, PLLiteral]]] = Nil
  private var lastState = Solver.UNKNOWN

  // no extra init necessary

  override def name = "MinisatRework1"
  
  override def reset() {
    assumptions.clear()
    assumptionClauses = Nil
    clauseToVar.clear()
    clauseToID.clear()
    minisatInstance = new MSJCoreProver()
    varToID.clear()
    idToVar.clear()
    lastState = Solver.UNKNOWN
  }

  override def add(clause: ClauseLike[PL, PLLiteral]) {
    // add clause to solver
    
    // Add clause without assumption variable if no mark is set
    if (assumptionClauses.isEmpty) {
      // converts ClauseLike to Set[Int]
      // and adds variables to minisatInstance, varToID, idToVar
      val clauseWithIDs = getIDsWithPhase(clause)
      
      // Add clause to minisatInstance
      val resClause = new IntVec()
      clauseWithIDs.foreach { x => resClause.push(x) }
      minisatInstance.newClause(resClause, false)
    } else {
    
      // add variable to disable clause if needed (for mark()/undo() needed)
      val assumptionVarTest = clauseToVar.get(clause)
      var assumptionVar = 0
      if (assumptionVarTest == None) {
        assumptionVar = newAssupmtionVar(clause)
        
        // converts ClauseLike to Set[Int]
        // and adds variables to minisatInstance, varToID, idToVar
        val clauseWithIDs = getIDsWithPhase(clause)
        
        // Add clause to minisatInstance
        val resClause = new IntVec()
        clauseWithIDs.foreach { x => resClause.push(x) }
        resClause.push(getMSJLit(assumptionVar, true, false))
        minisatInstance.newClause(resClause, false)
        
        
      } else {
        assumptionVar = assumptionVarTest.get
        val intVecIndex = clauseToID.get(clause).get
        
        assumptions.set(intVecIndex, getMSJLit(assumptionVar, false, true))
      }
      assumptionClauses = (clause :: assumptionClauses.head) :: assumptionClauses.tail
    }
    
    if (lastState != Solver.UNSAT)
      lastState = Solver.UNKNOWN
  }

  /**
   * converts ClauseLike[PL, PLLiteral] to Set[Int]
   * and adds variables to minisatInstance, varToID, idToVar
   */
  private def getIDsWithPhase(clause: ClauseLike[PL, PLLiteral]): Set[Int] = {
    clause.literals.map(literal => {
      val (v, phaseFactor) = (literal.variable, literal.phase)
      getMSJLit(varToID.getOrElseUpdate(v, {
        val nextID = minisatInstance.newVar()
        idToVar += (nextID -> v)
        nextID
      }), phaseFactor, false)
    }).toSet
  }
  
  private def newAssupmtionVar(clause: ClauseLike[PL, PLLiteral]) = {
    val variable = new PLAtom("AssumptionVar for: " + clause.toString())
    val nextID = minisatInstance.newVar()
    val intVarIndex = assumptions.size()
    assumptions.push(getMSJLit(nextID, false, true))
    idToVar += (nextID -> variable)
    varToID += (variable -> nextID)
    clauseToVar += (clause -> nextID)
    clauseToID += (clause -> intVarIndex)
    nextID
  }
  
  private def getMSJLit(variable:Int, phase:Boolean, isAssumption:Boolean) = {
    if (isAssumption) {
      MSJCoreProver.mkLit(variable, phase)
    } else {
      MSJCoreProver.mkLit(variable, phase)
    }
  }

  override def mark() {
    val newHead = List()
    assumptionClauses = List() :: assumptionClauses
  }

  override def undo() {
    lastState = Solver.UNKNOWN
    if (!assumptionClauses.isEmpty) {
      // TODO maybe a bug with double clauses
      for (clause <- assumptionClauses.head) {
        val intVarIndex = clauseToID.get(clause).get
        val assumptionVar = clauseToVar.get(clause).get
        assumptions.set(intVarIndex, getMSJLit(assumptionVar, true, true))
      }
      assumptionClauses = assumptionClauses.tail
    } // else no mark, then ignore undo
  }

  override def sat(): Int = {
    if (lastState == Solver.UNKNOWN) {
      /* call sat only if solver is in unknown state */
      lastState = MinisatRework1.minisatStateToSolverState(minisatInstance.solve(assumptions))
    }
    lastState
  }

  override def getModel(): Option[Model] = {
    require(lastState == Solver.SAT || lastState == Solver.UNSAT, "getModel(): Solver needs to be in SAT or UNSAT state!")

    val map:List[Integer] = minisatInstance.getModel().asScala.toList;
    
    lastState match {
      case Solver.UNSAT => None
      case Solver.SAT => {
        val positiveVariables = map.filter { lit => !MSJCoreProver.sign(lit) }.map { lit => idToVar(lit >> 1) }.toList
        val negativeVariables = map.filter { lit => MSJCoreProver.sign(lit) }.map { lit => idToVar(lit >> 1) }.toList
        Some(Model(positiveVariables, negativeVariables))
      }
    }
  }
  
}

object MinisatRework1 {
  
  private def minisatStateToSolverState(minisatState: Boolean) = minisatState match {
    case false => Solver.UNSAT
    case true => Solver.SAT
  }
}