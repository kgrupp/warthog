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

package org.warthog.pl.optimization.apreferredmcs

import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.decisionprocedures.satsolver.Solver
import org.warthog.pl.formulas.PL
import org.warthog.pl.formulas.PLAtom
import org.warthog.pl.optimization.apreferredmcs.impl.ClauseBAB
import scala.util.control.Breaks.{break, breakable}

/**
 * @author Konstantin Grupp
 */
class AdoptedBranchAndBound(satSolver:Solver) extends SATBasedAPreferredMCSSolver(satSolver) {
  
  var hardClauses : List[ClauseLike[PL, PLLiteral]] = Nil
  
  override def name = "AdoptedBranchAndBound"
  
  var mapOfVars:Map[PLAtom,Boolean] = Map()
  
  override def addHardConstraint(clause: ClauseLike[PL, PLLiteral]) {
    hardClauses = clause :: hardClauses
    clause.literals.foreach { lit => {
      mapOfVars.getOrElse(lit.variable, mapOfVars += (lit.variable -> false))
    }}
    super.addHardConstraint(clause)
  }

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    this.areHardConstraintsSatisfiable()
    val partialAssignment = satSolver.getModel().get.toMap
    val upperBound = calcUpperBound(softClauses, partialAssignment)
    var varStack:List[PLAtom] = Nil
    mapOfVars.foreach(v => {
      val phaseOpt = partialAssignment.get(v._1)
      if (phaseOpt.isEmpty) {
        varStack = v._1 :: varStack
      }
    })
    adoptedBranchAndBound(hardClauses, softClauses, upperBound, partialAssignment, varStack)
  }
  
  /**
   * Calcs upper bound and sets variables
   */
  private def calcUpperBound(softClauses: List[ClauseLike[PL, PLLiteral]], 
      partialAssignment: Map[PLAtom, Boolean]): Set[ClauseLike[PL, PLLiteral]] = {
    var delta:Set[ClauseLike[PL, PLLiteral]] = Set()
    for (clause <- softClauses) {
      Thread.sleep(0) // to handle interrupts
      var clauseIsTrue = false
      for (lit <- clause.literals) {
        val phaseOpt = partialAssignment.get(lit.variable)
        var phase = false
        if (!phaseOpt.isEmpty) {
          phase = phaseOpt.get
        }
        
        if (phase == lit.phase) {
          clauseIsTrue = true
        }
      }
      if (!clauseIsTrue) {
        delta += clause
      }
    }
    delta
  }
  
  private def adoptedBranchAndBound(hardClauses: List[ClauseLike[PL, PLLiteral]], 
      softClauses: List[ClauseLike[PL, PLLiteral]], 
      upperBound: Set[ClauseLike[PL, PLLiteral]], 
      assignment: Map[PLAtom, Boolean],
      varStack: List[PLAtom]): Set[ClauseLike[PL, PLLiteral]] = {
    val (hardClausesSimp, containsEmptyClauseHard, containsOnlyEmptyClausesHard) = simplify(hardClauses, assignment)
    val (softClausesSimp, containsEmptyClauseSoft, containsOnlyEmptyClausesSoft) = simplify(softClauses, assignment)
    
    if (containsEmptyClauseHard) {
      return Set.empty
    }
    if (softClausesSimp.isEmpty || containsOnlyEmptyClausesSoft) {
      return emptyClauses2OrginalClauses(softClausesSimp)
    }
    val lowerBound = emptyClauses2OrginalClauses(softClausesSimp).union(underestimation(softClausesSimp))
    
    if (antilex(lowerBound, upperBound)) {
      return upperBound
    }
    val x = varStack.head
    val resultPos = adoptedBranchAndBound(hardClausesSimp, softClausesSimp, upperBound, assignment + (x -> true), varStack.tail)
    val resultNeg = adoptedBranchAndBound(hardClausesSimp, softClausesSimp, upperBound, assignment + (x -> false), varStack.tail)
    if (antilex(resultPos, upperBound)) {
      return resultPos
    } else if (antilex(resultNeg, upperBound)) {
      return resultNeg
    } else {
      return upperBound
    }
  }
  
  /**
   * The function Simplify simplifies the given clause set by applying the 
   * partial assignment and the additional inference rules. Satisfied 
   * clauses will be removed from the set. Returns 2 flags
   *  containsEmptyClauses - the list contains empty clauses
   *  containsOnlyEmptyClauses - the list has only empty clauses
   */
  private def simplify(clauses: List[ClauseLike[PL, PLLiteral]], assignment: Map[PLAtom, Boolean]): (List[ClauseLike[PL, PLLiteral]], Boolean, Boolean) = {
    var containsEmptyClauses = false
    var containsOnlyEmptyClauses = false
    var result:List[ClauseLike[PL, PLLiteral]] = List.empty
    
    for (clause <- clauses) {
      Thread.sleep(0) // to handle interrupts
      val newClause = new ClauseBAB(clause, assignment)
      
      // delete/ignore satisfied clauses
      if (!newClause.isSatisfied) { // clause is open or empty
        result = clause :: result
      }
      containsEmptyClauses ||= newClause.isEmpty
      containsOnlyEmptyClauses &&= newClause.isEmpty
    }
    
    (result.reverse, containsEmptyClauses, containsOnlyEmptyClauses)
  }
  
  /**
   * Function EmptyClauses2OrginalClauses delivers the set of unsatisfied 
   * original clauses. For the non-trivial case that there are clauses not 
   * satisfied or empty yet, we build an underestimation consisting of: 
   *  (i)  Original clauses currently unsatisfied 
   *       (EmptyClauses2OrginalClauses), and 
   *  (ii) a clause set (Underestimation) of original clauses which will 
   *       become unsatisfied under the current assignment.
   */
  private def emptyClauses2OrginalClauses(softClauses:List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    // TODO
    Set()
  }
  
  /**
   * a clause set which will become unsatisfied under the current assignment
   */
  private def underestimation(softClauses:List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    // TODO
    Set()
  }
  
  /**
   * Checks whether the current lower bound is not preferred to the upper bound
   */
  private def antilex(lowerBound: Set[ClauseLike[PL, PLLiteral]], upperBound: Set[ClauseLike[PL, PLLiteral]]):Boolean = {
    // TODO
    true
  }
  
}