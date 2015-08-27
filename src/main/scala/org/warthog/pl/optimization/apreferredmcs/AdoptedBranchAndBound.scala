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
import scala.util.control.Breaks.{ break, breakable }
import collection.mutable.{ Map => MutableMap }
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.collections.{ Vec, IVec }
import org.warthog.pl.optimization.apreferredmcs.impl.ClauseBAB
import org.warthog.pl.optimization.apreferredmcs.impl.VariableBAB
import org.warthog.pl.optimization.apreferredmcs.impl.BABUtil
import org.warthog.pl.optimization.apreferredmcs.impl.VarState

/**
 * @author Konstantin Grupp
 */
class AdoptedBranchAndBound(satSolver: Solver) extends SATBasedAPreferredMCSSolver(satSolver) {

  var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil

  override def name = "AdoptedBranchAndBound"

  override def addHardConstraint(clause: ClauseLike[PL, PLLiteral]) {
    hardClauses = clause :: hardClauses
    super.addHardConstraint(clause)
  }

  override protected def sat(clauses: Traversable[ClauseLike[PL, PLLiteral]] = Set.empty): Boolean = {
    tUsat.start
    val isSAT = satSolver.sat() == Solver.SAT
    tUsat.end
    isSAT
  }

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]) = {
    // works because of modified sat call which does calls no mark/undo
    val partialAssignment = satSolver.getModel().get.toMap

    val upperBound = prepare(softClauses, partialAssignment)

    val hardClausesInt = (0 to hardClauses.size - 1).toList
    val softClausesInt = (0 to softClauses.size - 1).toList

    adoptedBranchAndBound(hardClausesInt, List.empty, softClausesInt, List.empty, upperBound)
  }

  private def adoptedBranchAndBound(hardClauses: List[Int],
                                    hardClausesEmpty: List[Int],
                                    softClauses: List[Int],
                                    softClausesEmpty: List[Int],
                                    upperBound: List[Int]): List[Int] = {
    val (hardClausesSimp, hardClausesSimpEmpty, softClausesSimp, softClausesSimpEmpty) = simplify(hardClauses, softClauses)

    if (!hardClausesSimpEmpty.isEmpty) {
      return List.empty
    }
    if (softClausesSimp.isEmpty) { // all soft clauses satisfied or empty
      return softClausesSimpEmpty
    }
    val lowerBound = softClausesSimpEmpty.union(underestimation(softClausesSimp))

    if (antilex(upperBound, lowerBound)) {
      return upperBound
    }
    val x = pickNextVar
    val currentLevel = decisionLevel
    assign(BABUtil.mkLit(x, false))
    val resultPos = adoptedBranchAndBound(hardClausesSimp, List.empty, softClausesSimp, List.empty, upperBound)
    cancelUntil(currentLevel)
    assign(BABUtil.mkLit(x, true))
    val resultNeg = adoptedBranchAndBound(hardClausesSimp, List.empty, softClausesSimp, List.empty, upperBound)
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
  private def simplify(hardClauses: List[Int], softClauses: List[Int]): (List[Int], List[Int], List[Int], List[Int]) = {
    var hardResult: List[Int] = List.empty
    var hardEmptyClauses: List[Int] = List.empty
    var softResult: List[Int] = List.empty
    var softEmptyClauses: List[Int] = List.empty

    while (qhead < trail.size()) {
      val propLit = trail.get(qhead)
      qhead += 1
      val watchers: IVec[ClauseBAB] = watches.get(propLit)
      var i = 0;
      var j = 0;
      while (i != watchers.size()) {
        if (watchers.get(i).isLit()) {
          val unitClause = watchers.get(i)
          if (!assign(unitClause.lit())) {
            // TODO clause empty
            //if (decisionLevel() == 0) {
            //  ok = false
            //}
            //confl = new MSJClause(2);
            //confl.set(1, not(propLit));
            //confl.set(0, unitClause.lit());
            qhead = trail.size()
            while (i < watchers.size())
              watchers.set(j, watchers.get(i))
              j += 1
              i += 1
          } else {
            watchers.set(j, watchers.get(i))
            j += 1
            i += 1
          }
        } else {
          val c = watchers.get(i)
          i += 1
          // Make sure the false literal is data[1]:
          val false_lit = BABUtil.not(propLit)
          if (c.get(0) == false_lit) {
            c.set(0, c.get(1))
            c.set(1, false_lit)
          }
          // If 0th watch is true, then clause is already satisfied.
          val first = c.get(0);
          if (value(first) == VarState.TRUE) {
            watchers.set(j, c)
            j += 1
          } else {
            // Look for new watch:
            var foundWatch = false
            breakable {
              for (k <- 2 to c.size) {
                if (!foundWatch) {
                  break
                }
                if (value(c.get(k)) != VarState.FALSE) {
                  c.set(1, c.get(k))
                  c.set(k, false_lit)
                  watches.get(BABUtil.not(c.get(1))).push(c)
                  foundWatch = true
                }
              }
            }
            // Did not find watch -- clause is unit under assignment
            if (!foundWatch) {
              watchers.set(j, c)
              j += 1
              if (!assign(first)) {
                // TODO empty clause
                //if (decisionLevel() == 0) {
                //  ok = false
                //}
                //confl = c
                qhead = trail.size()
                while (i < watchers.size())
                  watchers.set(j, watchers.get(i))
                  j += 1
                  i += 1
              }
            }
          }
        }
      }
      watchers.shrink(i - j)
    }
    (hardResult.reverse, hardEmptyClauses, softResult.reverse, softEmptyClauses.reverse)
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
  private def underestimation(softClauses: List[Int]): List[Int] = {
    // TODO
    List()
  }
  
  /**
   * Checks whether the current lower bound is not preferred to the upper bound
   */
  private def antilex(lis1: List[Int], lis2: List[Int]): Boolean = {
    val itLis1 = lis1.iterator
    val itLis2 = lis2.iterator
    while (itLis1.hasNext && itLis2.hasNext) {
      val id1 = itLis1.next
      val id2 = itLis2.next
      if (id1 < id2) {
        return true
      } else if (id2 < id1) {
        return false
      }
    }
    if (!itLis2.hasNext) {
      true
    } else {
      false
    }
  }

  /**
   * *****************************************
   * unit propagation etc.
   * *****************************************
   */

  //var hardClausesAry: Array[ClauseLike[PL, PLLiteral]] = Array.empty
  //var softClausesAry: Array[ClauseLike[PL, PLLiteral]] = Array.empty
  var hardClausesArySim: Array[ClauseBAB] = Array.empty
  var softClausesArySim: Array[ClauseBAB] = Array.empty

  val varToID: MutableMap[PLAtom, Int] = MutableMap()
  val vars: IVec[VariableBAB] = new Vec()
  val watches: IVec[IVec[ClauseBAB]] = new Vec()
  // TODO to improve performance use heap with var activity
  var varStack: List[VariableBAB] = List()

  var qhead: Int = 0
  var trail: IVec[Int] = new Vec()
  var trailLimits: IVec[Int] = new Vec()
  
  var emptySoft: IVec[Int] = new Vec()
  var emptySoftLimits: IVec[Int] = new Vec()

  /**
   * Initial calculation and preparation for unit propagation (simplyfy)
   */
  private def prepare(softClauses: List[ClauseLike[PL, PLLiteral]], assignment: Map[PLAtom, Boolean]) = {
    // create working Array for hard clauses
    //hardClausesAry = new Array(hardClauses.size)
    hardClausesArySim = new Array(hardClauses.size)
    var i = 0
    for (clause <- hardClauses) {
      //hardClausesAry(i) = clause
      hardClausesArySim(i) = newClause(true, i, clause)
      i += 1
    }

    // create working Array for soft clauses
    //softClausesAry = new Array(softClauses.size)
    softClausesArySim = new Array(softClauses.size)
    var upperBound: List[Int] = List()
    var j = 0
    for (clause <- softClauses) {
      var isSat = false
      softClausesArySim(j) = newClause(false, j, clause, (lit: PLLiteral) => {
        if (!isSat) {
          val phaseOpt = assignment.get(lit.variable)
          if (!phaseOpt.isEmpty) {
            if (phaseOpt.get == lit.phase) {
              isSat = true
            }
          }
        }
      })
      if (isSat) {
        upperBound = j :: upperBound
      }
      j += 1
    }
    upperBound.reverse
  }

  private def newVar(variable: PLAtom) = {
    val id = vars.size
    val newVar = new VariableBAB(variable, id)
    varToID += (variable -> id)
    vars.push(newVar)
    varStack = newVar :: varStack
    watches.push(new Vec())
    watches.push(new Vec())
    id
  }

  private def newClause(isHard: Boolean, id: Int, clause: ClauseLike[PL, PLLiteral], worker: (PLLiteral) => Unit = (_) => {}) = {
    val workingClause: Array[Int] = new Array(clause.size)
    var i = 0
    for (lit <- clause.literals) {
      val variable = varToID.getOrElseUpdate(lit.variable, newVar(lit.variable))
      workingClause(i) = BABUtil.mkLit(variable, !lit.phase)
      i += 1
      worker(lit)
    }
    val newClause = new ClauseBAB(isHard, id, clause, workingClause)
    if (clause.size == 1 && assign(workingClause(0))) {
      // TODO variable has already other state -> add to delta
      watches.get(BABUtil.not(workingClause(0))).push(newClause)
    } else {
      // TODO add watches
      watches.get(BABUtil.not(workingClause(0))).push(newClause)
      watches.get(BABUtil.not(workingClause(1))).push(newClause)
    }
    newClause
  }

  private def assume(lit: Int) = {
    trailLimits.push(trail.size)
    assign(lit)
  }

  private def assign(lit: Int): Boolean = {
    if (value(lit) != VarState.UNDEF) {
      value(lit) != VarState.FALSE
    } else {
      val variable = getVar(lit)
      variable.assign(VarState.fromBool(!BABUtil.sign(lit)))
      variable.setLevel(decisionLevel)
      trail.push(lit)
      true
    }
  }
  
  private def cancelUntil(level: Int) {
    if (decisionLevel() > level) {
      for (c <- trail.size - 1 to trailLimits.get(level)) {
        val variable = getVar(trail.get(c));
        variable.assign(VarState.UNDEF);
        //variable.setReason(null);
        //variable.setPolarity(sign(trail.get(c)));
        //if (varHeap.find(variable) == -1) {
//          varHeap.insert(variable);
  //      }
      }
      trail.shrink(trail.size() - trailLimits.get(level));
      trailLimits.shrink(trailLimits.size() - level);
      qhead = trail.size
    }
  }
  
  /**
   * Similar to pickBranchLit
   */
  private def pickNextVar(): Int = {
    while (!varStack.isEmpty) {
      val next = varStack.head
      varStack = varStack.tail
      if (next.assignment() == VarState.UNDEF) {
        return next.getID
      }
    }
    return -1
  }

  /**
   * *********
   * Helpers
   * *********
   */

  private def decisionLevel() = trailLimits.size

  private def getVar(lit: Int) = vars.get(BABUtil.toVar(lit))

  private def value(lit: Int) = {
    val variable = getVar(lit)
    if (BABUtil.sign(lit)) {
      variable.assignment.negate
    } else {
      variable.assignment
    }
  }

}