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

  override def name = "AdoptedBranchAndBound"

  override def reset() {
    super.reset()

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

    val hardClausesInt = new Vec[Int](hardClauses.size)
    for (i <- 0 to hardClauses.size - 1) {
      hardClausesInt.push(i)
    }
    val softClausesInt = new Vec[Int](softClauses.size)
    for (i <- 0 to softClauses.size - 1) {
      softClausesInt.push(i)
    }

    val resultVec = adoptedBranchAndBound(hardClausesInt, new Vec, softClausesInt, new Vec, upperBound, initialVarStack)
    if (!resultVec.isEmpty) {
      var result = List[Int]()
      for (i <- resultVec.size - 1 to 0 by -1) {
        result = resultVec.get(i) :: result
      }
      result
    } else {
      List()
    }
  }

  val emptyVecInt = new Vec[Int]()

  private def adoptedBranchAndBound(hardClauses: Vec[Int],
                                    hardClausesEmpty: Vec[Int],
                                    softClauses: Vec[Int],
                                    softClausesEmpty: Vec[Int],
                                    upperBound: Vec[Int],
                                    varStack: List[VariableBAB]): Vec[Int] = {
    myPrintln("adoptedBranchAndBound:\n" + hardClauses + "\n" + hardClausesEmpty + "\n" + softClauses + "\n" + softClausesEmpty + "\n" + upperBound + "\n" + varStack)
    val (hardClausesSimp, hardClausesSimpEmpty, softClausesSimp, softClausesSimpEmpty) = simplify(hardClauses, hardClausesEmpty, softClauses, softClausesEmpty)

    if (!hardClausesSimpEmpty.isEmpty) {
      return new Vec[Int]()
    }
    if (softClausesSimp.isEmpty) { // all soft clauses satisfied or empty
      return softClausesSimpEmpty
    }
    val lowerBound = underestimation(softClausesSimp, softClausesSimpEmpty)

    if (antilex(upperBound, lowerBound)) {
      return upperBound
    }
    val (x, newVarStack) = pickNextVar(varStack)
    if (x == -1) {
      throw new AssertionError("TODO need to assign new var, but already all are set")
    }
    myPrintln("newAssumptionVar: " + x + " on decisionLevel " + decisionLevel)
    myPrintln(varStack.toString)
    val currentLevel = decisionLevel
    if (!assume(BABUtil.mkLit(x, false))) {
      return throw new AssertionError("already assigned other way")
    }
    val resultPos = adoptedBranchAndBound(hardClausesSimp, emptyVecInt, softClausesSimp, emptyVecInt, upperBound, newVarStack)
    cancelUntil(currentLevel)
    if (!assume(BABUtil.mkLit(x, true))) {
      return throw new AssertionError("already assigned other way")
    }
    val resultNeg = adoptedBranchAndBound(hardClausesSimp, emptyVecInt, softClausesSimp, emptyVecInt, upperBound, newVarStack)
    myPrintln("bounds:\n"+resultPos+"\n"+resultNeg+"\n"+upperBound)
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
  private def simplify(hardClauses: Vec[Int],
                       hardClausesEmpty: Vec[Int],
                       softClauses: Vec[Int],
                       softClausesEmpty: Vec[Int]): (Vec[Int], Vec[Int], Vec[Int], Vec[Int]) = {
    var satNewHard = List[Int]()
    var satNewSoft = List[Int]()
    var emptyNewHard = List[Int]()
    var emptyNewSoft = List[Int]()

    while (qhead < trail.size()) {
      val propLit = trail.get(qhead)
      myPrintln("simplify: " + qhead + " < " + trail.size + " propLit: " + propLit)
      qhead += 1
      val watchers: IVec[ClauseBAB] = watches.get(propLit)
      var i = 0;
      var j = 0;
      while (i != watchers.size()) {
        myPrintln("simplify: watchers " + i + " < " + watchers.size + " clause: " + watchers.get(i))
        if (watchers.get(i).isLit()) {
          val unitClause = watchers.get(i)
          if (!assign(unitClause.lit())) {
            // clause empty
            if (unitClause.isHard) {
              emptyNewHard = unitClause.getID :: emptyNewHard
            } else {
              emptyNewSoft = unitClause.getID :: emptyNewSoft
            }
            /*if (decisionLevel() == 0) {
              ok = false
            }
            confl = new MSJClause(2);
            confl.set(1, not(propLit));
            confl.set(0, unitClause.lit());
            qhead = trail.size()
            while (i < watchers.size()) {
              watchers.set(j, watchers.get(i))
              j += 1
              i += 1
            }*/
          } else {
            if (unitClause.isHard) {
              satNewHard = unitClause.getID :: satNewHard
            } else {
              satNewSoft = unitClause.getID :: satNewSoft
            }
            watchers.set(j, watchers.get(i))
            j += 1
            i += 1
          }
        } else { // watched clause has more than one literal
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
            // clause is satisfied
            if (c.isHard()) {
              satNewHard = c.getID :: satNewHard
            } else {
              satNewSoft = c.getID :: satNewSoft
            }
            watchers.set(j, c)
            j += 1
          } else {
            // Look for new watch:
            var foundWatch = false
            breakable {
              for (k <- 2 to c.size - 1) {
                if (value(c.get(k)) != VarState.FALSE) {
                  c.set(1, c.get(k))
                  c.set(k, false_lit)
                  watches.get(BABUtil.not(c.get(1))).push(c)
                  foundWatch = true
                  break
                }
              }
            }
            // Did not find watch -- clause is unit under assignment
            if (!foundWatch) {
              watchers.set(j, c)
              j += 1
              if (!assign(first)) {
                // empty clause
                if (c.isHard) {
                  emptyNewHard = c.getID :: emptyNewHard
                } else {
                  emptyNewSoft = c.getID :: emptyNewSoft
                }
                /*if (decisionLevel() == 0) {
                  ok = false
                }
                confl = c
                qhead = trail.size()
                while (i < watchers.size()) {
                  watchers.set(j, watchers.get(i))
                  j += 1
                  i += 1
                }*/
              }
            } // found new watch -> not empty but still false
          }
        }
      }
      watchers.shrink(i - j)
    }
    // combine old result with newer information
    myPrintln("simplify (changed clauses):\n" + satNewHard + "\n" + emptyNewHard + "\n" + satNewSoft + "\n" + emptyNewSoft)
    val (resultHard, resultHardEmpty) = combineVecs(hardClauses, hardClausesEmpty, satNewHard, emptyNewHard)
    val (resultSoft, resultSoftEmpty) = combineVecs(softClauses, softClausesEmpty, satNewSoft, emptyNewSoft)
    myPrintln("simplify (result):\n" + resultHard + "\n" + resultHardEmpty + "\n" + resultSoft + "\n" + resultSoftEmpty)
    for (i <- 0 to resultSoft.size-1) {
      myPrintln("softClause not satisfied: "+softClausesArySim(resultSoft.get(i)))
    }
    (resultHard, resultHardEmpty, resultSoft, resultSoftEmpty)
  }

  private def combineVecs(clauses: Vec[Int], clausesEmpty: Vec[Int], satNew: List[Int], emptyNew: List[Int]): (Vec[Int], Vec[Int]) = {
    // sort satNew and emptyNew because they may be not in order to do a combination in linear time
    var clID = 0
    var itNewSat = satNew.sortWith(_ < _).distinct.iterator // TODO efficient duplicate elimination
    var clNewSat = -1
    if (itNewSat.hasNext) {
      clNewSat = itNewSat.next
    }
    val emptyNewSorted = emptyNew.sortWith(_ < _).distinct // TODO efficient duplicate elimination
    var itNewEm = emptyNewSorted.iterator
    var clNewEm = -1
    if (itNewEm.hasNext) {
      clNewEm = itNewEm.next
    }

    // calc result for clauses which are false
    val result = new Vec[Int](clauses.size - satNew.size - emptyNew.size)
    while (clID < clauses.size) {
      val currentCl = clauses.get(clID)
      if (currentCl == clNewSat) {
        if (itNewSat.hasNext) {
          clNewSat = itNewSat.next
        } else {
          clNewSat = -1
        }
      } else if (currentCl == clNewEm) {
        if (itNewEm.hasNext) {
          clNewEm = itNewEm.next
        } else {
          clNewEm = -1
        }
      } else {
        val currentClause = softClausesArySim(currentCl)
        if (value(currentClause.get(0)) == VarState.TRUE) {
          // clause is satisfied
        } else {
          result.push(currentCl)
        }
      }
      clID += 1
    }

    // calc result for empty Clauses
    val resultEmpty = new Vec[Int](clausesEmpty.size + emptyNew.size)
    var clEmID = 0
    itNewEm = emptyNewSorted.iterator
    clNewEm = -1
    if (itNewEm.hasNext) {
      clNewEm = itNewEm.next
    }
    while (clEmID < clausesEmpty.size) {
      val currentCl = clauses.get(clEmID)
      if (currentCl == clNewEm) {
        if (itNewEm.hasNext) {
          clNewEm = itNewEm.next
        } else {
          clNewEm = -1
        }
        resultEmpty.push(currentCl)
      }
      clEmID += 1
    }
    while (clNewEm != -1) {
      resultEmpty.push(clNewEm)
      if (itNewEm.hasNext) {
        clNewEm = itNewEm.next
      } else {
        clNewEm = -1
      }
    }
    (result, resultEmpty)
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
  private def underestimation(softClauses: Vec[Int], softClausesEmpty: Vec[Int]): Vec[Int] = {
    // TODO
    softClausesEmpty
  }

  /**
   * Checks whether the current lower bound is not preferred to the upper bound
   */
  private def antilex(lis1: Vec[Int], lis2: Vec[Int]): Boolean = {
    if (lis1.isEmpty) {
      return true
    } else if (lis2.isEmpty()) {
      return false
    }
    val itLis1 = lis1.iterator
    val itLis2 = lis2.iterator
    while (itLis1.hasNext && itLis2.hasNext) {
      val id1 = itLis1.next
      val id2 = itLis2.next
      if (id1 < id2) {
        return false
      } else if (id2 < id1) {
        return true
      }
    }
    if (itLis2.hasNext) {
      false
    } else {
      true
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
  var initialVarStack: List[VariableBAB] = List()

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
    hardClausesArySim = new Array(hardClauses.size)
    var i = 0
    for (clause <- hardClauses) {
      hardClausesArySim(i) = newClause(true, i, clause)
      i += 1
    }

    // create working Array for soft clauses
    softClausesArySim = new Array(softClauses.size)
    var upperBound: Vec[Int] = new Vec()
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
        upperBound.push(j)
      }
      j += 1
    }
    upperBound
  }

  private def newVar(variable: PLAtom) = {
    val id = vars.size
    val newVar = new VariableBAB(variable, id)
    varToID += (variable -> id)
    vars.push(newVar)
    initialVarStack = newVar :: initialVarStack
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
    if (clause.size == 0) {

    } else if (clause.size == 1) {
      if (isHard && !assign(workingClause(0))) {
        // hard clauses not satisfiable (should not be possible)
        throw new AssertionError("hard clauses not satisfiable")
      } else {
        // TODO variable has already other state -> add to delta
        watches.get(BABUtil.not(workingClause(0))).push(newClause)
      }
    } else {
      // add watches
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
      myPrintln("assign: " + getVar(lit))
      true
    }
  }

  private def cancelUntil(level: Int) {
    myPrintln("cancelUntil (start):\n" + trail + "\n" + trailLimits)
    if (level < decisionLevel()) {
      myPrintln("from " + (trail.size - 1) + " to " + trailLimits.get(level))
      for (c <- trail.size - 1 to trailLimits.get(level) by -1) {
        val variable = getVar(trail.get(c))
        variable.assign(VarState.UNDEF)
        myPrintln(variable)
        //variable.setReason(null);
        //variable.setPolarity(sign(trail.get(c)));
        //if (varHeap.find(variable) == -1) {
        //          varHeap.insert(variable);
        //      }
      }
      trail.shrink(trail.size() - trailLimits.get(level))
      trailLimits.shrink(trailLimits.size() - level)
      qhead = trail.size
    }
    myPrintln("cancelUntil (end):\n" + trail + "\n" + trailLimits)
    myPrintln(vars)
  }

  /**
   * Similar to pickBranchLit
   */
  private def pickNextVar(varStack: List[VariableBAB]): (Int, List[VariableBAB]) = {
    while (!varStack.isEmpty) {
      val next = varStack.head
      if (next.assignment() == VarState.UNDEF) {
        return (next.getID, varStack.tail)
      }
    }
    return (-1, List())
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

  private def myPrintln(s: Object) = println("\t" + decisionLevel() + "\t" + s.toString)

}