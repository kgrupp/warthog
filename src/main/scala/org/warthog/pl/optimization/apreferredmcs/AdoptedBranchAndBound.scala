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

  /**
   * Modify needed to avoid undo() call because the model is needed
   */
  override protected def sat(clauses: Traversable[ClauseLike[PL, PLLiteral]] = Set.empty): Boolean = {
    tUsat.start
    val isSAT = satSolver.sat() == Solver.SAT
    tUsat.end
    isSAT
  }

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]) = {
    // works because of modified sat call which does calls no mark/undo
    val partialAssignment = satSolver.getModel().get.toMap

    val (upperBound, emptySoftClauses) = prepare(softClauses, partialAssignment)

    val hardClausesInt = new Vec[Int](hardClauses.size)
    for (i <- 0 to hardClauses.size - 1) {
      hardClausesInt.push(i)
    }
    val softClausesInt = new Vec[Int](softClauses.size)
    if (emptySoftClauses.isEmpty()) {
      for (i <- 0 to softClauses.size - 1) {
        softClausesInt.push(i)
      }
    } else { // already empty clauses detected (can only be clauses without variables)
      val itEmCl = emptySoftClauses.iterator()
      var clEm = itEmCl.next()
      for (i <- 0 to softClauses.size - 1) {
        if (clEm == i) {
          if (itEmCl.hasNext()) {
            clEm = itEmCl.next()
          }
        } else {
          softClausesInt.push(i)
        }
      }
    }

    val resultVec = adoptedBranchAndBound(hardClausesInt, emptyVecInt, softClausesInt, emptySoftClauses, upperBound, initialVarStack)
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
    Thread.sleep(0) // to handle interrupts
    //myPrintln("adoptedBranchAndBound:\n\t\t" + /*hardClauses + "\n\t\t" + hardClausesEmpty + "\n\t\t" + */softClauses + "\n\t\t" + softClausesEmpty/* + "\n\t\t" + upperBound + "\n\t\t" + varStack*/)
    val (hardClausesSimp, hardClausesSimpEmpty, softClausesSimp, softClausesSimpEmpty) = simplify(hardClauses, hardClausesEmpty, softClauses, softClausesEmpty)

    if (!hardClausesSimpEmpty.isEmpty) {
      return emptyVecInt
    }
    if (softClausesSimp.isEmpty) { // all soft clauses satisfied or empty
      return softClausesSimpEmpty
    }
    val lowerBound = underestimation(softClausesSimp, softClausesSimpEmpty)

    if (antilex(upperBound, lowerBound)) {
      return upperBound
    }
    val (x, newVarStack) = pickNextVar(varStack)
    //myPrintln("newAssumptionVar: " + x + " on decisionLevel " + decisionLevel)
    //myPrintln(varStack.toString)
    if (x == -1) {
      // all soft clauses are satisfied but not all were detected by simplify 
      return softClausesSimpEmpty
    }
    val currentLevel = decisionLevel
    if (!assume(BABUtil.mkLit(x, false))) {
      return throw new AssertionError("already assigned other way")
    }
    val resultPos = adoptedBranchAndBound(hardClausesSimp, hardClausesSimpEmpty, softClausesSimp, softClausesSimpEmpty, upperBound, newVarStack)
    cancelUntil(currentLevel)
    if (!assume(BABUtil.mkLit(x, true))) {
      return throw new AssertionError("already assigned other way")
    }
    val resultNeg = adoptedBranchAndBound(hardClausesSimp, hardClausesSimpEmpty, softClausesSimp, softClausesSimpEmpty, upperBound, newVarStack)
    //myPrintln("bounds:\n\t\t" + resultPos + "\n\t\t" + resultNeg + "\n\t\t" + upperBound, true)
    if (antilex(resultPos, resultNeg)) {
      if (antilex(resultPos, upperBound)) {
        return resultPos
      } else {
        return upperBound
      }
    } else if (antilex(resultNeg, upperBound)) {
      return resultNeg
    } else {
      return upperBound
    }
  }

  private def remainingAre(clauses: Vec[Int]) = {

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
      //myPrintln("simplify: " + qhead + " < " + trail.size + " propLit: " + propLit)
      qhead += 1
      val watchers: IVec[ClauseBAB] = watches.get(propLit)
      var i = 0;
      var j = 0;
      while (i != watchers.size()) {
        Thread.sleep(0) // to handle interrupts
        //myPrintln("simplify: watchers " + i + " < " + watchers.size + " clause: " + watchers.get(i))
        if (watchers.get(i).isLit()) {
          val unitClause = watchers.get(i)
          if (unitClause.isHard()) {
            if (!assign(unitClause.lit())) {
              // clause empty
              //myPrintln("found hard empty clause: " + unitClause)
              emptyNewHard = unitClause.getID :: emptyNewHard
              // TODO break because hard clauses are not satisfied
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
              //myPrintln("found hard sat clause: " + unitClause)
              satNewHard = unitClause.getID :: satNewHard
              watchers.set(j, watchers.get(i))
              j += 1
              i += 1
            }
          } else { // is softclause
            // TODO
            if (value(unitClause.lit()) == VarState.TRUE) {
              //myPrintln("found soft sat clause: " + unitClause)
              satNewSoft = unitClause.getID :: satNewSoft
              watchers.set(j, watchers.get(i))
              j += 1
              i += 1
            } else if (value(unitClause.lit()) == VarState.FALSE) {
              //myPrintln("found soft empty clause: " + unitClause)
              emptyNewSoft = unitClause.getID :: emptyNewSoft
              i += 1
              j += 1
            }
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
              //myPrintln("found hard sat clause: " + c)
              satNewHard = c.getID :: satNewHard
            } else {
              //myPrintln("found soft sat clause: " + c)
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
              if (c.isHard()) {
                if (!assign(first)) {
                  // empty clause
                  //myPrintln("found hard empty clause: " + c)
                  emptyNewHard = c.getID :: emptyNewHard
                  // TODO break because hard clauses are not satisfied
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
              } else { // is soft clause
                if (value(first) == VarState.FALSE) {
                  //myPrintln("found soft empty clause: " + c)
                  emptyNewSoft = c.getID :: emptyNewSoft
                }
              }
            } // found new watch -> not empty but still false
          }
        }
      }
      watchers.shrink(i - j)
    }
    // combine old result with newer information
    //myPrintln("simplify (changed clauses):\n\t\t" + satNewHard + "\n\t\t" + emptyNewHard + "\n\t\t" + satNewSoft + "\n\t\t" + emptyNewSoft)
    val (resultHard, resultHardEmpty) = combineVecs(true, hardClauses, hardClausesEmpty, satNewHard, emptyNewHard)
    val (resultSoft, resultSoftEmpty) = combineVecs(false, softClauses, softClausesEmpty, satNewSoft, emptyNewSoft)
    /*myPrintln("simplify (result):\n\t\t" + resultHard + "\n\t\t" + resultHardEmpty + "\n\t\t" + resultSoft + "\n\t\t" + resultSoftEmpty)
    myPrintln("current states: " + vars)
    for (i <- 0 to resultSoft.size - 1) {
      myPrintln("softClause not satisfied: " + softClausesArySim(resultSoft.get(i)))
    }*/
    Thread.sleep(0) // to handle interrupts
    (resultHard, resultHardEmpty, resultSoft, resultSoftEmpty)
  }

  private def combineVecs(isHard: Boolean, clauses: Vec[Int], clausesEmpty: Vec[Int], satNew: List[Int], emptyNew: List[Int]): (Vec[Int], Vec[Int]) = {
    //myPrintln("combineVecs: \n\t\t" + clauses + "\n\t\t" + clausesEmpty + "\n\t\t" + satNew + "\n\t\t" + emptyNew)
    // sort satNew and emptyNew because they may be not in order to do a combination in linear time
    var clID = 0
    val satNewSorted = satNew.sortWith(_ < _).distinct // TODO efficient duplicate elimination
    var itNewSat = satNewSorted.iterator
    var clNewSat = Integer.MAX_VALUE
    if (itNewSat.hasNext) {
      clNewSat = itNewSat.next
    }
    val emptyNewSorted = emptyNew.sortWith(_ < _).distinct // TODO efficient duplicate elimination
    var itNewEm = emptyNewSorted.iterator
    var clNewEm = Integer.MAX_VALUE
    if (itNewEm.hasNext) {
      clNewEm = itNewEm.next
    }

    // calc result for clauses which are false
    var resultSize = clauses.size - satNewSorted.size - emptyNewSorted.size
    if (resultSize < 5) resultSize = 5
    val result = new Vec[Int](resultSize)
    while (clID < clauses.size) {
      val currentCl = clauses.get(clID)
      if (clNewSat <= currentCl) {
        // we need here <= because an element could be added to new sat which is already deleted from softClauses
        if (itNewSat.hasNext) {
          clNewSat = itNewSat.next
        } else {
          clNewSat = Integer.MAX_VALUE
        }
        if (clNewSat == currentCl) {
          clID += 1
        }
      } else if (clNewEm == currentCl) {
        if (itNewEm.hasNext) {
          clNewEm = itNewEm.next
        } else {
          clNewEm = Integer.MAX_VALUE
        }
        clID += 1
      } else {
        var currentClause: ClauseBAB = null
        if (isHard) {
          currentClause = hardClausesArySim(currentCl)
        } else {
          currentClause = softClausesArySim(currentCl)
        }
        if (value(currentClause.get(0)) == VarState.TRUE) {
          //myPrintln("found sat clause to delete: " + currentClause)
          // clause is satisfied
        } else {
          result.push(currentCl)
        }
        clID += 1
      }
    }

    // calc result for empty Clauses
    val resultEmpty = new Vec[Int](clausesEmpty.size + emptyNewSorted.size)
    var clEmID = 0
    itNewEm = emptyNewSorted.iterator
    clNewEm = Integer.MAX_VALUE
    if (itNewEm.hasNext) {
      clNewEm = itNewEm.next
    }
    while (clEmID < clausesEmpty.size) {
      val currentCl = clausesEmpty.get(clEmID)
      if (clNewEm < currentCl) {
        resultEmpty.push(clNewEm)
        if (itNewEm.hasNext) {
          clNewEm = itNewEm.next
        } else {
          clNewEm = Integer.MAX_VALUE
        }
      } else {
        resultEmpty.push(currentCl)
        clEmID += 1
      }
    }
    while (clNewEm != Integer.MAX_VALUE) {
      resultEmpty.push(clNewEm)
      if (itNewEm.hasNext) {
        clNewEm = itNewEm.next
      } else {
        clNewEm = Integer.MAX_VALUE
      }
    }
    //myPrintln("combineVecs (result): \n\t\t" + result + "\n\t\t" + resultEmpty)
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
    softClausesEmpty // in best case it could be this
  }

  /**
   * Checks whether the current lower bound is not preferred to the upper bound
   */
  private def antilex(lis1: Vec[Int], lis2: Vec[Int]): Boolean = {
    //myPrintln("antilex: " + lis1 + " < " + lis2)
    if (lis1.isEmpty) {
      return true
    } else if (lis2.isEmpty) {
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
    var tempMap = assignment
    
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
    var emptyClauses: Vec[Int] = new Vec()
    var j = 0
    for (clause <- softClauses) {
      var isSat = false
      var undefLit: PLLiteral = null
      softClausesArySim(j) = newClause(false, j, clause, (lit: PLLiteral) => {
        if (!isSat) {
          val phaseOpt = tempMap.get(lit.variable)
          if (!phaseOpt.isEmpty) {
            if (phaseOpt.get == lit.phase) {
              isSat = true
            }
          } else {
            undefLit = lit
          }
        }
      })
      if (!isSat && undefLit != null) {
        tempMap += (undefLit.variable -> undefLit.phase)
        isSat
      }
      if (!isSat || clause.size == 0) {
        upperBound.push(j)
      }
      if (clause.size == 0) {
        emptyClauses.push(j)
      }
      j += 1
    }
    (upperBound, emptyClauses)
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
      if (isHard) {
        throw new AssertionError("hard clauses not satisfiable")
      }
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
      //myPrintln("assign: " + getVar(lit))
      true
    }
  }

  private def cancelUntil(level: Int) {
    //myPrintln("cancelUntil (start):\n" + trail + "\n" + trailLimits)
    if (level < decisionLevel()) {
      //myPrintln("from " + (trail.size - 1) + " to " + trailLimits.get(level))
      for (c <- trail.size - 1 to trailLimits.get(level) by -1) {
        val variable = getVar(trail.get(c))
        variable.assign(VarState.UNDEF)
        //myPrintln(variable)
      }
      trail.shrink(trail.size() - trailLimits.get(level))
      trailLimits.shrink(trailLimits.size() - level)
      qhead = trail.size
    }
    //myPrintln("cancelUntil (end):\n" + trail + "\n" + trailLimits)
    //myPrintln(vars)
  }

  /**
   * Similar to pickBranchLit
   */
  private def pickNextVar(varStack: List[VariableBAB]): (Int, List[VariableBAB]) = {
    var temp = varStack
    while (!temp.isEmpty) {
      val next = temp.head
      if (next.assignment() == VarState.UNDEF) {
        return (next.getID, temp.tail)
      }
      temp = temp.tail
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
    if (BABUtil.sign(lit)) { // if literal negated
      variable.assignment.negate
    } else {
      variable.assignment
    }
  }

  //private def myPrintln(s: Object, activate: Boolean = false) = println("\t" + decisionLevel() + "\t" + s.toString)

}