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

import org.warthog.pl.decisionprocedures.satsolver.{ Model, Solver }
import org.warthog.pl.datastructures.cnf.{ PLLiteral, MutablePLClause, ImmutablePLClause }
import org.warthog.generic.formulas.Formula
import org.warthog.pl.formulas.{ PLAtom, PL }
import org.warthog.pl.optimization.maxsat.MaxSATHelper
import org.warthog.pl.generators.pbc.PBCtoSAT
import org.warthog.generic.datastructures.cnf.ClauseLike
import scala.util.control.Breaks.{ break, breakable }

/**
 * Implements the Fast Diag algorithm which was published in
 * 'An Efficient Diagnosis Algorithm for Inconsistent Constraint Sets' (2012)
 *
 * @author Konstantin Grupp
 */
class FastDiag(satSolver: Solver, assumeUNSAT: Boolean = false) extends SATBasedAPreferredMCSSolver(satSolver) {

  override def name = {
    var a = ""
    if (assumeUNSAT) a = "-assumeUNSAT"
    "FastDiag" + a
  }
  
  var softClausesAry = Array[ClauseLike[PL, PLLiteral]]()

  val (tUsat, tUsatAdd, tUsatDel) = (new TimeUsed("sat"), new TimeUsed("sat_add_clauses"), new TimeUsed("sat_del_clauses"))
  timeUsed = List(tUsat, tUsatAdd, tUsatDel)

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]) = {
    softClausesAry = softClauses.toArray
    val softClausesInt = (0 to softClauses.size-1).toList
    if (softClauses.isEmpty || (!assumeUNSAT && sat(softClauses))) {
      List()
    } else {
      solveImplHelper(1, true, softClausesInt, softClausesInt)
    }
  }

  /**
   * Helper function for the FastDiag algorithm (called FD in paper)
   *
   * @param d at start it should be empty
   * @param softClauses
   * @param allClauses at start it should be has all soft clauses
   */
  private def solveImplHelper(recursion: Int, isRedundant: Boolean, softClauses: List[Int], allClauses: List[Int]): List[Int] = {
    Thread.sleep(0) // to handle interrupts
    if (!isRedundant && mySat(allClauses)) {
      List()
    } else if (softClauses.size == 1) {
      softClauses
    } else {
      val k: Int = softClauses.size / 2
      val (softClauses1, softClauses2) = softClauses.splitAt(k)
      val d1 = solveImplHelper(recursion + 1, softClauses2.isEmpty, softClauses1, myDiff(allClauses,softClauses2))
      val d2 = solveImplHelper(recursion + 1, d1.isEmpty, softClauses2, myDiff(allClauses, d1))
      d1 ++ d2
    }
  }
  
  private def myDiff(lis1: List[Int], diffLis: List[Int]):List[Int] = {
    if (diffLis.isEmpty || lis1.isEmpty) {
      return lis1
    }
    var result:List[Int] = List()
    
    val iterator = lis1.iterator
    val iteratorDiff = diffLis.iterator
    var diff = iteratorDiff.next
    breakable {
      while (true) {
        if (!iterator.hasNext) {
          break
        }
        var current = iterator.next
        if (current == diff) {
          // not add 'current' to 'result'
          if (iteratorDiff.hasNext) {
            diff = iteratorDiff.next
          } else {
            break
          }
        } else {
          result = current :: result
        }
      }
    }
    while (iterator.hasNext) {
      result = iterator.next :: result
    }
    result.reverse
  }

  private def mySat(clausesInt: List[Int] = List.empty): Boolean = {
    tUsatAdd.start()
    satSolver.mark()
    var j = 0
    for (cInt <- clausesInt) {
      if (100 < j) {
        Thread.sleep(0) // to handle interrupts
        j = 0
      }
      satSolver.add(softClausesAry(cInt))
      j += 1
    }
    tUsatAdd.end()
    tUsat.start()
    val isSAT = satSolver.sat() == Solver.SAT
    tUsat.end()
    tUsatDel.start()
    satSolver.undo()
    tUsatDel.end()
    isSAT
  }

}