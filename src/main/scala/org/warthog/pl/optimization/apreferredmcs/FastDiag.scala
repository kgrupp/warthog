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

/**
 * Implements the Fast Diag algorithm which was published in
 * 'An Efficient Diagnosis Algorithm for Inconsistent Constraint Sets' (2012)
 *
 * @author Konstantin Grupp
 */
class FastDiag(satSolver: Solver, assumeUNSAT:Boolean = false) extends SATBasedAPreferredMCSSolver(satSolver) {

  override def name = {
    var a = ""
    if (assumeUNSAT) a = "-assumeUNSAT"
    "FastDiag"+a
  }

  val (tUsat, tUsatAdd, tUsatDel) = (new TimeUsed("sat"), new TimeUsed("sat_add_clauses"), new TimeUsed("sat_del_clauses"))
  timeUsed = List(tUsat, tUsatAdd, tUsatDel)

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    val softClausesSet = softClauses.toSet
    if (softClauses.isEmpty || (!assumeUNSAT && sat(softClausesSet))) {
      Set()
    } else {
      // reverse the list of soft clauses because FastDiag works that way
      solveImplHelper(1, Set.empty, softClauses.reverse, softClausesSet)
    }
  }

  /**
   * Helper function for the FastDiag algorithm (called FD in paper)
   *
   * @param d at start it should be empty
   * @param softClauses
   * @param allClauses at start it should be has all soft clauses
   */
  private def solveImplHelper(recursion:Int, d: Set[ClauseLike[PL, PLLiteral]], softClauses: List[ClauseLike[PL, PLLiteral]], allClauses: Set[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    Thread.sleep(0) // to handle interrupts
    if (!d.isEmpty && sat(allClauses)) {
      Set()
    } else if (softClauses.size == 1) {
      softClauses.toSet
    } else {
      val k: Int = softClauses.size / 2
      val (softClauses1, softClauses2) = softClauses.splitAt(k)
      val diff1 = allClauses.diff(softClauses1.toSet)
      val d1 = solveImplHelper(recursion + 1, softClauses1.toSet, softClauses2, diff1)
      val diff2 = allClauses.diff(d1)
      val d2 = solveImplHelper(recursion + 1, d1, softClauses1, diff2)
      val result = d1.union(d2)
      result
    }
  }

  override protected def sat(clauses: Set[ClauseLike[PL, PLLiteral]] = Set.empty): Boolean = {
    tUsatAdd.start()
    satSolver.mark()
    var j = 0
    for (c <- clauses) {
      if (100 < j) {
        Thread.sleep(0) // to handle interrupts
        j = 0
      }
      satSolver.add(c)
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