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

package org.warthog.pl.optimization.maxsat.apreferredmcs

import org.warthog.pl.decisionprocedures.satsolver.{Model, Solver}
import org.warthog.pl.datastructures.cnf.{PLLiteral, MutablePLClause, ImmutablePLClause}
import org.warthog.generic.formulas.Formula
import org.warthog.pl.formulas.{PLAtom, PL}
import org.warthog.pl.optimization.maxsat.MaxSATHelper
import org.warthog.pl.generators.pbc.PBCtoSAT
import org.warthog.generic.datastructures.cnf.ClauseLike


/**
 * Implements the Fast Diag algorithm which was published in 
 * 'An Efficient Diagnosis Algorithm for Inconsistent Constraint Sets' (2012)
 * 
 */
class FastDiag(satSolver: Solver) extends APreferredMCSMaxSATSolver {

  override def name = "FastDiag ("+ satSolver.name + ")"
  
  val (tUsolveAPreferredMCSImpl, tUsolveAPreferredMCSImplHelper, tUunion, tUdiff, tUsat, tUsatAdd, tUsatDel) = (new TimeUsed("solveAPreferredMCSImpl"), new TimeUsed("tUsolveApreferredMCSImplHelper"), new TimeUsed("union"), new TimeUsed("diff"), new TimeUsed("sat"), new TimeUsed("sat_add_clauses"), new TimeUsed("sat_del_clauses")) 
  timeUsed = List(tUsolveAPreferredMCSImpl, tUsolveAPreferredMCSImplHelper, tUunion, tUdiff, tUsat, tUsatAdd, tUsatDel)

  override def reset() {
    super.reset()
    satSolver.reset()
  }

  override def addHardConstraint(clause: ClauseLike[PL, PLLiteral]) {
    satSolver.add(clause)
  }

  override def markHardConstraints() {
    satSolver.mark()
  }

  def undoHardConstraints() {
    satSolver.undo()
  }

  override protected def solveAPreferredMCSImpl(softClauses: List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    tUsolveAPreferredMCSImpl.start()
    if (softClauses.isEmpty || !areHardConstraintsSatisfiable || sat(softClauses)) {
      tUsolveAPreferredMCSImpl.end()
      Set()
    } else {
      // reverse the list of soft clauses because FastDiag works that way
      val gamma = solveAPreferredMCSImplHelper(Set.empty, softClauses.reverse, softClauses.toSet)
      tUsolveAPreferredMCSImpl.end()
      gamma
    }
  }

  /**
   * Helper function for the FastDiag algorithm (called FD in paper)
   * 
   * @param d at start it should be empty
   * @param softClauses
   * @param allClauses at start it should be has all soft clauses
   */
  private def solveAPreferredMCSImplHelper(d:Set[ClauseLike[PL, PLLiteral]], softClauses: List[ClauseLike[PL, PLLiteral]], allClauses:Set[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    tUsolveAPreferredMCSImplHelper.start()
    Thread.sleep(1) // to handle interrupts
    if (!d.isEmpty && sat(allClauses)) {
      tUsolveAPreferredMCSImplHelper.end()
      Set()
    } else if (softClauses.size == 1) {
      tUsolveAPreferredMCSImplHelper.end()
      softClauses.toSet
    } else {
      val k:Int = softClauses.size/2
      val (softClauses1, softClauses2) = softClauses.splitAt(k)
      tUdiff.start()
      val diff1 = allClauses.diff(softClauses1.toSet)
      tUdiff.end()
      val d1 = solveAPreferredMCSImplHelper(softClauses1.toSet, softClauses2, diff1)
      tUdiff.start()
      val diff2 = allClauses.diff(d1)
      tUdiff.end()
      val d2 = solveAPreferredMCSImplHelper(d1, softClauses1, diff2)
      tUunion.start()
      val result = d1.union(d2)
      tUunion.end()
      tUsolveAPreferredMCSImplHelper.end()
      result
    }
  }

  override protected def areHardConstraintsSatisfiable() = sat()

  private def sat(clauses: Traversable[ClauseLike[PL, PLLiteral]] = Set.empty): Boolean = {
    tUsatAdd.start()
    satSolver.mark()
    for (c <- clauses)
      satSolver.add(c)
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