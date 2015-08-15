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
 * Linear Search algorithm for A-preferred MCS.
 */
class LinearSearch(satSolver: Solver) extends SatSolverUsingMCSSolver(satSolver) {

  override def name = "LinearSearch" + super.name

  override protected def solveAPreferredMCSImpl(softClauses: List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    val result = solveAPreferredMCSImplHelper(softClauses)
    result
  }

  private def solveAPreferredMCSImplHelper(softClauses: List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    var delta:Set[ClauseLike[PL, PLLiteral]] = Set()
    for (clause <- softClauses) {
      Thread.sleep(0) // to handle interrupts
      if (mySat(clause)) {
        // add to gamma, treated as hard clause
        satSolver.add(clause)
      } else {
        delta += clause
      }
    }
    delta
  }
  
  private def mySat(clause:ClauseLike[PL, PLLiteral]): Boolean = {
    satSolver.mark()
    satSolver.add(clause)
    val isSAT = satSolver.sat() == Solver.SAT
    satSolver.undo()
    isSAT
  }
  
}