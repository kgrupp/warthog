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
class LinearSearch(satSolver: Solver) extends APreferredMCSMaxSATSolver() {

  private var workingModel: Model = null

  override def name = "LinearSearch"

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
    satSolver.mark() /* Mark to remove all added clauses after solving */
    val result = solveAPreferredMCSImplHelper(softClauses)
    satSolver.undo()
    result
  }

  private def solveAPreferredMCSImplHelper(softClauses: List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    var gamma:Set[ClauseLike[PL, PLLiteral]] = Set()
    var delta:Set[ClauseLike[PL, PLLiteral]] = Set()
    for (clause <- softClauses) {
      if (sat(gamma + clause)) {
        gamma += clause
      } else {
        delta += clause
      }
    }
    delta
  }

  override protected def areHardConstraintsSatisfiable() = {
    satSolver.sat() == Solver.SAT
  }

  private def sat(clauses: Set[ClauseLike[PL, PLLiteral]] = Set.empty): Boolean = {
    satSolver.mark()
    for (c <- clauses)
      satSolver.add(c)
    val isSAT = satSolver.sat() == Solver.SAT
    if (isSAT)
      workingModel = satSolver.getModel().get
    satSolver.undo()
    isSAT
  }
  
}

object LinearSearch {
  
}
