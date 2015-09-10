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
import org.warthog.generic.formulas.Formula
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.decisionprocedures.satsolver.Model
import org.warthog.pl.formulas.PL
import org.warthog.pl.transformations.CNFUtil
import org.warthog.pl.optimization.apreferredmcs.impl.TimeUsed

/**
 * Common interface for APreferred MCS MaxSAT solvers.
 *
 * @author Konstantin Grupp
 */
abstract class APreferredMCSSolver() {

  protected var result: Option[List[Int]] = None

  def name: String

  /**
   * For benchmark only
   */
  var timeUsed: List[TimeUsed] = List()

  def reset() {
    result = None
  }

  def addHardConstraint(fm: Formula[PL]) {
    addHardConstraint(CNFUtil.toImmutableCNF(fm))
  }

  def addHardConstraint(clauses: Traversable[ClauseLike[PL, PLLiteral]]) {
    clauses.foreach(addHardConstraint)
  }

  def addHardConstraint(clause: ClauseLike[PL, PLLiteral])

  def markHardConstraints()

  def undoHardConstraints()

  /**
   * Calculates the a-preferred MCS for this instance with the given soft clauses.
   *
   * @param keepState if true it ensures the state of this instance after calling solve. It uses markHardConstraints/undoHardConstraints
   */
  def solve(softClauses: List[ClauseLike[PL, PLLiteral]], keepState: Boolean = false): Option[List[Int]] = {
    if (keepState) {
      markHardConstraints()
    }
    if (!areHardConstraintsSatisfiable())
      result = None
    else
      result = Some(solveImpl(softClauses))
    if (keepState) {
      undoHardConstraints()
    }
    result
  }

  /**
   * Actual solving method.
   *
   * Assumption: Previously added hard constraints are satisfiable.
   *
   * First Clause in List is the most important one.
   *
   * @param softClauses in the L-Preferred order
   * @return
   */
  protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]): List[Int]

  protected def areHardConstraintsSatisfiable(): Boolean
}