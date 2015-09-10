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
import org.warthog.pl.decisionprocedures.satsolver.Solver
import org.warthog.pl.datastructures.cnf.ImmutablePLClause
import org.warthog.pl.formulas.PL
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.optimization.maxsat.partialweighted.PartialWeightedMaxSATSolver

/**
 * @author Konstantin Grupp
 */
class WeightedMCSGuidedSearch(solver: PartialWeightedMaxSATSolver) extends APreferredMCSSolver {

  override def name = "WeightedMCSGuidedSearch"
  
  def solverName = solver.name

  override def reset() {
    super.reset()
    solver.reset()
    hardClauses = Nil
    marks = Nil
  }

  protected var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil
  private var marks: List[Int] = Nil

  override def addHardConstraint(clause: ClauseLike[PL, PLLiteral]) {
    solver.addHardConstraint(clause)
    hardClauses = (clause :: hardClauses)
  }

  override def markHardConstraints() {
    marks = hardClauses.length :: marks
  }

  override def undoHardConstraints() {
    marks match {
      case h :: t => {
        marks = t
        solver.reset
        hardClauses = hardClauses.drop(hardClauses.length - h)
        hardClauses.foreach(solver.addHardConstraint)
      }
      case _ => // No mark, then ignore undo
    }
  }

  override protected def areHardConstraintsSatisfiable() = solver.solveMinUNSAT(List(), List()).isDefined

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]) = {
    
    // TODO needed resulting clauses and not only minimal cost 
    
    List()
  }
  
  
}