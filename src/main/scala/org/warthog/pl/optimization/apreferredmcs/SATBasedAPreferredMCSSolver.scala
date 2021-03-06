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
import org.warthog.pl.formulas.PL
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.optimization.apreferredmcs.impl.TimeUsed

/**
 * A helper class for algorithms which use a SAT Solver
 * 
 * @author Konstantin Grupp
 */
abstract class SATBasedAPreferredMCSSolver(satSolver: Solver) extends APreferredMCSSolver {

  def satSolverName = satSolver.name

  protected val (tUsat, tUsatAdd, tUsatDel) = (new TimeUsed("sat"), new TimeUsed("sat_add_clauses"), new TimeUsed("sat_del_clauses"))
  timeUsed = List(tUsat, tUsatAdd, tUsatDel)

  override def reset() {
    super.reset()
    satSolver.reset()
    hardClauses = Nil
    marks = Nil
  }

  protected var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil
  private var marks: List[Int] = Nil

  override def addHardConstraint(clause: ClauseLike[PL, PLLiteral]) {
    satSolver.add(clause)
    hardClauses = (clause :: hardClauses)
  }

  override def markHardConstraints() {
    marks = hardClauses.length :: marks
  }

  override def undoHardConstraints() {
    marks match {
      case h :: t => {
        marks = t
        satSolver.reset
        hardClauses = hardClauses.drop(hardClauses.length - h)
        hardClauses.foreach(satSolver.add)
      }
      case _ => // No mark, then ignore undo
    }
  }

  override protected def areHardConstraintsSatisfiable() = sat()

  /**
   * Makes a mark, adds the given clauses to the sat solver and calculates if the formula is satisfiable
   *
   * Note: Makes a mark but does not call the undo() operation
   *
   * @param clauses the clauses which will be added
   */
  protected def sat(clauses: Traversable[ClauseLike[PL, PLLiteral]] = Set.empty): Boolean = {
    if (!clauses.isEmpty) {
      tUsatAdd.start
      satSolver.mark
      var j = 0
      for (c <- clauses) {
        if (100 < j) {
          Thread.sleep(0) // to handle interrupts
          j = 0
        }
        satSolver.add(c)
        j += 1
      }
      tUsatAdd.end
    }
    tUsat.start
    val isSAT = satSolver.sat() == Solver.SAT
    tUsat.end
    if (!clauses.isEmpty) {
      tUsatDel.start
      satSolver.undo
      tUsatDel.end
    }
    isSAT
  }

  /**
   * Makes a mark, adds the given clause to the sat solver and calculates if the formula is satisfiable
   *
   * Note: Makes a mark but does not call the undo() operation
   *
   * @param clause the clause which will be added
   */
  protected def sat(clause: ClauseLike[PL, PLLiteral]): Boolean = {
    tUsatAdd.start
    satSolver.mark
    satSolver.add(clause)
    tUsatAdd.end
    tUsat.start
    val isSAT = satSolver.sat() == Solver.SAT
    tUsat.end
    isSAT
  }

}