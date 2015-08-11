package org.warthog.pl.optimization.maxsat.apreferredmcs

import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.decisionprocedures.satsolver.Solver
import org.warthog.pl.formulas.PL
import org.warthog.pl.datastructures.cnf.PLLiteral

/**
 * @author Konstantin
 */
abstract class SatSolverUsingMCSSolver(satSolver: Solver) extends APreferredMCSMaxSATSolver {
  
  override def name = "LinearSearchModelExploiting ("+ satSolver.name + ")"

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

  override def undoHardConstraints() {
    satSolver.undo()
  }
  
  override protected def areHardConstraintsSatisfiable() = sat()

  protected def sat(clauses: Set[ClauseLike[PL, PLLiteral]] = Set.empty): Boolean = {
    satSolver.mark()
    for (c <- clauses)
      satSolver.add(c)
    val isSAT = satSolver.sat() == Solver.SAT
    satSolver.undo()
    isSAT
  }
  
}