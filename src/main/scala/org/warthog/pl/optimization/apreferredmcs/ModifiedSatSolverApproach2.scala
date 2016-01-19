package org.warthog.pl.optimization.apreferredmcs

import scala.collection.mutable.{ Map => MutableMap }
import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.decisionprocedures.satsolver.Solver
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.collections.nativeType.IntVec
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.prover.datastructures.LBool
import org.warthog.pl.formulas.PL
import org.warthog.pl.formulas.PLAtom
import org.warthog.pl.optimization.apreferredmcs.impl.ModifiedMSJCoreProver
import org.warthog.pl.optimization.apreferredmcs.impl.PartitionMaker

/**
 * Implements an optimized version of the Normalization and Reduction approach which was published in
 * 'Suggestions for Improvements of Preferred Minimal Correction Subset Computiation' (2015)
 *
 * Uses the ModifiedMSJCoreProver for the calculation.
 *
 * @author Konstantin Grupp
 */
class ModifiedSatSolverApproach2(partitionMaker: PartitionMaker) extends APreferredMCSSolver {

  private var modifiedSatSolver = new ModifiedMSJCoreProver
  private val varToID = MutableMap[PLAtom, Int]()
  private val idToVar = MutableMap[Int, PLAtom]()
  private var hardClauses: List[ClauseLike[PL, PLLiteral]] = Nil
  private var marks: List[Int] = Nil
  private var lastState = Solver.UNKNOWN

  override def name = "ModifiedSatSolverApproach2-" + partitionMaker.name

  override def reset() {
    super.reset()
    modifiedSatSolver = new ModifiedMSJCoreProver
    varToID.clear
    idToVar.clear
    hardClauses = Nil
    marks = Nil
    lastState = Solver.UNKNOWN
  }

  override def addHardConstraint(clause: ClauseLike[PL, PLLiteral]) {
    internalAddHard(clause)
    hardClauses = (clause :: hardClauses)
    if (lastState != Solver.UNSAT)
      lastState = Solver.UNKNOWN
  }

  private def internalAddHard(clause: ClauseLike[PL, PLLiteral]) {
    val clauseAsIntVec = new IntVec(clause.literals.map(literal => {
      val (v, phase) = (literal.variable, literal.phase)
      val id = varToID.getOrElseUpdate(v, {
        modifiedSatSolver.newVar(false)
        val nextID = varToID.size
        idToVar += (nextID -> v)
        nextID
      })
      ModifiedMSJCoreProver.mkLit(id, !phase)
    }).toArray)

    modifiedSatSolver.newClause(clauseAsIntVec, false)
  }

  override def markHardConstraints() {
    marks = hardClauses.length :: marks
  }

  override def undoHardConstraints() {
    marks match {
      case h :: t => {
        marks = t
        modifiedSatSolver = new ModifiedMSJCoreProver()
        hardClauses = hardClauses.drop(hardClauses.length - h)
        hardClauses.foreach(internalAddHard)
      }
      case _ => // No mark, then ignore undo
    }
  }

  override protected def areHardConstraintsSatisfiable() = modifiedSatSolver.solve()

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]) = {
    val assumptionVars = new IntVec(softClauses.size)

    var softClausesAry: Array[ClauseLike[PL, PLLiteral]] = new Array(softClauses.size)
    var j = 0
    softClauses.foreach(y => {
      softClausesAry(j) = y
      j += 1
    })

    var delta: List[Int] = Nil
    partitionMaker.initialize(0, softClauses.size - 1, 1)
    while (partitionMaker.hasNext(0)) {
      Thread.sleep(0) // to handle interrupts
      val (recStart, recEnd) = partitionMaker.nextPartition(0)

      // Normalization
      for (i <- recStart to recEnd) {
        Thread.sleep(0) // to handle interrupts
        val variable = modifiedSatSolver.newVar(true)
        assumptionVars.push(variable)

        // add clause with assumptionVar negate and assumptionVar as unit clause
        internalAddSoft(softClausesAry(i.toInt), variable)
      }

      // modified sat solving
      val result = modifiedSatSolver.solve()
      if (!result) {
        throw new AssertionError("sat was false -> solve does not work")
      }

      // Analyzing result
      for (i <- recStart to recEnd) {
        val assumptionVar = assumptionVars.get(i.toInt)
        modifiedSatSolver.getVarState(assumptionVar) match {
          case LBool.TRUE  => addUnitClause(assumptionVar, true)
          case LBool.FALSE => {
            delta = i.toInt :: delta
            addUnitClause(assumptionVar, false)
          }
          case LBool.UNDEF => throw new AssertionError("assumptionVars should always be defined")
        }
      }

    }
    delta.reverse
  }
  
  private def addUnitClause(variable: Int, phase: Boolean) {
    val unitClause = new IntVec(1)
    unitClause.push(getMSJLit(variable, phase))
    modifiedSatSolver.newClause(unitClause, false)
  }

  private def getMSJLit(variable: Int, phase: Boolean) = ModifiedMSJCoreProver.mkLit(variable, !phase)

  private def internalAddSoft(clause: ClauseLike[PL, PLLiteral], assumptionVar: Int) {
    // add clause with additional assumption var
    val resClause = new IntVec()
    val clauseWithIDs = getIDsWithPhase(clause)
    clauseWithIDs.foreach(resClause.push)
    resClause.push(getMSJLit(assumptionVar, false))
    modifiedSatSolver.newClause(resClause, false)
  }

  /**
   * converts ClauseLike[PL, PLLiteral] to Set[Int]
   * and adds variables to miniSatJavaInstance, varToID, idToVar
   */
  private def getIDsWithPhase(clause: ClauseLike[PL, PLLiteral]): List[Int] = {
    clause.literals.map(literal => {
      val (v, phaseFactor) = (literal.variable, literal.phase)
      getMSJLit(varToID.getOrElseUpdate(v, {
        val nextID = modifiedSatSolver.newVar(false)
        idToVar += (nextID -> v)
        nextID
      }), phaseFactor)
    })
  }

}