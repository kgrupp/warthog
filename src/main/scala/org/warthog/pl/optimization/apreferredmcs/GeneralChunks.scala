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
import org.warthog.pl.optimization.apreferredmcs.impl.PartitionMaker
import scala.util.control.Breaks.{ break, breakable }
import org.warthog.pl.optimization.apreferredmcs.impl.ModelExploiting

/**
 * Implements an optimized version of the general chunks approach which was published in
 * 'Suggestions for Improvements of Preferred Minimal Correction Subset Computiation' (2015)
 *
 * @author Konstantin Grupp
 */
class GeneralChunks(satSolver: Solver, partitionMaker: PartitionMaker, useModelExploiting: Boolean = false, useBackbone: Boolean = false, assumeUNSAT: Boolean = false) extends SATBasedAPreferredMCSSolver(satSolver) {

  def this(satSolver: Solver) = this(satSolver, PartitionStrategy.constant(10))

  override def name = {
    var m = ""
    if (useModelExploiting) m = "-modelExploiting"
    var b = ""
    if (useBackbone) b = "-backbone"
    var a = ""
    if (assumeUNSAT) a = "-assumeUNSAT"
    "GeneralChunks-" + partitionMaker.name + m + b + a
  }

  var delta: List[Int] = List()
  var softClausesAry: Array[ClauseLike[PL, PLLiteral]] = Array.empty
  val modelExploiting = new ModelExploiting(satSolver)

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]) = {
    softClausesAry = new Array(softClauses.size)
    var i = 0
    softClauses.foreach(y => {
      softClausesAry(i) = y
      i += 1
    })
    chunksHelper(1, assumeUNSAT, 0, softClauses.size - 1)
    delta.reverse
  }

  /**
   * Helper function for the chunks algorithm
   *
   * @param d at start it should be empty
   * @param softClauses
   * @param allClauses at start it should be has all soft clauses
   */
  private def chunksHelper(recursion: Int, isRedundant: Boolean, start: Int, end: Int): (Boolean, Int) = {
    //println("chunksHelper "+start+" to "+end)
    Thread.sleep(0) // to handle interrupts
    val isSatisfied = !isRedundant && mySat(start, end)
    if (!isSatisfied) {
      tUsatDel.start()
      satSolver.undo()
      tUsatDel.end()
    }

    if (isSatisfied) {
      
      var numberOfAdditionalClausesSatisfied = 0

      if (useModelExploiting) {
        // restricted model exploiting start
        breakable {
          for (j <- end + 1 to softClausesAry.size - 1) {
            Thread.sleep(0) // to handle interrupts
            val checkClause = softClausesAry(j)
            if (modelExploiting.isSat(checkClause)) {
              satSolver.addHard(checkClause)
              numberOfAdditionalClausesSatisfied += 1
            } else {
              break
            }
          }
        }
        // restricted model exploiting end
      }

      tUsatDel.start
      satSolver.forgetLastMark()
      tUsatDel.end

      (true, numberOfAdditionalClausesSatisfied)
    } else if (end == start) {
      delta = start :: delta
      if (useBackbone) {
        for (lit <- softClausesAry(start).literals) {
          satSolver.addHard(new ImmutablePLClause(lit.negate))
        }
      }
      (false, 0)
    } else {
      val tempPartitionMaker = partitionMaker.createNewInstance()
      tempPartitionMaker.initialize(start, end, recursion)
      var areSubCallsSAT = true
      var skip = 0
      while (tempPartitionMaker.hasNext(skip)) {
        Thread.sleep(0) // to handle interrupts
        val (recStart, recEnd) = tempPartitionMaker.nextPartition(skip)
        val result = chunksHelper(recursion + 1, areSubCallsSAT && !tempPartitionMaker.hasNext(), recStart, recEnd)
        areSubCallsSAT &&= result._1
        skip = result._2
      }
      (areSubCallsSAT, tempPartitionMaker.recursiveSkip(skip))
    }
  }

  private def mySat(start: Int, end: Int): Boolean = {
    tUsatAdd.start()
    satSolver.mark()
    var j = 0
    for (i <- start to end) {
      if (100 < j) {
        Thread.sleep(0) // to handle interrupts
        j = 0
      }
      satSolver.add(softClausesAry(i))
      j += 1
    }
    tUsatAdd.end()
    tUsat.start()
    val isSAT = satSolver.sat() == Solver.SAT
    tUsat.end()
    isSAT
  }

}