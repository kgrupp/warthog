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

package org.warthog.pl.optimization.maxsat.apreferredmcs

import org.warthog.pl.decisionprocedures.satsolver.{Model, Solver}
import org.warthog.pl.datastructures.cnf.{PLLiteral, MutablePLClause, ImmutablePLClause}
import org.warthog.generic.formulas.Formula
import org.warthog.pl.formulas.{PLAtom, PL}
import org.warthog.pl.optimization.maxsat.MaxSATHelper
import org.warthog.pl.generators.pbc.PBCtoSAT
import org.warthog.generic.datastructures.cnf.ClauseLike


/**
 * Implements the general chunks approach (4.1 from paper) 
 * 
 */
class GeneralChunks(satSolver: Solver, k:Int) extends SatSolverUsingMCSSolver(satSolver) {

  def this(satSolver:Solver) = this(satSolver, 10)
  
  override def name = "GeneralChunks" + super.name
  
  val (tUsat, tUsatAdd, tUsatDel) = (new TimeUsed("sat"), new TimeUsed("sat_add_clauses"), new TimeUsed("sat_del_clauses")) 
  timeUsed = List(tUsat, tUsatAdd, tUsatDel)
  
  var delta:Set[ClauseLike[PL, PLLiteral]] = Set.empty
  var softClausesAry:Array[ClauseLike[PL, PLLiteral]] = Array.empty

  override protected def solveAPreferredMCSImpl(softClauses: List[ClauseLike[PL, PLLiteral]]): Set[ClauseLike[PL, PLLiteral]] = {
    if (sat()) {
      softClausesAry = new Array(softClauses.size)
      var i = 0
      softClauses.foreach(y => {
        softClausesAry(i) = y
        i += 1
      })
      chunksHelper(false, 0, softClauses.size-1)
      delta
    } else {
      Set()
    }
  }

  /**
   * Helper function for the chunks algorithm
   * 
   * @param d at start it should be empty
   * @param softClauses
   * @param allClauses at start it should be has all soft clauses
   */
  private def chunksHelper(isRedundant:Boolean, start:Int, end:Int):Boolean = {
    //println("chunksHelper "+start+" to "+end)
    Thread.sleep(0) // to handle interrupts
    if (!isRedundant && mySat(start, end)) {
      for (i <- start to end) {
        satSolver.add(softClausesAry(i))
      } 
      true
    } else if (end == start) {
      delta += softClausesAry(start)
      false
    } else {
      val chunks = calcPartition(start,end)
      var areSubCallsSAT = true
      for (j <- 0 to chunks.size-1) {
        Thread.sleep(0) // to handle interrupts
        val isConsistent = chunksHelper(areSubCallsSAT && j == (k-1), chunks(j)._1, chunks(j)._2)
        areSubCallsSAT &&= isConsistent
      }
      areSubCallsSAT
    }
  }
  
  private def calcPartition(start:Int, end:Int):Array[(Int, Int)] = {
    val difference = end - start + 1
    var size = difference / k
    val modulo = difference % k
    if (size == 0) {
      val result:Array[(Int,Int)] = new Array(difference)
      var j = 0
      for (i <- start to end) {
        result(j) = (i, i)
        j += 1
      }
      result
    } else {
      val result:Array[(Int,Int)] = new Array(k)
      if (modulo != 0) size += 1
      var subEnd = start-1
      for (i <- 0 to k-1) {
        if (modulo != 0 && i == modulo) size -= 1
        val subStart = subEnd + 1
        if (i == k-1) {
          subEnd = end
        } else {
          subEnd = subStart + size - 1
        }
        result(i) = (subStart, subEnd)
      }
      result
    }
  }

  private def mySat(start:Int, end:Int): Boolean = {
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
    tUsatDel.start()
    satSolver.undo()
    tUsatDel.end()
    isSAT
  }
  
}