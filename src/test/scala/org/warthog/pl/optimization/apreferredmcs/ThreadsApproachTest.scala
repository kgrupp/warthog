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

import java.io.File

import org.specs2.mutable.Specification
import org.warthog.pl.parsers.maxsat.PartialWeightedMaxSATReader

/**
 * Tests linear search
 *
 * @author Konstantin Grupp
 */
class ThreadsApproachTest extends Specification {

  val fs = System.getProperty("file.separator")

  private def getFileString(folder: String, file: String) =
    List("src", "test", "resources", "maxsat", "partial", folder, file).mkString(File.separator)

  private def testWCNFDIMACSFile(subFolder: String, fileName: String, expResult: Option[List[Int]]) {
    val solver = new ThreadsApproach(List( 
        new ModifiedSatSolverApproach2(PartitionStrategy.constant(2))))//,new ModifiedSatSolverApproach()))
    val expText = if (expResult.isEmpty) "no solution" else "solution " + expResult.get.size
    "File " + fileName + " with " + solver.name should {
      "have " + expText in {
        val reader = new PartialWeightedMaxSATReader()
        reader.read(getFileString(subFolder, fileName))

        solver.reset()
        solver.addHardConstraint(reader.hardClauses)
        val result = solver.solve(reader.softClauses.toList)

        result must be equalTo expResult
      }
    }
  }
  
  testWCNFDIMACSFile("simple", "emptyAndNotEmptyClauses.wcnf", None)

  testWCNFDIMACSFile("simple", "f01.wcnf", Some(List()))
  testWCNFDIMACSFile("simple", "f02.wcnf", Some(List()))
  testWCNFDIMACSFile("simple", "f03.wcnf", Some(List(5)))
  testWCNFDIMACSFile("simple", "f04.wcnf", Some(List(10)))
  testWCNFDIMACSFile("simple", "f05.wcnf", Some(List(6)))

  testWCNFDIMACSFile("simple", "f06.wcnf", Some(List(2)))
  testWCNFDIMACSFile("simple", "f07.wcnf", Some(List(0, 2)))
  testWCNFDIMACSFile("simple", "f08.wcnf", Some(List(0, 1, 2, 3, 4)))
  testWCNFDIMACSFile("simple", "f09.wcnf", None)
  testWCNFDIMACSFile("simple", "f10.wcnf", None)

  testWCNFDIMACSFile("simple", "f11.wcnf", Some(List(0, 2)))

  testWCNFDIMACSFile("simple", "oneClauseFormulaSoft.wcnf", Some(List()))
  testWCNFDIMACSFile("simple", "oneClauseFormulaHard.wcnf", Some(List()))
  testWCNFDIMACSFile("simple", "oneEmptyClauseSoft.wcnf", Some(List(0)))
  testWCNFDIMACSFile("simple", "oneEmptyClauseHard.wcnf", None)
  testWCNFDIMACSFile("simple", "oneVariableFormula.wcnf", Some(List()))
  testWCNFDIMACSFile("simple", "oneVariableOneClauseFormulaSoft.wcnf", Some(List()))
  testWCNFDIMACSFile("simple", "oneVariableOneClauseFormulaHard.wcnf", Some(List()))
  testWCNFDIMACSFile("simple", "threeEmptyClauses.wcnf", None)

  testWCNFDIMACSFile("randomVertexCover", "edges00040_vertices00010.wcnf", Some(List(0, 1, 3, 5, 6, 7, 8, 9)))
  testWCNFDIMACSFile("randomVertexCover", "edges00150_vertices00020.wcnf", Some(List(2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19)))
  
  testWCNFDIMACSFile2("ijcai13-bench" + fs + "mm-s12", "depots2_ks99i.shuffled-as.sat05-4011.cnf.wcnf", 422)
  testWCNFDIMACSFile2("ijcai13-bench" + fs + "mm-s12", "a620test0100-modified2.cnf.wcnf", 6)
  testWCNFDIMACSFile2("simple", "testingMinisatRework1.wcnf", 1)
  testWCNFDIMACSFile2("ijcai13-bench" + fs + "mm-s11", "huge-r.cnf.wcnf", 118)
  /*Some(List(  3,   6,  17,  23,  24,  26,  27,  31,  42,  55,  56,  68,  69,  91,  94,  95, 101, 112, 113, 127, 146, 170, 182, 183, 190, 206, 209, 220, 222, 239, 
              245, 247, 265, 285, 287, 301, 318, 335, 337, 339, 353, 357, 358, 360, 368, 372, 378, 385, 390, 391, 400, 407, 410, 412, 414, 417, 423, 432, 433, 442, 
              443, 449, 453, 455, 462, 466, 485, 490, 491, 497, 502, 524, 528, 529, 531, 534, 540, 560, 566, 569, 583, 592, 601, 608, 630, 633, 651, 652, 657, 660, 
              666, 672, 680, 689, 700, 707, 730, 745, 748, 756, 757, 758, 765, 782, 783, 806, 815, 818, 825, 839, 849, 850, 852, 886, 889, 902, 908, 925))
   */
  testWCNFDIMACSFile2("ijcai13-bench" + fs + "mm-s12", "dme3ptimonegTest.cnf.wcnf", 3)
  testWCNFDIMACSFile2("ijcai13-bench" + fs + "mm-s12", "dme3ptimonegOrdered.cnf.wcnf", 189)
  testWCNFDIMACSFile2("ijcai13-bench" + fs + "mm-s12", "dme3ptimoneg.cnf.wcnf", 189)
  
  private def testWCNFDIMACSFile2(subFolder: String, fileName: String, result1: Int) {
    val solver = new ThreadsApproach(List(new ModifiedSatSolverApproach(), 
        new ModifiedSatSolverApproach2(PartitionStrategy.constant(2))))
    "File " + fileName should {
      "have " + result1 + " MCS clauses" in {
        val reader = new PartialWeightedMaxSATReader()
        reader.read(getFileString(subFolder, fileName))

        solver.reset()
        solver.addHardConstraint(reader.hardClauses)
        val result = solver.solve(reader.softClauses.toList)

        result.get.size must be equalTo result1
      }
    }
  }
}
