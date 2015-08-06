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

import java.io.File

import org.specs2.mutable.Specification
import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.{ ImmutablePLClause => Clause }
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.Minisat
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.MinisatRework1
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.MinisatRework2
import org.warthog.pl.formulas.PL
import org.warthog.pl.parsers.maxsat.PartialWeightedMaxSATReader
import org.warthog.pl.decisionprocedures.satsolver.impl.minisatjava.Minisat

class LinearSearchTest extends Specification {

  val fs = System.getProperty("file.separator")
  

  private def getFileString(folder: String, subFolder: String, file: String) =
    List("src", "test", "resources", folder, subFolder, file).mkString(File.separator)

  private def testWCNFDIMACSFile(subFolder: String, fileName: String, expResult: Option[Set[ClauseLike[PL, PLLiteral]]]) {
    val solver = new LinearSearch(new Minisat())
    val expText = if (expResult.isEmpty) "no solution" else "solution " + expResult.get.size
    "File " + fileName should {
      "have " + expText in {
        val reader = new PartialWeightedMaxSATReader()
        reader.read(getFileString("maxsat", subFolder, fileName))

        solver.reset()
        solver.addHardConstraint(reader.hardClauses)
        val result = solver.solveAPreferredMCS(reader.softClauses.toList)

        result must be equalTo expResult
      }
    }
  }
  
  val (v1, v2, v3, v4, v5, v6) = (PLLiteral("1", true), PLLiteral("2", true), PLLiteral("3", true), PLLiteral("4", true), PLLiteral("5", true), PLLiteral("6", true))
  val (v1f, v2f, v3f, v4f, v5f, v6f) = (PLLiteral("1", false), PLLiteral("2", false), PLLiteral("3", false), PLLiteral("4", false), PLLiteral("5", false), PLLiteral("6", false))
  val (v7f, v8f, v9f, v10f, v11f, v12f) = (PLLiteral("7", false), PLLiteral("8", false), PLLiteral("9", false), PLLiteral("10", false), PLLiteral("11", false), PLLiteral("12", false))
  val (v13f, v14f, v15f, v16f, v17f, v18f) = (PLLiteral("13", false), PLLiteral("14", false), PLLiteral("15", false), PLLiteral("16", false), PLLiteral("17", false), PLLiteral("18", false))

  testWCNFDIMACSFile2("partial" + fs + "ijcai13-bench" + fs + "mm-s12", "depots2_ks99i.shuffled-as.sat05-4011.cnf.wcnf", 422)
  testWCNFDIMACSFile2("partial" + fs + "simple", "testingMinisatRework1.wcnf", 1)
  private def testWCNFDIMACSFile2(subFolder: String, fileName: String, result1: Int) {
    val solver = new LinearSearch(new MinisatRework1())
    "File " + fileName should {
      "have " + result1 + " MCS clauses" in {
        val reader = new PartialWeightedMaxSATReader()
        reader.read(getFileString("maxsat", subFolder, fileName))

        solver.reset()
        solver.addHardConstraint(reader.hardClauses)
        val result = solver.solveAPreferredMCS(reader.softClauses.toList)
        result.get.size must be equalTo result1
      }
    }
  }
  testWCNFDIMACSFile("partial" + fs + "simple", "emptyAndNotEmptyClauses.wcnf", None)

  testWCNFDIMACSFile("partial" + fs + "simple", "f01.wcnf", Some(Set()))
  testWCNFDIMACSFile("partial" + fs + "simple", "f02.wcnf", Some(Set()))
  testWCNFDIMACSFile("partial" + fs + "simple", "f03.wcnf", Some(Set(new Clause(v1f, v2f, v3))))
  testWCNFDIMACSFile("partial" + fs + "simple", "f04.wcnf", Some(Set(new Clause(v5, v6))))
  testWCNFDIMACSFile("partial" + fs + "simple", "f05.wcnf", Some(Set(new Clause(v1f))))

  testWCNFDIMACSFile("partial" + fs + "simple", "f06.wcnf", Some(Set(new Clause(v2, v3))))
  testWCNFDIMACSFile("partial" + fs + "simple", "f07.wcnf", Some(Set(new Clause(v2, v3), new Clause(v1f))))
  testWCNFDIMACSFile("partial" + fs + "simple", "f08.wcnf", Some(Set(new Clause(v5f), new Clause(v4f), new Clause(v2f), new Clause(v1f), new Clause(v3f))))
  testWCNFDIMACSFile("partial" + fs + "simple", "f09.wcnf", None)
  testWCNFDIMACSFile("partial" + fs + "simple", "f10.wcnf", None)

  testWCNFDIMACSFile("partial" + fs + "simple", "f11.wcnf", Some(Set(new Clause(v1f, v2f), new Clause(v2f, v3f))))

  testWCNFDIMACSFile("partial" + fs + "simple", "oneClauseFormulaSoft.wcnf", Some(Set()))
  testWCNFDIMACSFile("partial" + fs + "simple", "oneClauseFormulaHard.wcnf", Some(Set()))
  testWCNFDIMACSFile("partial" + fs + "simple", "oneEmptyClauseSoft.wcnf", Some(Set(new Clause())))
  testWCNFDIMACSFile("partial" + fs + "simple", "oneEmptyClauseHard.wcnf", None)
  testWCNFDIMACSFile("partial" + fs + "simple", "oneVariableFormula.wcnf", Some(Set()))
  testWCNFDIMACSFile("partial" + fs + "simple", "oneVariableOneClauseFormulaSoft.wcnf", Some(Set()))
  testWCNFDIMACSFile("partial" + fs + "simple", "oneVariableOneClauseFormulaHard.wcnf", Some(Set()))
  testWCNFDIMACSFile("partial" + fs + "simple", "threeEmptyClauses.wcnf", None)

  testWCNFDIMACSFile("partial" + fs + "randomVertexCover", "edges00040_vertices00010.wcnf", Some(Set(new Clause(v1f), new Clause(v2f), 
      new Clause(v3f), new Clause(v4f), new Clause(v5f), new Clause(v7f), new Clause(v9f), new Clause(v10f))))
  testWCNFDIMACSFile("partial" + fs + "randomVertexCover", "edges00150_vertices00020.wcnf", Some(Set(new Clause(v1f), new Clause(v2f), 
      new Clause(v3f), new Clause(v4f), new Clause(v5f), new Clause(v6f), new Clause(v7f), new Clause(v8f), new Clause(v10f), new Clause(v11f),
      new Clause(v12f), new Clause(v13f), new Clause(v14f), new Clause(v15f), new Clause(v16f), new Clause(v17f), new Clause(v18f))))
}
