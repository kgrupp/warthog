/*
 * Copyright (c) 2011-2014, Andreas J. Kuebler & Christoph Zengler & Konstantin Grupp
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

package org.warthog.pl.printer

import org.warthog.pl.formulas.PL
import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.PLLiteral

/**
 * @author Konstantin Grupp
 */
class WeightedDIMACSPrinter {

  /**
   * Returns a string in weighted DIMACS format.
   * 
   * Note: Works only correct, if variable names are represented by integers
   */
  def print(hardClauses: List[ClauseLike[PL, PLLiteral]], softClauses: List[ClauseLike[PL, PLLiteral]]): String = {

    var s: StringBuilder = new StringBuilder()
    val hardInt = hardClauses.size + softClauses.size + 1
    val vars = Set[String]()
    for (clause <- hardClauses) {
      s ++= hardInt + " "
      for (lit <- clause.literals) {
        vars.+(lit.variable.toString)
        if (lit.phase) {
          s ++= lit.variable + " "
        } else {
          s ++= "-" + lit.variable + " "
        }
      }
      s ++= "0\n"
    }
    for (clause <- softClauses) {
      s ++= "1 "
      for (lit <- clause.literals) {
        vars.+(lit.variable.toString)
        if (lit.phase) {
          s ++= lit.variable + " "
        } else {
          s ++= "-" + lit.variable + " "
        }
      }
      s ++= "0\n"
    }
    "p wcnf " + hardClauses.size + softClauses.size + " " + vars.size + " " + hardInt + "\n" + s.mkString
  }

}