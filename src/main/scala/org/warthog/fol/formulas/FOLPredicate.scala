/*
 * Copyright (c) 2011, Andreas J. Kuebler & Christoph Zengler
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

package org.warthog.fol.formulas

import org.warthog.generic.formulas.{ Literal, Formula }

/**
  * FOL predicate application
  * @param symbol the predicate symbol
  * @param args the applied terms
  */
case class FOLPredicate(symbol: PredicateSymbol, phase: Boolean, args: FOLTerm*)
    extends Formula[FOL] with Literal[FOL] {

  def negate = FOLPredicate(symbol, !phase, args: _*)

  def getAtom = FOLPredicate(symbol, true, args: _*)

  override def toString = {
    val s = if (args.size == 0)
      symbol.toString
    else if (args.size == 2 && symbol.name.size == 1 && "<>=".contains(symbol.name))
      "(" + args(0) + " " + symbol + " " + args(1) + ")"
    else
      symbol + "(" + (args.mkString(",")) + ")"
    if (phase) s else Formula.NOT + s
  }

  def atoms = List(FOLPredicate(symbol, true, args: _*).asInstanceOf[Literal[FOL]])

  def vars = if (args.size > 0) args.map(_.vars).reduce(_ union _).distinct else List()

  def functions = args.foldLeft(List[FunctionSymbol]())((set, elem) => set union elem.functions).distinct

  def numOfNodes = args.foldLeft(1)((s, e) => s + e.numOfNodes)

  def tsubst(s: Map[FOLVariable, FOLTerm]): FOLPredicate = FOLPredicate(symbol, phase, args.map(_.tsubst(s)): _*)
}

object FOLPredicate {
  def apply(name: String, args: FOLTerm*): FOLPredicate =
    new FOLPredicate(new PredicateSymbol(name, args.length), true, args: _*)

  def apply(name: String, phase: Boolean, args: FOLTerm*): FOLPredicate =
    new FOLPredicate(new PredicateSymbol(name, args.length), phase, args: _*)

}
