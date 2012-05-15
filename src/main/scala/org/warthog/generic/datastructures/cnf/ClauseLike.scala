/**
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

package org.warthog.generic.datastructures.cnf

import org.warthog.generic.formulas.{Logic, Formula}

/**
 * Trait for a clause
 *
 * Author: zengler
 * Date:   15.05.12
 */
trait ClauseLike[L <: Logic, T <: Literal[L]] {

  /**
   * The sequence of literals in this clause
   * @return the list of literals
   */
  def literals: List[T]

  override def toString = "(" + literals.mkString(", ") + ")"

  override def equals(p1: Any): Boolean =
    if (p1.getClass == this.getClass) {
      val other_lits = p1.asInstanceOf[this.type].literals
      if (other_lits.size != literals.size)
        false
      else {
        for (l <- other_lits) {
          if (!literals.contains(l))
            return false
        }
        true
      }
    } else
      false

  override def hashCode() = literals.foldLeft(1)(_ & _.##)

  /**
   * Delete a literal in this clause
   * @param lit a literal
   */
  def delete(lit: T): ClauseLike[L, T]

  /**
   * Push a literal to this clause
   * @param lit a literal
   */
  def push(lit: T): ClauseLike[L, T]

  /**
   * Add a number of literals to this clause
   * @param lits a list of literals
   */
  def pushLiterals(lits: T*): ClauseLike[L, T]

  /**
   * Unite this clause with another one
   * @param c a clause
   * @return the union of this clause and c
   */
  def union(c: ClauseLike[L, T]): ClauseLike[L, T] = pushLiterals(c.literals: _*)

  /**
   * A formula representation of the clause
   * @return a formula respresentation in propositional logic
   */
  def toFormula: Formula[L]

  /**
   * The size of the clause
   * @return the size of the clause
   */
  def size: Int = literals.size

  /**
   * Is this clause empty?
   * @return `true` if the clause is empty, `false` otherwise
   */
  def isEmpty: Boolean = literals.isEmpty

  /**
   * Is this clause unit?
   * @return `true` if the clause is unit, `false` otherwise
   */
  def isUnit: Boolean = literals.size == 1

  /**
   * Is this clause a tautology?
   * @return `true` if the clause is a tautology, `false` otherwise
   */
  def isTautology: Boolean

  /**
   * Does this clause contain a certain literal
   * @param literal a literal
   * @return `true` if this clause contains the literal, `false` otherwise
   */
  def contains(literal: T): Boolean = literals.contains(literal)

  /**
   * Return the premise of the clause as a list of literals
   * @return the premise of the clause
   */
  def premise: List[T]

  /**
   * Return the consequence of the clause as a list of literals
   * @return the consequence of the clause
   */
  def consequence: List[T]

}
