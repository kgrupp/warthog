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

package org.warthog.pl.optimization.apreferredmcs.impl

import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.formulas.PL
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.formulas.PLAtom
import scala.util.control.Breaks.{break, breakable}

/**
 * @author Konstantin Grupp
 */
class ClauseBAB(clause:ClauseLike[PL, PLLiteral], assignment:Map[PLAtom, Boolean]) {
  
  {
    var allAssigned = true
    breakable {
      for (lit <- clause.literals) {
        val phaseOpt = assignment.get(lit.variable)
        if (phaseOpt.isEmpty) {
          allAssigned = false
        } else {
          if (lit.phase == phaseOpt.get) {
            state = State.TRUE
            break
          }
        }
      }
      if (allAssigned) {
        state = State.FALSE
      }
    }
  }
  
  object State extends Enumeration {
    type State = Value
    val TRUE, FALSE, UNDEF = Value 
  }
  
  var state = State.UNDEF
  
  def getClause() = clause
  
  def isEmpty() = state == State.FALSE
  def isSatisfied() = state == State.TRUE
  def isOpen() = state == State.UNDEF
  
}