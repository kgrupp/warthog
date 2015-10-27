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

/**
 * @author Konstantin Grupp
 */
class PartitionMaker(strategyName: String, calcNumPartitions: (Int, Int) => Int) {

  private var end: Int = 0
  private var currentStart: Int = 0
  private var remaining: Int = 0

  def name() = strategyName

  def createNewInstance() = new PartitionMaker(strategyName, calcNumPartitions)
  
  def initialize(s: Int, e: Int, recDepth: Int) {
    end = e
    currentStart = s
    remaining = calcNumPartitions(recDepth, end - currentStart + 1)
  }

  def hasNext(skip: Int = 0) = currentStart + skip <= end

  def nextPartition(skip: Int): (Int, Int) = {
    val nStart = currentStart + skip
    var nEnd = end

    val difference = end - nStart + 1
    var size = difference / remaining

    if (size == 0) {
      nEnd = nStart
    } else {
      val modulo = difference % remaining

      if (modulo != 0) size += 1
      nEnd = nStart + size - 1
      if (remaining == 1 || end < nEnd) nEnd = end
    }
    remaining -= 1
    currentStart = nEnd + 1
    (nStart, nEnd)
  }
  
  def recursiveSkip(skip: Int) = {
    if (currentStart < end && end < currentStart + skip) {
      currentStart + skip - end
    } else {
      0
    }
  }

}