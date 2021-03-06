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

import org.warthog.pl.optimization.apreferredmcs.impl.PartitionMaker

/**
 * Provides different strategies for the general chunks algorithm
 * 
 * @author Konstantin Grupp
 */
object PartitionStrategy {

  def linearSearch() = new PartitionMaker("linearSearch", (_, size) => size)

  def fastDiag() = new PartitionMaker("2", (_, _) => 2)

  def constant(k: Int) = new PartitionMaker(k.toString, (_, _) => k)

  def hierarchized(a: Int, b: Int, c: Int) = new PartitionMaker(a + "-" + b + "-" + c,
    (recursionDepth, _) => recursionDepth match {
      case 1 => a
      case 2 => b
      case _ => c
    })

  def maxSize(max: Int) = new PartitionMaker("maxSize-" + max,
    (_, size) => {
      val k = size / max
      if (k < 2) 2
      else k
    })

  def maxSizeHierachized(max1: Int, max2: Int) = new PartitionMaker("maxSize-" + max1 + "-" + max2,
    (recursionDepth, size) => recursionDepth match {
      case 1 => {
        val k = size / max1
        if (k < 2) 2
        else k
      }
      case 2 => {
        val k = size / max2
        if (k < 2) 2
        else k
      }
      case _ => size
    })

  def maxSizeFastDiag(max: Int) = new PartitionMaker("maxSize-" + max + "-FastDiag",
    (recursionDepth, size) => recursionDepth match {
      case 1 => {
        val k = size / max
        if (k < 2) 2
        else k
      }
      case _ => 2
    })

}