package org.warthog.pl.optimization.apreferredmcs

import scala.util.control.Breaks.{ break, breakable }
import scala.language.implicitConversions
import org.warthog.generic.datastructures.cnf.ClauseLike
import org.warthog.pl.datastructures.cnf.PLLiteral
import org.warthog.pl.formulas.PL

/**
 * Implements an version which can make use of different algorithms and returns the result of the fastest algorithm.
 * 
 * Creates threads for each algorithm.
 *
 * @author Konstantin Grupp
 */
class ThreadsApproach(lis: List[APreferredMCSSolver]) extends APreferredMCSSolver {

  override def name = "ThreadsApproach" + lis.foldRight("": String)((solver, result) => "-" + solver.name + result)

  override def reset() {
    super.reset()
    lis.foreach(x => x.reset())
  }

  override def addHardConstraint(clause: ClauseLike[PL, PLLiteral]) {
    lis.foreach(x => x.addHardConstraint(clause))
  }

  override def markHardConstraints() {
    lis.foreach(x => x.markHardConstraints())
  }

  override def undoHardConstraints() {
    lis.foreach(x => x.undoHardConstraints())
  }

  override def areHardConstraintsSatisfiable() = lis.head.solve(List(), false).isDefined

  override protected def solveImpl(softClauses: List[ClauseLike[PL, PLLiteral]]) = {
    implicit def funcToRunnable(func: () => Unit) =
      new Runnable() {
        def run() = {
          try {
            func()
          } catch {
            case ie: InterruptedException => // nothing to do
          }
        }
      }

    var result: Option[List[Int]] = None
    val threadAry: Array[Thread] = new Array(lis.length)
    val threadResultAry: Array[(Boolean, Option[List[Int]])] = new Array(lis.length)

    var i = 0
    for (solver <- lis) {
      val j = i
      threadAry(i) = new Thread(() => {
        val result = solver.solve(softClauses, false)
        this.synchronized {
          threadResultAry(j) = (true, result)
        }
      })
      threadResultAry(i) = (false, None)
      i += 1
    }

    try {
      threadAry.foreach { thread => thread.start }

      while (result.isEmpty) {
        Thread.sleep(10)

        var k = 0
        while (k < threadResultAry.length) {
          if (threadResultAry(k)._1) {
            result = threadResultAry(k)._2

            k = threadResultAry.length
          } else {
            k += 1
          }
        }
      }

    } finally {
      threadAry.foreach { thread => thread.interrupt }
    }

    result.get
  }

}