package org.warthog.pl.optimization.maxsat.apreferredmcs

/**
 * @author Konstantin Grupp
 */
class TimeUsed(functionName:String) {
  
  private var time:Long = 0
  private var counter:Int = 0
  private var lastStart:List[Long] = List()
  
  def start() = {
    lastStart = lastStart.+:(System.currentTimeMillis())
    counter += 1
  }
  
  def end() = {
    time += System.currentTimeMillis() - lastStart.head
    lastStart = lastStart.tail
  }
  
  def getInfo() = functionName + "\t\t" + time + "ms\t\t" + counter + " Aufrufe"  
  
}