package pal

import scala.collection.mutable

import ScaffoldGalil.{FPP_QUANTUM, OnlineGalil, OnlineSource}

/** Executable FIFO service specification; local SCA lowering is separate.
  *
  * The deque models the buffer for this reference. It is not claimed to be a
  * finite local transition table. Output decisions depend only on source events
  * and buffer emptiness; diagnostic counts do not guide the source or scheduler.
  *
  * Python 原典: `galil_realtime.py`。
  */
object GalilRealtime {

  /** A source behind a FIFO buffer that is granted `service` transitions per offered symbol. */
  class BufferedSource(val source: OnlineSource, val service: Int) {
    if (service < 1) {
      throw new IllegalArgumentException("positive integral source service required")
    }

    val pending: mutable.ArrayDeque[String] = mutable.ArrayDeque.empty

    // diagnostic counts
    var offered: Int = 0
    var reads: Int = 0
    var outputs: Int = 0
    var transitions: Int = 0
    var maxPending: Int = 0

    /** The last answer was the source's own output for the last offered symbol. */
    var lastCompleted: Boolean = false

    /** Offer one symbol, run the service, and answer for it (0 while still behind). */
    def read(char: String): Int = {
      if (char != "a" && char != "b") {
        throw new IllegalArgumentException("one binary input symbol required")
      }
      pending.append(char)
      offered += 1
      maxPending = math.max(maxPending, pending.size)
      var answer = 0
      lastCompleted = false
      var slot = 0
      var quiescent = false
      while (slot < service && !quiescent) {
        if (source.inputReady && pending.isEmpty) {
          quiescent = true // remaining service transitions are quiescent
        } else {
          val result = if (source.inputReady) {
            val readResult = source.read(pending.removeHead())
            reads += 1
            readResult
          } else {
            source.work()
          }
          transitions += 1
          result.output.foreach { value =>
            outputs += 1
            if (pending.isEmpty) {
              answer = value
              lastCompleted = true
            }
          }
          slot += 1
        }
      }
      answer
    }
  }

  /** The buffered online controller with the service derived from its quantum.
    *
    * @param galil the wrapped controller (`source`, with its concrete type)
    */
  final class RealtimeGalil private (val galil: OnlineGalil) extends BufferedSource(galil, galil.timing.service) {
    def acceptsEmpty: Boolean = RealtimeGalil.acceptsEmpty
  }

  object RealtimeGalil {
    def apply(quantum: Int = FPP_QUANTUM): RealtimeGalil = new RealtimeGalil(new OnlineGalil(quantum))

    /** Python `accepts_empty` (a static method): the empty word is a palindrome. */
    def acceptsEmpty: Boolean = true
  }
}
