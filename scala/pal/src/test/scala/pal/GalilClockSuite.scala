package pal

import FppCost.bounds
import GalilClock.derive

/** Check integer deadline margins, including the zero-radius initial call. (test_galil_clock.py) */
class GalilClockSuite extends munit.FunSuite {

  test("stage cost fits initial and subsequent match deadlines") {
    val dp = bounds().dp
    for (quantum <- Seq(1, 2, 3, 8, 64, 128, 4096)) {
      val timing = derive(quantum)
      for (lower <- 0 until 65) {
        var span = 8 * math.max(lower, 1)
        for (stage <- 0 until 6) {
          val size = span + 1
          val growth = if (stage == 0) { math.max(lower, 1) } else { span / 2 }
          val work = growth + 2 * lower + 2 * size + 7 + (dp(size) + quantum - 1) / quantum
          assert(work <= timing.stageFactor * span, (quantum, lower, stage))
          val (radius, comparisons) = if (stage == 0) {
            ((5 * lower) / 3, work / timing.matchDelay) // freshly reset clock
          } else {
            (span / 8, (work + timing.matchDelay - 1) / timing.matchDelay)
          }
          assert(radius + comparisons <= span / 4, (quantum, lower, stage))
          span *= 2
        }
      }
    }
  }

  test("predictability arithmetic covers positive and negative boundaries") {
    val timing = derive()
    for (size <- 1 until 50) {
      for (oldCenter <- size until 2 * size) {
        for (newCenter <- math.max(oldCenter, size + 1) until 2 * (size + 1)) {
          val delta = newCenter - oldCenter
          val oldK = math.max(oldCenter - size - 1, 0)
          val newK = math.max(newCenter - size - 2, 0)
          val cost = timing.moveSlope * delta + timing.intervalOverhead
          assert((newK - oldK + 2) * timing.predictability >= cost)
          if (newCenter == size + 1) {
            assert(cost <= timing.predictability)
          }
        }
      }
    }
  }
}
