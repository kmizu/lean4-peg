package pal

/** Service bounds for the window backend's fixed batch instructions. */
final case class BatchRates(k: Int, decomposition: Int, singleStage: Int, firstJob: Int, matching: Int, flags: Int)

/** Service bounds for the window backend's fixed GS batch instructions.
  *
  * The batch movement operands are constants in the finite instruction table.
  * See `GS_LOCAL_CLOCK.md` for their loop accounting. Queue maintenance is done
  * once while preparing each actual input-node window, outside this service.
  *
  * Port of `gs_batch_clock.py`.
  */
object GsBatchClock {
  import GsLocalClock.{derive, powerTwoAtLeast}

  def deriveBatch(k: Int = 8): BatchRates = {
    if (k < 4) {
      throw new IllegalArgumentException("fixed integer k >= 4 required")
    }
    val failed = Fraction(34 * k + 32) + Fraction(10 * k + 2, k - 2)
    val finalStage = Fraction(7 * k + 19) + Fraction(5, k)
    val decomposition = (finalStage + failed * Fraction(k - 2, k * (k - 3))).ceil + 5
    val stage = decomposition + (5 * k + 12) + (3 * k + 6) + 23
    val singleStage = stage + 11
    val firstJob = (Fraction(stage) * Fraction(k - 1, k - 3)).ceil + 11
    // For jobs 2..4, Lower >= b/2, whereas the next stage is <2b/(k-1).
    // With k=8 it is already below Lower. Job 1 still sums all stages.
    if (Fraction(2, k - 1) >= Fraction(1, 2)) {
      throw new IllegalArgumentException("this early-stop job schedule requires k >= 6")
    }
    val flagRate = powerTwoAtLeast(math.max(firstJob, 4 * singleStage + 1))
    // A batch costs no more instructions than its unit expansion; retain the
    // already established logical matcher rate instead of tightening it here.
    val matching = derive(k).matching / 4
    BatchRates(k, decomposition, singleStage, firstJob, matching, math.max(matching, flagRate))
  }

  val DEFAULT_BATCH: BatchRates = deriveBatch()

  /** Quanta for which the Lean proof's step bounds are established
    * (`lean-pal/PalPeg/ScaWindowFast.lean`): matcher 2048, flags 32768. The proven bounds
    * (Decompose within 1698|x| + 230 steps, a flags job within 8098|y| + 10) are looser than the
    * accounting behind `DEFAULT_BATCH`, so the verified source uses larger quanta; `WindowPAL`
    * accepts any rates above the derived ones.
    */
  val VERIFIED_BATCH: BatchRates = DEFAULT_BATCH.copy(matching = 2048, flags = 32768)
}
