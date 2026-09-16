import PalPeg.TextFeedPipelineService
import PalPeg.TextFeedPipelinePrefixFedPhysical

/-! The completed prefix supplies a physical verifier snapshot. The ideal
text is only a refinement witness; no future input is written to the machine. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineInitial
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineBank
open PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineVerifier
open PalPeg.TextFeedPipelinePrefixFedPhysical PalPeg.TextFeedPipelineSourceSafety

variable {k : ℕ} {Terminal : Type}

theorem prefix_snapshot {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {leftPat rightPat Text : List (Fin k)} {x : Config e leftSym R rate}
    (h : Complete e leftSym R rate leftPat rightPat Text rate p r n x)
    (hs : SourceSafe e leftSym rate x.1.1.2.2)
    (hz : x.1.1.1 ≠ 0) (hn : n ≤ Text.length) :
    ∃ u : Snapshot k,
      Valid e leftSym R rate Text n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x)
        u [verifyLoop rate] ∧
      u.frames = [] ∧
      VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
        leftPat rightPat Text rate p r n u.model ∧
      u.model.z.1.pos = leftPat.length ∧ u.model.z.1.q = 0 ∧
      u.model.z.2 = 0 ∧
      u.dir = (x.2 38).applyAction e.blank (e.mark, .stay) := by
  obtain ⟨_, D, M, U, qt₁, m₁, qt₂, m₂, hd, ht, hq₁, hq₂, hf, hp, hq, hm⟩ := h.ready
  obtain ⟨hyt, hyb, hyc, _⟩ := h.enter (Terminal := Terminal) hz
  let V := TextFeedPrefixReady.model M U D.X D.q₂ ⟨qt₂ ∘ m₂.roles, 0⟩
  have ht' : x.2 = tapes e qt₁ m₁ qt₂ m₂ V D.aux D.old D.dir := by
    rw [ht]
    unfold TextFeedPrefixMachine.tapes
    rw [hd]
    rfl
  let u : Snapshot k := ⟨qt₁, m₁, qt₂, m₂, V, D.aux, D.old,
    D.dir.applyAction e.blank (e.mark, .stay),
    VerifierFeedRefinement.idealTapes e Text V
      (V.z.1.pos + V.z.1.q) (V.z.1.pos - leftPat.length + V.z.2),
    V.z.1.pos + V.z.1.q, V.z.1.pos - leftPat.length + V.z.2, []⟩
  refine ⟨u, ⟨hyb, run_safe e leftSym R rate x hs, hyc, ?_, hq₁, hq₂,
    VerifierFeedRefinement.initial hn (VerifierFeedRaw.of_feedInv hf)⟩,
    rfl, hf, hp, hq, rfl, ?_⟩
  · rw [hyt, ht', TextFeedPipelineFrameControl.writeDir_tapes]
    rfl
  · change D.dir.applyAction e.blank (e.mark, .stay) = _
    rw [ht']
    rfl

/-- The same physical handoff establishes service and semantic invariants.
A nonempty left pattern pays the three pending calls; the zigzag deadline
supplies the initial verification quota. -/
theorem prefix_service {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {leftPat rightPat Text : List (Fin k)} {x : Config e leftSym R rate}
    (h : Complete e leftSym R rate leftPat rightPat Text rate p r n x)
    (hs : SourceSafe e leftSym rate x.1.1.2.2)
    (hz : x.1.1.1 ≠ 0) (hn : n ≤ Text.length)
    (hdir : (x.2 38).applyAction e.blank (e.mark, .stay) =
      GSVProgZLoop.dirTape e.blank e.mark true 0)
    (hleft : 0 < leftPat.length)
    (hdeadline : GSVerifierZ.ZDeadline leftPat rightPat rate p r) :
    ∃ a : TextFeedPipelineService.Entry e leftSym R rate Text leftPat rightPat p r n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x),
      a.rank = 3 ∧ a.z.1.pos = leftPat.length ∧ a.z.1.q = 0 ∧
      a.z.2 = ⟨0, 0, 0, true⟩ ∧
      ScanInv rightPat (TextFeed.padW e.blank Text Text.length) a.z.1 ∧
      GSVerifierZ.ZInv leftPat rightPat (TextFeed.padW e.blank Text Text.length) a.z := by
  obtain ⟨u, hv, hf, hfeed, hp, hq, hh, hd⟩ := prefix_snapshot h hs hz hn
  let z : GSVerifierZ.VStateZ := (u.model.z.1, ⟨0, 0, 0, true⟩)
  have hg : u.model.z = (z.1, z.2.head) := by
    apply Prod.ext
    · rfl
    · exact hh
  have hw : GSVerifierZ.ZWf leftPat.length z.2 := by
    simp [GSVerifierZ.ZWf, z]
  have hc : 3 ≤ TextFeedPipelineFrontier.progressRate rate *
      Phi rate z.1 := by
    have hmul : 1 ≤ (rate + 1) * leftPat.length := Nat.mul_pos (by omega) hleft
    have hbound := Nat.mul_le_mul_left (TextFeedPipelineFrontier.progressRate rate) hmul
    simp only [Nat.mul_one] at hbound
    have hrate : 15 ≤ TextFeedPipelineFrontier.progressRate rate := by
      unfold TextFeedPipelineFrontier.progressRate
      omega
    simp only [z, Phi, hp, hq, Nat.add_zero]
    omega
  have hscan : ScanInv rightPat (TextFeed.padW e.blank Text Text.length) z.1 := by
    rw [ScanInv, show z.1.q = 0 from hq]
    exact ⟨matchLen_zero _ _ _, Nat.zero_le _⟩
  have hzinv : GSVerifierZ.ZInv leftPat rightPat
      (TextFeed.padW e.blank Text Text.length) z := by
    refine ⟨Nat.le_of_eq hp.symm, hw, GSVerifierZ.matchIv_empty _ _ _ 0, ?_⟩
    intro _
    have hd₀ := hdeadline 0 (Nat.zero_le _)
    have hle := Nat.mul_le_mul_left GSVerifierZ.zQuota
      (Nat.sub_le rightPat.length (gsNextQ rate p r 0))
    simp only [z, GSVerifierZ.zrem, hq, Nat.sub_zero, ↓reduceIte]
    omega
  exact ⟨TextFeedPipelineService.Entry.initial u z hv hf hfeed hg hw
    (hd.trans hdir) hc, rfl, hp, hq, rfl, hscan, hzinv⟩

/-- Boot the actual loop before charging verifier progress. This includes
empty left patterns and input interruptions: at most six scheduled calls
and three actual arrivals expose the first macro. -/
theorem prefix_boot {e : Env k} (hcode : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} (hR : 0 < R)
    (enc : Terminal → Fin k) {leftPat rightPat Text : List (Fin k)}
    {x : Config e leftSym R rate}
    (h : Complete e leftSym R rate leftPat rightPat Text rate p r n x)
    (hs : SourceSafe e leftSym rate x.1.1.2.2) (hz : x.1.1.1 ≠ 0)
    (hfirst : x.1.1.2.1 = false)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (hdir : (x.2 38).applyAction e.blank (e.mark, .stay) =
      GSVProgZLoop.dirTape e.blank e.mark true 0)
    (as : List Terminal) (hlen : 3 ≤ as.length) (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a)) :
    ∃ m pre post y,
      ∃ a : TextFeedPipelineService.Macro e leftSym R rate Text leftPat rightPat p r
          (n + pre.length) y,
      m ≤ 6 ∧ pre.length ≤ 3 ∧ as = pre ++ post ∧
      (TextFeedPipelineReentryInput.tick e leftSym R rate enc)^[m]
        (as, TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) = (post, y) ∧
      a.z.1.pos = leftPat.length ∧ a.z.1.q = 0 ∧ a.z.2 = ⟨0, 0, 0, true⟩ ∧
      a.events = [] ∧
      ((rate + 1) * (n + 3) ≤
          (rate + 1) * leftPat.length + rate * rightPat.length →
        TextFeedPipelineService.target rate rightPat (n + pre.length) ≤ a.score) := by
  obtain ⟨u, hv, hf, hfeed, hp, hq, hh, hd⟩ := prefix_snapshot h hs hz (by omega)
  let z : GSVerifierZ.VStateZ := (u.model.z.1, ⟨0, 0, 0, true⟩)
  have hg : u.model.z = (z.1, z.2.head) := Prod.ext rfl hh
  have hw : GSVerifierZ.ZWf leftPat.length z.2 := by simp [GSVerifierZ.ZWf, z]
  have he : TextFeedPipelineReentryInput.Entry e leftSym R rate Text n
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) u 3 :=
    ⟨hv, by simp only [hf, TextFeedPipelineFrames.next]⟩
  obtain ⟨m, pre, post, y, v, hmc, hpc, hsplit, hrun, hv', hi, hd', _⟩ :=
    TextFeedPipelineReentryInput.finish hcode hmb leftSym R rate hR enc hb hm
      3 n as (by omega) hlen hn ha _ u he
      (TextFeedPipelineInputRun.run_not_first leftSym R rate x hfirst)
  obtain ⟨hvalid, hstart⟩ := TextFeedPipelineReentry.restart hv hfeed hg hw
    (hd.trans hdir) hv'.1 hv'.2 hi hd'
  let v' := TextFeedPipelineMacroBoundary.annotate v z
  let a : TextFeedPipelineService.Macro e leftSym R rate Text leftPat rightPat p r
      (n + pre.length) y :=
    { n₀ := n + pre.length, x₀ := y, u₀ := v', z := z, u := v'
      events := [], waits := 0, frontier := Nat.le_refl _
      origin := hvalid, start := hstart, valid := hvalid
      follows := .nil _, wait_le := by simp, credit := by simp }
  refine ⟨m, pre, post, y, a, hmc, hpc, hsplit, hrun, hp, hq, rfl, rfl, ?_⟩
  intro hbudget
  apply a.initial_deadline hp hq
  exact (Nat.mul_le_mul_left (rate + 1) (by omega : n + pre.length ≤ n + 3)).trans hbudget

/-- Complete the pending workers of a startup frame, then use ordinary
input rounds. The trace retains the startup suffix; no scan state or
output is reset at the next arrival boundary. -/
theorem pending_frames {e : Env k} (hcode : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (a : TextFeedPipelineService.State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, TextFeedPipelineInputMacro.Conditions e Text leftPat rightPat rate p r z)
    (hpat : 0 < rightPat.length) (N : ℕ) (as : List Terminal)
    (hn : n + as.length ≤ Text.length)
    (has : ∀ j c, as[j]? = some c → Text[n + j]? = some (enc c))
    (hworker : ∀ j < N,
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j] x).1.1.1 ≠ 0)
    (hend : ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false)
    (hR : TextFeedPipelineFrontier.progressRate rate * (rate + 1) ≤ R)
    (ha : TextFeedPipelineService.target rate rightPat n ≤ a.score + N) :
    ∃ b : TextFeedPipelineService.State e leftSym R rate Text leftPat rightPat p r (n + as.length)
        (TextFeedPipelineInputRun.frames e leftSym R rate enc as
          ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x)),
      TextFeedPipelineService.Trace e leftSym R rate enc Text leftPat rightPat p r a
        (List.replicate N none ++ TextFeedPipelineService.schedule R as) b ∧
      TextFeedPipelineService.target rate rightPat (n + as.length) ≤ b.score := by
  obtain ⟨b, ht, hb⟩ := a.workers hcode leftSym R rate N enc hc hpat (by omega) hworker
  rw [Nat.min_eq_right ha] at hb
  have hf : ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.2.1 = false := by
    clear hworker hend ha b ht hb
    induction N with
    | zero => exact hfirst
    | succ N ih =>
      simpa only [Function.iterate_succ_apply'] using
        TextFeedPipelineInputRun.run_not_first leftSym R rate
          ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x) ih
  obtain ⟨c, htc, hcredit⟩ := b.frames hcode leftSym R rate enc hc hpat as hn has hend hf hR hb
  exact ⟨c, ht.trans htc, hcredit⟩

/-- info: 'PalPeg.TextFeedPipelineInitial.pending_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pending_frames

/-- info: 'PalPeg.TextFeedPipelineInitial.prefix_boot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_boot

/-- info: 'PalPeg.TextFeedPipelineInitial.prefix_service' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_service

/-- info: 'PalPeg.TextFeedPipelineInitial.prefix_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_snapshot

end PalPeg.TextFeedPipelineInitial
