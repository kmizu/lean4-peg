import PalPeg.TextFeedPipelineInitial
import PalPeg.TextFeedPipelineOutputPrefixSetup
import PalPeg.TextFeedPipelineObserved

/-! Enter the verifier from the completed observed prefix, including a
real arrival when completion coincides with an input boundary. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputInitial
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelinePrefixFedPhysical PalPeg.TextFeedPipelineSourceSafety
open PalPeg.TextFeedPipelineObserved (View pack project opStep)

variable {k : ℕ} {Terminal : Type}

theorem prefix_snapshot {e : Env k} (hcode : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} {leftPat rightPat Text : List (Fin k)}
    (x : View e leftSym R rate)
    (h : Complete e leftSym R rate leftPat rightPat Text rate p r n (project x))
    (hs : SourceSafe e leftSym rate x.1.1.1.2.2)
    (hz : x.1.1.1.1 ≠ 0) (hn : n ≤ Text.length) :
    let y := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x
    project y = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (project x) ∧
    ∃ u : Snapshot k, Valid e leftSym R rate Text n (project y) u [verifyLoop rate] ∧
      u.frames = [] ∧
      VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
        leftPat rightPat Text rate p r n u.model ∧
      u.model.z.1.pos = leftPat.length ∧ u.model.z.1.q = 0 ∧ u.model.z.2 = 0 ∧
      u.dir = (x.2 38).applyAction e.blank (e.mark, .stay) := by
  obtain ⟨u, hv, hf, hfeed, hp, hq, hh, hd⟩ :=
    TextFeedPipelineInitial.prefix_snapshot (Terminal := Terminal) h hs hz hn
  have he := TextFeedPipelineOutput.step_preserves (Terminal := Terminal) hcode x hv
  change project (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x) =
    TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (project x) at he
  exact ⟨he, u, he.symm ▸ hv, hf, hfeed, hp, hq, hh, hd⟩

/-- Arrival at a finished prefix is still real queue work. It preserves
completion and exposes the next worker slot without resetting state. -/
theorem complete_arrival {e : Env k} (hcode : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {leftSym : Fin k} {R rate d p r n : ℕ}
    {u v Text : List (Fin k)} (enc : Terminal → Fin k) (x : View e leftSym R rate)
    (h : Complete e leftSym R rate u v Text d p r n (project x))
    (hz : x.1.1.1.1 = 0) (hR : 0 < R) (a : Terminal)
    (hn : n < Text.length) (ha : Text[n]? = some (enc a)) (ham : enc a ≠ e.mark) :
    let y := opStep e leftSym R rate enc x (some a)
    Complete e leftSym R rate u v Text d p r (n + 1) (project y) ∧
      y.1.1.1.1 ≠ 0 ∧
      project y = TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
        (TextFeedPipelineInputRun.captured e leftSym R rate enc a (project x)) := by
  obtain ⟨z, hl, hg, hr⟩ := h
  obtain ⟨he, hl'⟩ := TextFeedPipelineOutputPrefix.arrival_step hcode hmb enc hl hz a ham
    x.1.2.1 x.1.2.2
  have hg' := hg.arrive hmb hn ha
  have hr' := hr.arrival hn ha
  refine ⟨⟨TextFeedPipelinePrefixLink.arrival (enc a) z, hl', hg', hr'⟩, ?_, he⟩
  have hp := congrArg (fun t : Config e leftSym R rate => t.1.1.1) he
  exact fun hh => TextFeedPipelineReentryInput.after_arrival e leftSym R rate hR enc a
    (project x) hz (hp.symm.trans hh)

noncomputable def tick (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (z : List Terminal × View e leftSym R rate) : List Terminal × View e leftSym R rate :=
  if z.2.1.1.1.1 = 0 then
    match z.1 with
    | [] => z
    | a :: as => (as, opStep e leftSym R rate enc z.2 (some a))
  else (z.1, opStep e leftSym R rate enc z.2 none)

open PalPeg.TextFeedPipelineReentryInput (Entry)
open PalPeg.VerifierFeedSupplyProgress (filled)

theorem entry_worker {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n s : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : View e leftSym R rate) (u : Snapshot k)
    (h : Entry e leftSym R rate Text n (project x) u s) (hpos : 0 < s) (hs : s ≤ 3)
    (hz : x.1.1.1.1 ≠ 0) (hf : x.1.1.1.2.1 = false) :
    let y := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x
    ∃ t v, t < s ∧ Entry e leftSym R rate Text n (project y) v t ∧
      v.ideal = u.ideal ∧ v.dir = u.dir ∧ filled u.model ≤ filled v.model ∧
      y.1.1.1.2.1 = false := by
  obtain ⟨t, v, ht, hv, hi, hd, hm'⟩ := h.worker hc hmb leftSym R rate hb hm hn
    (project x) u hpos hs hz
  have he := TextFeedPipelineOutput.step_preserves (Terminal := Terminal) hc x hv.1
  change project (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x) =
    TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (project x) at he
  refine ⟨t, v, ht, he.symm ▸ hv, hi, hd, hm', ?_⟩
  exact (congrArg (fun q : Config e leftSym R rate => q.1.1.2.1) he).trans
    (TextFeedPipelineInputRun.run_not_first leftSym R rate (project x) hf)

theorem entry_arrival {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (hR : 0 < R) (enc : Terminal → Fin k) (a : Terminal)
    {Text : List (Fin k)} {n s : ℕ} (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : View e leftSym R rate) (u : Snapshot k)
    (h : Entry e leftSym R rate Text n (project x) u s) (hs : s ≤ 3) (hz : x.1.1.1.1 = 0)
    (hf : x.1.1.1.2.1 = false) (ha : Text[n]? = some (enc a)) :
    let y := opStep e leftSym R rate enc x (some a)
    ∃ v, Entry e leftSym R rate Text (n + 1) (project y) v s ∧
      v.ideal = u.ideal ∧ v.dir = u.dir ∧ filled u.model ≤ filled v.model ∧
      y.1.1.1.2.1 = false ∧ y.1.1.1.1 ≠ 0 := by
  obtain ⟨v, hv, hi, hd, hmono⟩ := h.arrival hc hmb leftSym R rate enc a hm hn
    (project x) u hs hz hf ha
  have he := TextFeedPipelineOutput.step_preserves (Terminal := Terminal) hc
    (pack (TextFeedPipelineInputRun.captured e leftSym R rate enc a (project x)) x.1.2.1 x.1.2.2) hv.1
  change project (opStep e leftSym R rate enc x (some a)) =
    TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
      (TextFeedPipelineInputRun.captured e leftSym R rate enc a (project x)) at he
  refine ⟨v, he.symm ▸ hv, hi, hd, hmono, ?_, ?_⟩
  · exact (congrArg (fun q : Config e leftSym R rate => q.1.1.2.1) he).trans
      (TextFeedPipelineInputRun.run_not_first leftSym R rate _ hf)
  · have hp := congrArg (fun q : Config e leftSym R rate => q.1.1.1) he
    exact fun hh => TextFeedPipelineReentryInput.after_arrival e leftSym R rate hR enc a
      (project x) hz (hp.symm.trans hh)

/-- Startup finishes on the observed schedule within twice the pending
rank, including actual intervening arrivals and without resetting output. -/
theorem entry_finish {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (hR : 0 < R) (enc : Terminal → Fin k)
    {Text : List (Fin k)} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (s n : ℕ) (as : List Terminal) (hs : s ≤ 3) (hlen : s ≤ as.length)
    (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : View e leftSym R rate) (u : Snapshot k)
    (hu : Entry e leftSym R rate Text n (project x) u s) (hfirst : x.1.1.1.2.1 = false) :
    ∃ m pre post y v, m ≤ 2 * s ∧ pre.length ≤ s ∧ as = pre ++ post ∧
      (tick e leftSym R rate enc)^[m] (as, x) = (post, y) ∧
      Entry e leftSym R rate Text (n + pre.length) (project y) v 0 ∧
      v.ideal = u.ideal ∧ v.dir = u.dir ∧ filled u.model ≤ filled v.model ∧
      y.1.1.1.2.1 = false := by
  induction s using Nat.strong_induction_on generalizing n as x u with
  | h s ih =>
    by_cases hs0 : s = 0
    · subst s
      exact ⟨0, [], as, x, u, by omega, by simp, rfl, rfl, hu, rfl, rfl, Nat.le_refl _, hfirst⟩
    · by_cases hz : x.1.1.1.1 = 0
      · cases as with
        | nil => simp only [List.length_nil] at hlen; omega
        | cons a as =>
          have hn' : n < Text.length := by simp only [List.length_cons] at hn; omega
          have ha0 : Text[n]? = some (enc a) := by simpa using ha 0 a rfl
          obtain ⟨v₁, hv₁, hi₁, hd₁, hmono₁, hf₁, hp₁⟩ := entry_arrival hc hmb
            leftSym R rate hR enc a hm hn' x u hu hs hz hfirst ha0
          let x₁ := opStep e leftSym R rate enc x (some a)
          obtain ⟨t, v₂, hts, hv₂, hi₂, hd₂, hmono₂, hf₂⟩ := entry_worker
            (Terminal := Terminal) hc hmb leftSym R rate hb hm (by omega)
            x₁ v₁ hv₁ (by omega) hs hp₁ hf₁
          let x₂ := opStep e leftSym R rate enc x₁ none
          have htail : ∀ j b, as[j]? = some b → Text[(n + 1) + j]? = some (enc b) := by
            intro j b hj
            have hh := ha (j + 1) b (by simpa using hj)
            simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh
          obtain ⟨m, pre, post, y, v, hmc, hpc, hsplit, hrun, hv, hi, hd, hmono, hf⟩ :=
            ih t hts (n + 1) as (by omega) (by simp only [List.length_cons] at hlen; omega)
              (by simp only [List.length_cons] at hn; omega) htail x₂ v₂ hv₂ hf₂
          have htwo : (tick e leftSym R rate enc)^[2] (a :: as, x) = (as, x₂) := by
            rw [Function.iterate_succ_apply', Function.iterate_one]
            simp only [tick, if_pos hz, if_neg hp₁]
            rfl
          refine ⟨m + 2, a :: pre, post, y, v, by omega, ?_, ?_, ?_, ?_,
            hi.trans (hi₂.trans hi₁), hd.trans (hd₂.trans hd₁), hmono₁.trans (hmono₂.trans hmono), hf⟩
          · simp only [List.length_cons]; omega
          · simp only [List.cons_append, hsplit]
          · rw [Function.iterate_add_apply, htwo]
            exact hrun
          · convert hv using 1
            simp only [List.length_cons]
            omega
      · obtain ⟨t, v₁, hts, hv₁, hi₁, hd₁, hmono₁, hf₁⟩ := entry_worker
          (Terminal := Terminal) hc hmb leftSym R rate hb hm (by omega) x u hu (by omega) hs hz hfirst
        let x₁ := opStep e leftSym R rate enc x none
        obtain ⟨m, pre, post, y, v, hmc, hpc, hsplit, hrun, hv, hi, hd, hmono, hf⟩ :=
          ih t hts n as (by omega) (by omega) hn ha x₁ v₁ hv₁ hf₁
        refine ⟨m + 1, pre, post, y, v, by omega, by omega, hsplit, ?_, hv,
          hi.trans hi₁, hd.trans hd₁, hmono₁.trans hmono, hf⟩
        rw [Function.iterate_succ_apply]
        simpa only [tick, if_neg hz] using hrun

/-- The completed observed prefix reaches the first service macro, even
for an empty left pattern. Startup credit is exposed as an explicit bound. -/
theorem prefix_boot {e : Env k} (hcode : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r n : ℕ} (hR : 0 < R)
    (enc : Terminal → Fin k) {leftPat rightPat Text : List (Fin k)}
    (x : View e leftSym R rate)
    (h : Complete e leftSym R rate leftPat rightPat Text rate p r n (project x))
    (hs : SourceSafe e leftSym rate x.1.1.1.2.2) (hz : x.1.1.1.1 ≠ 0)
    (hfirst : x.1.1.1.2.1 = false)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (hdir : (x.2 38).applyAction e.blank (e.mark, .stay) =
      GSVProgZLoop.dirTape e.blank e.mark true 0)
    (as : List Terminal) (hlen : 3 ≤ as.length) (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a)) :
    ∃ m pre post y,
      ∃ a : TextFeedPipelineService.Macro e leftSym R rate Text leftPat rightPat p r
          (n + pre.length) (project y),
      m ≤ 6 ∧ pre.length ≤ 3 ∧ as = pre ++ post ∧
      (tick e leftSym R rate enc)^[m]
        (as, TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x) = (post, y) ∧
      a.z.1.pos = leftPat.length ∧ a.z.1.q = 0 ∧ a.z.2 = ⟨0, 0, 0, true⟩ ∧
      a.events = [] ∧ y.1.1.1.2.1 = false ∧
      ((rate + 1) * (n + 3) ≤ (rate + 1) * leftPat.length + rate * rightPat.length →
        TextFeedPipelineService.target rate rightPat (n + pre.length) ≤ a.score) := by
  obtain ⟨he, u, hv, hf, hfeed, hp, hq, hh, hd⟩ := prefix_snapshot (Terminal := Terminal)
    hcode x h hs hz (by omega)
  let z : GSVerifierZ.VStateZ := (u.model.z.1, ⟨0, 0, 0, true⟩)
  have hg : u.model.z = (z.1, z.2.head) := Prod.ext rfl hh
  have hw : GSVerifierZ.ZWf leftPat.length z.2 := by simp [GSVerifierZ.ZWf, z]
  let x₁ := TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x
  have he₁ : Entry e leftSym R rate Text n (project x₁) u 3 :=
    ⟨hv, by simp only [hf, TextFeedPipelineFrames.next]⟩
  have hf₁ : x₁.1.1.1.2.1 = false :=
    (congrArg (fun t : Config e leftSym R rate => t.1.1.2.1) he).trans
      (TextFeedPipelineInputRun.run_not_first leftSym R rate (project x) hfirst)
  obtain ⟨m, pre, post, y, v, hmc, hpc, hsplit, hrun, hv', hi, hd', _, hyfirst⟩ :=
    entry_finish hcode hmb leftSym R rate hR enc hb hm 3 n as (by omega) hlen hn ha x₁ u he₁ hf₁
  obtain ⟨hvalid, hstart⟩ := TextFeedPipelineReentry.restart hv hfeed hg hw
    (hd.trans hdir) hv'.1 hv'.2 hi hd'
  let v' := TextFeedPipelineMacroBoundary.annotate v z
  let a : TextFeedPipelineService.Macro e leftSym R rate Text leftPat rightPat p r
      (n + pre.length) (project y) :=
    { n₀ := n + pre.length, x₀ := project y, u₀ := v', z := z, u := v'
      events := [], waits := 0, frontier := Nat.le_refl _
      origin := hvalid, start := hstart, valid := hvalid
      follows := .nil _, wait_le := by simp, credit := by simp }
  refine ⟨m, pre, post, y, a, hmc, hpc, hsplit, hrun, hp, hq, rfl, rfl, hyfirst, ?_⟩
  intro hbudget
  apply a.initial_deadline hp hq
  exact (Nat.mul_le_mul_left (rate + 1) (by omega : n + pre.length ≤ n + 3)).trans hbudget

/-- info: 'PalPeg.TextFeedPipelineOutputInitial.prefix_boot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_boot
/-- info: 'PalPeg.TextFeedPipelineOutputInitial.entry_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_finish
/-- info: 'PalPeg.TextFeedPipelineOutputInitial.entry_worker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_worker
/-- info: 'PalPeg.TextFeedPipelineOutputInitial.entry_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_arrival
/-- info: 'PalPeg.TextFeedPipelineOutputInitial.prefix_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_snapshot
/-- info: 'PalPeg.TextFeedPipelineOutputInitial.complete_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complete_arrival
end PalPeg.TextFeedPipelineOutputInitial
