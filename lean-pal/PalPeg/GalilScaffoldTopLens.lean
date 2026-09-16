import PalPeg.GalilScaffoldTopShift

/-!
# Pulling a controller frame back along a lens

Each mode's VM effects were instantiated on its own component state
(`ScanVM`, `ShiftVM`, `FppControl.State`, `RewindVM`). The whole machine has
one VM containing all components. A `Lens σ σ'` (get/set with the usual
laws) pulls a `Frame σ'` back to a `Frame σ`: every relation holds on the
projections and the rest of `σ` is untouched. Ticks and `Steps` of the
component frame lift to the pulled-back frame, so the per-mode phase
theorems compose on the unified VM.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldTop
open GalilScaffoldController

structure Lens (σ σ' : Type) where
  get : σ → σ'
  set : σ → σ' → σ
  get_set : ∀ s v, get (set s v) = v
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s v w, set (set s v) w = set s w

variable {σ σ' : Type}

def Lens.rel (L : Lens σ σ') (R : σ' → σ' → Prop) : σ → σ → Prop :=
  fun s t => R (L.get s) (L.get t) ∧ t = L.set s (L.get t)

def Frame.pull (L : Lens σ σ') (F : Frame σ') : Frame σ where
  init := L.rel F.init
  available := fun s => F.available (L.get s)
  background := L.rel F.background
  compare := L.rel F.compare
  matched := fun s => F.matched (L.get s)
  shiftGuard := fun s => F.shiftGuard (L.get s)
  matchedPlace := fun b s t => F.matchedPlace b (L.get s) (L.get t) ∧ t = L.set s (L.get t)
  replayExhausted := fun s => F.replayExhausted (L.get s)
  onLetter := fun s => F.onLetter (L.get s)
  leftFirst := fun s => F.leftFirst (L.get s)
  beginShift := L.rel F.beginShift
  beginFallback := L.rel F.beginFallback
  remainingPos := fun s => F.remainingPos (L.get s)
  shiftOne := L.rel F.shiftOne
  copyOne := L.rel F.copyOne
  copyEnd := L.rel F.copyEnd
  atLeft := fun s => F.atLeft (L.get s)
  fppStart := L.rel F.fppStart
  homeStep := L.rel F.homeStep
  fppSlice := L.rel F.fppSlice
  fppDone := L.rel F.fppDone
  atEnd := fun s => F.atEnd (L.get s)
  markBack := L.rel F.markBack
  markForward := L.rel F.markForward
  markSet := fun s => F.markSet (L.get s)
  choose := L.rel F.choose
  atFirst := fun s => F.atFirst (L.get s)
  fppReset := L.rel F.fppReset
  rewindOne := L.rel F.rewindOne
  rewindPair := L.rel F.rewindPair
  replayStart := L.rel F.replayStart
  replayPos := fun s => F.replayPos (L.get s)
  restart := L.rel F.restart

theorem Lens.rel_set (L : Lens σ σ') (R : σ' → σ' → Prop) (s : σ) (v : σ') (h : R (L.get s) v) :
    L.rel R s (L.set s v) := by
  refine ⟨?_, ?_⟩ <;> rw [L.get_set]
  · exact h

theorem Lens.rel_set' (L : Lens σ σ') (R : σ' → σ' → Prop) (s : σ) (v w : σ') (h : R v w) :
    L.rel R (L.set s v) (L.set s w) := by
  refine ⟨?_, ?_⟩
  · rw [L.get_set, L.get_set]; exact h
  · rw [L.get_set, L.set_set]

theorem Lens.un (L : Lens σ σ') (P : σ' → Prop) (s : σ) (v : σ') (h : P v) : P (L.get (L.set s v)) := by
  rw [L.get_set]; exact h

theorem Lens.unb (L : Lens σ σ') (P : σ' → Bool) (s : σ) (v : σ') : P (L.get (L.set s v)) = P v := by
  rw [L.get_set]

theorem refresh_pull (L : Lens σ σ') (F : Frame σ') (s : σ) (v : σ') (old o : Bool)
    (h : refresh F v old o) : refresh (Frame.pull L F) (L.set s v) old o := by
  simp only [refresh, Frame.pull, L.get_set] at h ⊢
  exact h

theorem pull_scan_match (L : Lens σ σ') (F : Frame σ') (delay : ℕ) (c : Control) (s : σ)
    (s1 v : σ') (o : Bool) (hm : c.mode = .scan) (hav : c.replaying = true ∨ F.available (L.get s))
    (hc : c.clock = 1) (hcmp : F.compare (L.get s) s1) (hmt : F.matched s1)
    (hpl : F.matchedPlace c.replaying s1 v) (ho : refresh F v c.output o) :
    Tick (Frame.pull L F) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := c.replaying && !F.replayExhausted v}, L.set s v⟩ := by
  have ht := Tick.scan_match (F := Frame.pull L F) (delay := delay) c s (L.set s s1) (L.set s v) o hm hav hc
    (L.rel_set _ _ _ hcmp) (L.un _ _ _ hmt) (L.rel_set' _ _ _ _ hpl) (refresh_pull L F s v c.output o ho)
  have e : (Frame.pull L F).replayExhausted (L.set s v) = F.replayExhausted v := by
    simp [Frame.pull, L.get_set]
  rw [e] at ht
  exact ht

theorem pull_scan_shift (L : Lens σ σ') (F : Frame σ') (delay : ℕ) (c : Control) (s : σ)
    (s1 v : σ') (hm : c.mode = .scan) (hav : c.replaying = true ∨ F.available (L.get s))
    (hc : c.clock = 1) (hcmp : F.compare (L.get s) s1) (hmt : ¬ F.matched s1) (hr : c.replaying = false)
    (hg : F.shiftGuard s1) (hb : F.beginShift s1 v) :
    Tick (Frame.pull L F) delay ⟨c, s⟩ ⟨{c with clock := delay, mode := .shift}, L.set s v⟩ :=
  .scan_shift c s (L.set s s1) (L.set s v) hm hav hc (L.rel_set _ _ _ hcmp)
    (fun h => hmt (by
      have h' : F.matched (L.get (L.set s s1)) := h
      rw [L.get_set] at h'; exact h')) hr (L.un _ _ _ hg) (L.rel_set' _ _ _ _ hb)

theorem pull_scan_fallback (L : Lens σ σ') (F : Frame σ') (delay : ℕ) (c : Control) (s : σ)
    (s1 v : σ') (hm : c.mode = .scan) (hav : c.replaying = true ∨ F.available (L.get s))
    (hc : c.clock = 1) (hcmp : F.compare (L.get s) s1) (hmt : ¬ F.matched s1)
    (hg : c.replaying = true ∨ ¬ F.shiftGuard s1) (hr : c.replaying = false) (hb : F.beginFallback s1 v) :
    Tick (Frame.pull L F) delay ⟨c, s⟩ ⟨{c with clock := delay, mode := .copy}, L.set s v⟩ := by
  refine .scan_fallback c s (L.set s s1) (L.set s v) hm hav hc (L.rel_set _ _ _ hcmp)
    (fun h => hmt (by
      have h' : F.matched (L.get (L.set s s1)) := h
      rw [L.get_set] at h'; exact h')) ?_ hr (L.rel_set' _ _ _ _ hb)
  rcases hg with hg | hg
  · exact Or.inl hg
  · right; intro h; apply hg
    have h' : F.shiftGuard (L.get (L.set s s1)) := h
    rw [L.get_set] at h'; exact h'

theorem pull_replayStart (L : Lens σ σ') (F : Frame σ') (delay : ℕ) (c : Control) (s : σ)
    (v : σ') (o : Bool) (hm : c.mode = .replayStart) (h1 : F.replayStart (L.get s) v)
    (ho : F.replayPos v = true → o = c.output) (ho' : F.replayPos v = false → refresh F v c.output o) :
    Tick (Frame.pull L F) delay ⟨c, s⟩
      ⟨{c with mode := .scan, clock := delay, output := o, replaying := F.replayPos v}, L.set s v⟩ := by
  have e : (Frame.pull L F).replayPos (L.set s v) = F.replayPos v := by
    simp [Frame.pull, L.get_set]
  have ht := Tick.replayStart (F := Frame.pull L F) (delay := delay) c s (L.set s v) o hm
    (L.rel_set _ _ _ h1) (by rw [e]; exact ho)
    (by rw [e]; intro h; exact refresh_pull L F s v c.output o (ho' h))
  rw [e] at ht
  exact ht

theorem pull_shift_done (L : Lens σ σ') (F : Frame σ') (delay : ℕ) (c : Control) (s : σ)
    (o : Bool) (hm : c.mode = .shift) (hp : ¬ F.remainingPos (L.get s))
    (ho : refresh F (L.get s) c.output o) :
    Tick (Frame.pull L F) delay ⟨c, s⟩ ⟨{c with mode := .scan, output := o}, L.set s (L.get s)⟩ := by
  rw [L.set_get]
  exact Tick.shift_done c s o hm hp
    (by rw [← L.set_get s]; exact refresh_pull L F s (L.get s) c.output o ho)

/-- A tick of the component frame on the projection is a tick of the pulled
frame on the whole VM, with the same controller records. -/
theorem tick_pull (L : Lens σ σ') (F : Frame σ') (delay : ℕ) (c c' : Control) (s : σ) (v : σ')
    (h : Tick F delay ⟨c, L.get s⟩ ⟨c', v⟩) :
    Tick (Frame.pull L F) delay ⟨c, s⟩ ⟨c', L.set s v⟩ := by
  cases h
  case init =>
    rename_i hm hi
    exact .init c s (L.set s v) hm (L.rel_set _ _ _ hi)
  case scan_wait =>
    rename_i hm hav hb
    exact .scan_wait c s (L.set s v) hm hav (L.rel_set _ _ _ hb)
  case scan_count =>
    exact .scan_count c s (L.set s v) ‹_› ‹_› ‹_› (L.rel_set _ _ _ ‹_›)
  case scan_match =>
    exact pull_scan_match L F delay c s _ v _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case scan_shift =>
    exact pull_scan_shift L F delay c s _ v ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case scan_fallback =>
    exact pull_scan_fallback L F delay c s _ v ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case shift_one =>
    rename_i hm hp h1
    exact .shift_one c s (L.set s v) hm hp (L.rel_set _ _ _ h1)
  case shift_done =>
    exact pull_shift_done L F delay c s _ ‹_› ‹_› ‹_›
  case copy_one =>
    rename_i hm hp h1
    exact .copy_one c s (L.set s v) hm hp (L.rel_set _ _ _ h1)
  case copy_done =>
    rename_i hm hp h1
    exact .copy_done c s (L.set s v) hm hp (L.rel_set _ _ _ h1)
  case home_start =>
    rename_i hm hl h1
    exact .home_start c s (L.set s v) hm hl (L.rel_set _ _ _ h1)
  case home_step =>
    rename_i hm hl h1
    exact .home_step c s (L.set s v) hm hl (L.rel_set _ _ _ h1)
  case fpp_slice =>
    rename_i hm h1
    exact .fpp_slice c s (L.set s v) hm (L.rel_set _ _ _ h1)
  case fpp_done =>
    rename_i hm h1
    exact .fpp_done c s (L.set s v) hm (L.rel_set _ _ _ h1)
  case markEnd_found =>
    rename_i hm he h1
    exact .markEnd_found c s (L.set s v) hm he (L.rel_set _ _ _ h1)
  case markEnd_step =>
    rename_i hm he h1
    exact .markEnd_step c s (L.set s v) hm he (L.rel_set _ _ _ h1)
  case choose_select =>
    rename_i hm ho hs h1
    exact .choose_select c s (L.set s v) hm ho hs (L.rel_set _ _ _ h1)
  case choose_step =>
    rename_i hm hs h1
    exact .choose_step c s (L.set s v) hm hs (L.rel_set _ _ _ h1)
  case rewind_done =>
    rename_i hm hf h1
    exact .rewind_done c s (L.set s v) hm hf (L.rel_set _ _ _ h1)
  case rewind_one =>
    exact .rewind_one c s (L.set s v) ‹_› ‹_› ‹_› (L.rel_set _ _ _ ‹_›)
  case rewind_pair =>
    exact .rewind_pair c s (L.set s v) ‹_› ‹_› ‹_› (L.rel_set _ _ _ ‹_›)
  case replayStart =>
    exact pull_replayStart L F delay c s v _ ‹_› ‹_› ‹_› ‹_›

  case restart =>
    exact .restart c s (L.set s v) ‹_› (L.rel_set _ _ _ ‹_›)

#print axioms tick_pull

/-- `Steps` of the component frame lift likewise. -/
theorem steps_pull (L : Lens σ σ') (F : Frame σ') (delay : ℕ) (n : ℕ) :
    ∀ (c c' : Control) (s : σ) (v : σ'),
      GalilScaffoldChainInputSupply.Steps F delay n ⟨c, L.get s⟩ ⟨c', v⟩ →
      GalilScaffoldChainInputSupply.Steps (Frame.pull L F) delay n ⟨c, s⟩ ⟨c', L.set s v⟩ := by
  induction n with
  | zero =>
    intro c c' s v h
    cases h
    rw [L.set_get]
    exact .zero _
  | succ n ih =>
    intro c c' s v h
    cases h with
    | succ ht hr =>
      rename_i y
      have ht' := tick_pull L F delay c y.ctl s y.vm ht
      have hr' := ih y.ctl c' (L.set s y.vm) v (by rw [L.get_set]; exact hr)
      rw [L.set_set] at hr'
      exact .succ ht' hr'

#print axioms steps_pull

end PalPeg.GalilScaffoldTop
