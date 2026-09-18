import PalPeg.GalilScaffoldTopFallbackCycle

/-!
# Init and scan runs on the merged frame

The `init` tick and whole scan-mode runs: a `JointRun` on enabled events
(`replicate n true`) from a clock between 1 and `delay` is a run of the
pulled scan frame (counting ticks and matched comparisons), and scan-frame
runs with `replaying = false` transfer to `galilFrame` — no scan-frame tick
leaves scan mode, since its shift and fallback entries are empty.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- The `init` tick. -/
theorem init_tick (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (hm : c.mode = .init) (s : GalilVM) :
    ∃ t : GalilVM, Tick (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay ⟨c, s⟩
        ⟨{c with mode := .scan, output := true}, t⟩ ∧
      t.right = right s.right ∧ t.left = right s.right ∧ t.center = right s.right ∧
      t.length = GalilScaffoldCounter.inc s.length ∧ t.radius = s.radius ∧ t.remaining = s.remaining ∧
      t.replay = s.replay ∧ t.cycle = s.cycle ∧ t.fpp = s.fpp ∧ t.chain = .idle ∧
      t.search = GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset s.radius ∧
      t.lower = GalilScaffoldCounter.reset ∧ t.dp = GalilScaffoldControl.reset entry s.dp := by
  let t : GalilVM := ⟨right s.right, right s.right, right s.right, .idle, s.cycle, s.remaining, s.radius,
    GalilScaffoldCounter.inc s.length, s.replay, s.fpp, GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset s.radius,
    GalilScaffoldControl.reset entry s.dp, GalilScaffoldCounter.reset, s.periodOnly, s.walker⟩
  exact ⟨t, .init c s t hm ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Scan-frame ticks from scan mode stay in scan mode and keep
`replaying = false`. -/
theorem scan_tick_stays (f g : ScanVM → Prop) (delay : ℕ) {c c' : Control} {s t : GalilVM}
    (hm : c.mode = .scan) (hr : c.replaying = false)
    (h : Tick (Frame.pull scanLens (scanFrame f g)) delay ⟨c, s⟩ ⟨c', t⟩) :
    c'.mode = .scan ∧ c'.replaying = false := by
  cases h <;> try wrong_mode
  case scan_wait => exact ⟨hm, hr⟩
  case scan_count => exact ⟨hm, hr⟩
  case scan_match => exact ⟨hm, by simp [hr]⟩
  case scan_shift =>
    exact ((‹(Frame.pull scanLens (scanFrame f g)).shiftGuard _›) : False).elim
  case scan_fallback =>
    exact ((‹(Frame.pull scanLens (scanFrame f g)).beginFallback _ _›) : (False ∧ _)).1.elim
  case restart =>
    exact ((‹(Frame.pull scanLens (scanFrame f g)).restart _ _›) : (False ∧ _)).1.elim

theorem scan_frame_reparam (P : Shared) (s : GalilVM) (v0 : ScanVM) :
    scanFrame (fun v => P.onLetter (scanLens.set (scanLens.set s v0) v))
        (fun v => P.leftFirst (scanLens.set (scanLens.set s v0) v)) =
      scanFrame (fun v => P.onLetter (scanLens.set s v)) (fun v => P.leftFirst (scanLens.set s v)) := by
  simp only [scanLens.set_set]

/-- Scan-mode runs of the pulled scan frame transfer to `galilFrame`. -/
theorem steps_transfer_scan (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ) :
    ∀ {c c' : Control} {s0 s t : GalilVM} {v0 : ScanVM}, s = scanLens.set s0 v0 →
      c.mode = .scan → c.replaying = false →
      Steps (Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s0 v))
        (fun v => P.leftFirst (scanLens.set s0 v)))) delay n ⟨c, s⟩ ⟨c', t⟩ →
      Steps (galilFrame P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ c'.mode = .scan ∧ c'.replaying = false := by
  induction n with
  | zero =>
    intro c c' s0 s t v0 _ hm hr h
    cases h
    exact ⟨.zero _, hm, hr⟩
  | succ n ih =>
    intro c c' s0 s t v0 hs hm hr h
    cases h with
    | succ ht hr' =>
      rename_i y
      obtain ⟨c1, s1⟩ := y
      have hfr : (fun v => P.onLetter (scanLens.set s0 v)) = (fun v => P.onLetter (scanLens.set s v)) := by
        subst hs; funext v; rw [scanLens.set_set]
      have hfr' : (fun v => P.leftFirst (scanLens.set s0 v)) = (fun v => P.leftFirst (scanLens.set s v)) := by
        subst hs; funext v; rw [scanLens.set_set]
      have ht' := ht
      rw [hfr, hfr'] at ht'
      have hg := scan_transfer P q first delay hm hr ht'
      obtain ⟨hm1, hr1⟩ := scan_tick_stays _ _ delay hm hr ht
      obtain ⟨v1, hv1⟩ := tick_pull_shape scanLens _ delay ht
      have hs1 : s1 = scanLens.set s0 (scanLens.get s1) := by
        rw [hv1, hs, scanLens.set_set, scanLens.get_set]
      obtain ⟨hg', hm', hr''⟩ := ih hs1 hm1 hr1 hr'
      exact ⟨.succ hg hg', hm', hr''⟩

#print axioms init_tick
#print axioms steps_transfer_scan

end PalPeg.GalilScaffoldChainInputSupply
