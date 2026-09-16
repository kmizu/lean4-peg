import PalPeg.GalilScaffoldTopReplay

/-!
# Scan-mode ticks on the merged frame

The scan frame pulled along `scanLens` supplies `available`/`background`/
`compare`/`matched`/`matchedPlace`; its shift and fallback entries are empty,
so only `scan_wait`/`scan_count`/`scan_match` transfer. The output refresh
uses the shared `onLetter`/`leftFirst`, and `replaying = false` makes the
replay flag update trivial.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

theorem scan_match_merge (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s s1 t : GalilVM) (o : Bool) (hm : c.mode = .scan) (hr : c.replaying = false)
    (hav : c.replaying = true ∨ (Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))).available s)
    (hc : c.clock = 1)
    (hcmp : (Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))).compare s s1)
    (hmt : (Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))).matched s1)
    (hpl : (Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))).matchedPlace c.replaying s1 t)
    (ho : refresh (Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))) t c.output o) :
    Tick (galilFrame P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := c.replaying && !P.replayExhausted t}, t⟩ := by
  have hts : t = scanLens.set s (scanLens.get t) := by
    obtain ⟨_, hs1⟩ := hcmp
    obtain ⟨_, ht⟩ := hpl
    conv_lhs => rw [ht]
    rw [hs1, scanLens.set_set]
  have ho' : refresh (galilFrame P q first) t c.output o := by
    simp only [refresh, Frame.pull, galilFrame, scanFrame] at ho ⊢
    rw [← hts] at ho
    exact ho
  have hts1 : t = s1 := by
    obtain ⟨h1, ht⟩ := hpl
    have h1' : scanLens.get t = scanLens.get s1 := h1
    rw [ht, h1', scanLens.set_get]
  have hpl' : (galilFrame P q first).matchedPlace c.replaying s1 t := by
    show t = (if c.replaying then _ else s1)
    rw [hr]; simp [hts1]
  exact Tick.scan_match c s s1 t o hm hav hc hcmp hmt hpl' ho'

theorem scan_transfer (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .scan) (hr : c.replaying = false)
    (h : Tick (Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))) delay ⟨c, s⟩ ⟨c', t⟩) :
    Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩ := by
  cases h <;> try wrong_mode
  case scan_wait =>
    exact .scan_wait c s t ‹_› ‹_› ‹_›
  case scan_count =>
    exact .scan_count c s t ‹_› ‹_› ‹_› ‹_›
  case scan_match =>
    have ht := scan_match_merge P q first delay c s _ t _ hm hr ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    rw [hr] at ht ⊢
    simpa using ht
  case scan_shift =>
    exact (‹(Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))).shiftGuard _› : False).elim
  case scan_fallback =>
    exact (‹(Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))).beginFallback _ _› : (False ∧ _)).1.elim
  case restart =>
    exact (‹(Frame.pull scanLens (scanFrame (fun v => P.onLetter (scanLens.set s v))
      (fun v => P.leftFirst (scanLens.set s v)))).restart _ _› : (False ∧ _)).1.elim

#print axioms scan_transfer

end PalPeg.GalilScaffoldChainInputSupply
