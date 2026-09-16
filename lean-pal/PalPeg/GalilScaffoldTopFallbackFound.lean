import PalPeg.GalilScaffoldTopFallbackRestart

/-!
# From a mismatch with the chain idle to the next found state

`fallback_restarted` followed by `restarted_next_found`: after the fallback
cycle the controller is in a restarted state (radius `0`, lower bound `0`),
and a chain-idle segment (the replay and the following scan, with the
search running) ending in a found comparison re-establishes `FoundReady`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem fallback_next_found (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (hP : Decodes (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry))
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hi : ShiftIdle s) (hav : canRight s.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false s vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre s) (place s)
      s.center s.radius s.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq))
    {raw : List (Fin 2)} (hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw)
    (hfoc : (right s.right).head.focus ≠ none)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (n : ℕ) (o : Bool) (t : GalilVM),
        Steps (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first)
          2048 (1 + (n+1)) ⟨c, s⟩
          ⟨{c with mode := .scan, clock := 2048, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}, t⟩ ∧
        t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        ∀ {es1 : List Bool} {c1 : Control} {s1 : GalilVM},
          WatchSegE (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first 2048 es1
            {c with mode := .scan, clock := 2048, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}
            t c1 s1 →
          s1.chain = .idle → 0 < es1.count true → c1.clock = 1 →
          ∀ (vq' : SearchVM),
            searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) true s1 vq' →
            vq'.search.mode = .found →
          FoundReady (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) raw s1 ∧
          ((s1.search.mode = .run ∧
            ∃ (a' : Fin 2) (ls' rs'' q'' : List (Fin 2)) (gap' : Bool) (k : ℕ),
              s1.center = represent ⟨a' :: ls',gap'⟩ (rs''.map some) q'' ∧ value (reset : Counter) = k ∧
              (∃ dpv, vq'.dp = ⟨dpv, true⟩ ∧
                GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a' :: ls',gap'⟩).take (8*max k 1+1)) k 0
                  (GalilScaffoldProgram.denote dpv)) ∧
              (∀ (rad' : Counter), Canonical rad' → ∀ (r0 : ℕ), value rad' = r0 → 0 < r0 → ∀ (sm dm : Bool),
                ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
                  GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a' :: ls',gap'⟩).take (8*max k 1+1)) k h ∧
                  ys.length+1 = h)) ∨
           (∃ (L : ℕ) (vL : SearchVM), L ≤ es1.length ∧
              SearchRun ((galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry).place t)
                (es1.take L) (searchLens.get t) vL ∧
              vL.search.mode ≠ .run ∧ vL.search.mode ≠ .found)) := by
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hst, hRst, hrep', _, _, _, _⟩ :=
    fallback_restarted onLetter leftFirst rs centre place entry q hq0 first h7 h8 2048 c hm hr hc s hi hav
      vs vq hl hrr hmis hq hch hg hrep hfoc hcan ℓ hv heven
  refine ⟨a, xs, rs', q', hdec, hraw, n, o, t, hst, hrep', ?_⟩
  intro es1 c1 s1 hseg hs1 hpos hc1 vq' hq' hfound
  exact restarted_next_found _ q first hP hRst rfl (fun k _ => by omega) hseg hs1 (by simpa using hpos)
    hc1 vq' hq' hfound

#print axioms fallback_next_found

end PalPeg.GalilScaffoldChainInputSupply
