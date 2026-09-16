import PalPeg.GalilScaffoldTopIdleFound

/-!
# The centre across the rounds

The centre head after the re-shift rounds is represented (`Entry` carries
`Represents`) and sits at the origin's centre advanced by the rounds' half
periods; the final matched segment and the breaking comparison keep it. A
represented head with a real symbol decomposes as `represent ⟨a :: ls,gap⟩`,
the form the search-stage lemmas read the window from.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- A represented head on a real symbol is a `represent` of a nonempty place. -/
theorem represents_decompose (p : PlaceHead) (raw : List (Fin 2))
    (h : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none) :
    ∃ (a : Fin 2) (ls rs q : List (Fin 2)),
      p = represent ⟨a :: ls, p.gap⟩ (rs.map some) q ∧ raw = (a :: ls).reverse ++ rs ++ q := by
  obtain ⟨xs, rs, q, hh, hw⟩ := h
  cases xs with
  | nil =>
    exfalso
    apply hp
    rw [hh]; rfl
  | cons a ls =>
    refine ⟨a, ls, rs, q, ?_, hw⟩
    rcases p with ⟨head, gap⟩
    simp only at hh
    rw [hh]; rfl

theorem place_read_some (a : Fin 2) (ls : List (Fin 2)) (gap : Bool) :
    ∃ c : Fin 3, GalilScaffoldPlace.read ⟨a :: ls, gap⟩ = some c :=
  ⟨_, rfl⟩

/-- A scan segment keeps the centre. -/
theorem scanSeg_center (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    t.center = s.center := by
  induction h with
  | stop c s => rfl
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨_, _, hcen, _⟩ := background_frame P q first hb
    rw [ih, hcen]
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨_, _, hcen, _⟩ := background_frame P q first hb
    rw [ih, hcen]
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ _ ih =>
    rw [ih, afterCompare_center]

/-- After `m` rounds from an `Entry`, the centre head is represented, on a
real symbol, at the origin's centre advanced by `m` half periods. -/
theorem rounds_centerRep (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ) {m : ℕ}
    {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s')
    (w0 : GalilScaffoldChainWatch.State) (hp0 : s.periodOnly = true) (hs0 : s.chain = .watch w0)
    (hz0 : zero w0.lag = true) {raw : List (Fin 2)} (org : ReadOrigin raw)
    (hint : org.interior.length+1 = h) (he : Entry raw org (toOnly s w0)) :
    GalilScaffoldInputTrace.Represents s'.center.head raw ∧ s'.center.head.focus ≠ none ∧
      position s'.center = org.center + m*h + h := by
  obtain ⟨_, w', _, _, _, hcr⟩ := rounds_lift P q first delay h hr w0 hp0 hs0 hz0
  obtain ⟨o', he', _, hinterior, _, _, _, hcenter', _⟩ := rounds_origin hcr org hint he
  refine ⟨he'.centerRep, he'.centerPresent, ?_⟩
  have := he'.centerPos
  rw [hinterior, hint, hcenter'] at this
  exact this

#print axioms represents_decompose
#print axioms rounds_centerRep

end PalPeg.GalilScaffoldChainInputSupply
