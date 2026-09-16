import PalPeg.GalilScaffoldTopRoundsCounters

/-!
# From a restarted state to the next found state

`Restarted P raw r Rad last`: the facts about the state right after a
restart tick (chain idle, the search started at `begin last radius`, the
scan invariant with radius `Rad`, canonical counters, the represented
centre). A chain-idle segment from it followed by a matched comparison whose
search lands in `found` yields the static premises of `found_life` at the
state before that comparison (`FoundReady`), together with the DP result and
the run mode — or the first stage halted earlier without `found`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The decoding of the centre by the shared parameters: they read the
centre symbol and place off the centre head. -/
def Decodes (P : Shared) : Prop :=
  (∀ (u : GalilVM) (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool),
    u.center = represent ⟨a :: ls,gap⟩ (rs.map some) q →
    GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some (P.centre u) ∧ P.place u = ⟨a :: ls,gap⟩) ∧
  (∀ u v : GalilVM, u.center = v.center → P.place u = P.place v)

/-- The static premises of `found_life` at a state. -/
def FoundReady (P : Shared) (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  ∃ (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (R : ℕ),
    s.center = represent ⟨a :: ls,gap⟩ (rs.map some) q ∧ raw = (a :: ls).reverse ++ (rs ++ q) ∧
    ScanInvariant raw (position s.center) R s.left s.right ∧
    value s.radius = R ∧ Canonical s.radius ∧ Canonical s.length ∧ 0 < R ∧
    GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some (P.centre s) ∧ P.place s = ⟨a :: ls,gap⟩

/-- The state right after a restart. -/
def Restarted (raw : List (Fin 2)) (r : GalilVM) (Rad : ℕ) (last : Counter) : Prop :=
  r.chain = .idle ∧
  GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none ∧
  ScanInvariant raw (position r.center) Rad r.left r.right ∧
  RadiusRep r.radius Rad ∧ Canonical r.length ∧
  r.search = GalilScaffoldSearchFinish.begin last r.radius ∧ r.lower = last ∧
  Canonical last ∧ 0 ≤ value last

/-- A chain-idle segment from a restarted state, then a matched comparison
whose search lands in `found`: the next found state. -/
theorem restarted_next_found (P : Shared) (qq : ℕ) (first : Fin 9) (hP : Decodes P)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last)
    {c0 : Control} (hcl : c0.clock = 2048)
    (hstage : ∀ k : ℕ, value last = k → 3 * Rad ≤ 5 * k)
    {es1 : List Bool} {c1 : Control} {s1 : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r c1 s1) (hs1 : s1.chain = .idle)
    (hpos : 0 < Rad + es1.count true)
    (hc1 : c1.clock = 1) (vq : SearchVM) (hq : searchEffect P true s1 vq)
    (hfound : vq.search.mode = .found) :
    FoundReady P raw s1 ∧
    ((s1.search.mode = .run ∧
      ∃ (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (k : ℕ),
        s1.center = represent ⟨a :: ls,gap⟩ (rs.map some) q ∧ value last = k ∧
        (∃ dpv, vq.dp = ⟨dpv, true⟩ ∧
          GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k 0
            (GalilScaffoldProgram.denote dpv)) ∧
        (∀ (rad' : Counter), Canonical rad' → ∀ (r0 : ℕ), value rad' = r0 → 0 < r0 → ∀ (sm dm : Bool),
          ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
            GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k h ∧
            ys.length+1 = h)) ∨
     (∃ (L : ℕ) (vL : SearchVM), L ≤ es1.length ∧
        SearchRun (P.place r) (es1.take L) (searchLens.get r) vL ∧
        vL.search.mode ≠ .run ∧ vL.search.mode ≠ .found)) := by
  obtain ⟨hidle, hrep, hfoc, hscan, ⟨hrc, hrv⟩, hlc, hsearch, hlower, hlast, hlv⟩ := hR
  obtain ⟨a, ls, rs, q, hcen, hraw⟩ := represents_decompose r.center raw hrep hfoc
  obtain ⟨hreadr, hplr⟩ := hP.1 r a ls rs q r.center.gap hcen
  have hplace := hP.2
  -- the lower bound's value
  obtain ⟨k, hk⟩ : ∃ k : ℕ, value last = k := ⟨(value last).toNat, (Int.toNat_of_nonneg hlv).symm⟩
  obtain ⟨c, hc⟩ := place_read_some a ls r.center.gap
  -- the heads and counters along the segment
  obtain ⟨hsc, _, hrad1, hrc1, hlc1⟩ := watchSegE_heads P qq first 2048 hseg
  have hcen1 : s1.center = r.center := watchSegE_center P qq first 2048 hseg
  have hraw' : raw = (a :: ls).reverse ++ (rs ++ q) := by rw [hraw, List.append_assoc]
  have hinv1 : ScanInvariant raw (position s1.center) (Rad + es1.count true) s1.left s1.right := by
    rw [hcen1]
    exact scan_events_invariant (hsc raw (position r.center) Rad) hscan
  have hrad1' : value s1.radius = ((Rad + es1.count true : ℕ) : ℤ) := by
    rw [hrad1, hrv]; push_cast; ring
  obtain ⟨hread1, hpl1⟩ := hP.1 s1 a ls rs q r.center.gap (by rw [hcen1]; exact hcen)
  have hready : FoundReady P raw s1 :=
    ⟨a, ls, rs, q, r.center.gap, Rad + es1.count true, by rw [hcen1]; exact hcen, hraw', hinv1, hrad1',
      hrc1 hrc, hlc1 hlc, hpos, hread1, hpl1⟩
  refine ⟨hready, ?_⟩
  -- the search
  have hstep : searchStep (P.place s1) true (searchLens.get s1) vq := by
    rcases hq with ⟨_, hstep⟩ | ⟨hne, _⟩
    · exact hstep
    · exact absurd hs1 hne
  rcases idle_segment_found_first P qq first hplace a ls rs q r.center.gap hcl hplr hcen c hc last r.radius
      hlast k hk hrc Rad hrv (hstage k hk) hsearch hlower hseg hs1 true (fun _ => hc1) vq hstep hfound
    with ⟨⟨dpv, hdp, hres⟩, hrun, hcand⟩ | ⟨L, vL, hL, hrunL, hnr, hnf⟩
  · left
    exact ⟨hrun, a, ls, rs, q, r.center.gap, k, by rw [hcen1]; exact hcen, hk, ⟨dpv, hdp, hres⟩, hcand⟩
  · right
    refine ⟨L, vL, hL, ?_, hnr, hnf⟩
    rw [hplr]; exact hrunL

#print axioms restarted_next_found

end PalPeg.GalilScaffoldChainInputSupply
