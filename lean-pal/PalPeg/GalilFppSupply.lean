import PalPeg.GalilFppLazyForward

set_option autoImplicit false
namespace PalPeg.GalilFppSupply
open GalilFppInstruction GalilFppCode GalilFppEnqueue GalilFppCache
open GalilFppLazyForward GalilFppDelta GalilFppDeltaTape

theorem aligned_append (s : ℕ → Fin 2) (n : ℕ) (q r : List (Fin 2))
    (hq : Aligned s n q) (hr : Aligned s (n+q.length) r) : Aligned s n (q ++ r) := by
  induction q generalizing n with
  | nil => simpa using hr
  | cons b q ih =>
    refine ⟨hq.1, ih (n+1) hq.2 ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

/-- Each actual BACK push extends the supplied reference prefix by one,
provided its emitted bit is the next reference bit. -/
theorem enqueue_supply (j : Fin 7) (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = entry j) (hs : Supply x s n q) (hb : bit j = s (n+q.length)) :
    Steps code x [entry j,entry j-1] (pushed (bit j) (target j) x) ∧
    Supply (pushed (bit j) (target j) x) s n (q ++ [bit j]) ∧
    n+(q ++ [bit j]).length = n+q.length+1 := by
  obtain ⟨hr, hq, _, ht⟩ := enqueue j x q hp hs.2.1
  refine ⟨hr, ⟨?_, hq, aligned_append s n q [bit j] hs.2.2 ⟨hb, trivial⟩⟩, by simp [Nat.add_assoc]⟩
  unfold CacheAt
  rw [ht]
  exact hs.1

theorem position_mono (f : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) : position f a ≤ position f b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b hab ih =>
    have hh := position_step f b
    omega

/-- A candidate strictly shorter than the processed prefix only scans
already generated deltas, including the final zero delimiter. -/
theorem scan_available (f : ℕ → ℕ) (p N available : ℕ)
    (hp : p < N) (ha : position f N + 1 ≤ available) :
    position f p + 1 + delta f p < available := by
  have hm := position_mono f (show p+1 ≤ N by omega)
  have hs := position_step f p
  omega

variable {α : Type} [DecidableEq α]

/-- All candidates reached by falling back from failure(N) satisfy the
same availability bound. No per-candidate queue-length estimate is needed. -/
theorem failure_scan_available (w : List α) (p N available : ℕ)
    (hN : 0 < N) (hp : p ≤ failure w N)
    (ha : position (failure w) N + 1 ≤ available) :
    position (failure w) p + 1 + delta (failure w) p < available := by
  have hf := failure_le w N
  exact scan_available (failure w) p N available (by omega) ha

/-- The reference stream's delta encoding, independent of how much C has
materialized. This allows an arbitrary cache/FIFO split. -/
def Encoded (s : ℕ → Fin 2) (f : ℕ → ℕ) (N : ℕ) : Prop :=
  (∀ p, p ≤ N → s (position f p) = 0) ∧
  (∀ p, p < N → ∀ k, k < delta f p → s (position f p+1+k) = 1)

/-- Reference stream only: delimiters are zero and every intervening cell
is one. This is not an additional register or oracle in the actual VM. -/
noncomputable def referenceStream (f : ℕ → ℕ) : ℕ → Fin 2 := by
  classical
  exact fun i => if ∃ k, position f k = i then 0 else 1

theorem reference_encoded (f : ℕ → ℕ) (N : ℕ) : Encoded (referenceStream f) f N := by
  classical
  constructor
  · intro p _
    simp [referenceStream, show ∃ k, position f k = position f p from ⟨p, rfl⟩]
  · intro p _ k hk
    have hn : ¬ ∃ j, position f j = position f p+1+k := by
      rintro ⟨j, hj⟩
      by_cases hjp : j ≤ p
      · have hm := position_mono f hjp
        omega
      · have hm := position_mono f (show p+1 ≤ j by omega)
        have hp := position_step f p
        omega
    simp [referenceStream, hn]

/-- Invoke the actual mixed-cache/FIFO scan from a valid KMP candidate.
Availability is derived from the processed prefix, and the resulting S/C
positions are exactly those of the next candidate. -/
theorem scan_candidate (w : List α) (N p : ℕ) (x : Config) (s : ℕ → Fin 2)
    (n : ℕ) (q : List (Fin 2)) (hN : 0 < N) (hp : p ≤ failure w N)
    (hpc : x.pc = 39) (hC : x.pos 2 = position (failure w) p+1)
    (hS : x.pos 3 = p-failure w p) (hh : x.pos 2 ≤ n)
    (ha : position (failure w) N+1 ≤ n+q.length)
    (hs : Supply x s n q) (he : Encoded s (failure w) N)
    (hu : GalilFppForward.FullUnary (x.tape 3) (x.pos 3)) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧
      y.pos 2 = position (failure w) (p+1) ∧ y.pos 3 = p+1-failure w (p+1) ∧
      GalilFppForward.FullUnary (y.tape 3) (y.pos 3) ∧ Supply y s m r ∧
      n ≤ m ∧ m+r.length = n+q.length ∧ y.pos 2 < m ∧
      (∀ t, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ≠ 6 →
        y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  have hfp := failure_le w N
  have hpN : p < N := by omega
  have hav := failure_scan_available w p N (n+q.length) hN hp ha
  have hpos := position_step (failure w) p
  have ho : ∀ k, k < delta (failure w) p → s (x.pos 2+k) = 1 := by
    intro k hk
    rw [hC]
    exact he.2 p hpN k hk
  have hz : s (x.pos 2+delta (failure w) p) = 0 := by
    have hh := he.1 (p+1) (by omega)
    have heq : x.pos 2+delta (failure w) p = position (failure w) (p+1) := by omega
    rw [heq]
    exact hh
  obtain ⟨y, qs, m, r, hr, hypc, hyC, hyS, hyu, hys, hnm, htotal, hlt, hframe⟩ :=
    GalilFppLazyForward.scan (delta (failure w) p) x s n q hpc hh (by omega) hs hu ho hz
  refine ⟨y, qs, m, r, hr, hypc, ?_, ?_, hyu, hys, hnm, htotal, hlt, hframe⟩
  · omega
  · have hfl := failure_le w p
    have hg := failure_grows w p
    unfold delta at hyS
    omega

/-- Matched generation and the complete lazy scan, starting at actual
PC62. Unlike the cached-only matched theorem, C may end during the block. -/
theorem matched_lazy (w : List α) (N p : ℕ) (x : Config) (s : ℕ → Fin 2)
    (n : ℕ) (q : List (Fin 2)) (hN : 0 < N) (hp : p ≤ failure w N)
    (hpc : x.pc = 62) (hC : x.pos 2 = position (failure w) p)
    (hS : x.pos 3 = p-failure w p) (hcell : x.tape 2 (x.pos 2) = 7)
    (ha : position (failure w) N+1 ≤ n+q.length)
    (hs : Supply x s n q) (he : Encoded s (failure w) N)
    (hb : s (n+q.length) = 0)
    (hu : GalilFppForward.FullUnary (x.tape 3) (x.pos 3)) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧
      y.pos 2 = position (failure w) (p+1) ∧ y.pos 3 = p+1-failure w (p+1) ∧
      GalilFppForward.FullUnary (y.tape 3) (y.pos 3) ∧ Supply y s m r ∧
      n ≤ m ∧ m+r.length = n+q.length+1 ∧ y.pos 2 < m ∧
      (∀ t, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ≠ 6 →
        y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  have hinside : x.pos 2 < n := by
    by_contra h
    have hblank := hs.1.2 (x.pos 2) (by omega)
    rw [hcell] at hblank
    contradiction
  let z := pushed 0 60 x
  let u : Config := { z with pc := 39, pos := Function.update z.pos 2 (z.pos 2+1) }
  obtain ⟨hpush, hsz, _⟩ := enqueue_supply 0 x s n q hpc (hs) (by exact hb.symm)
  change Supply z s n (q ++ [0]) at hsz
  have hm : Steps code z [60] u := .step _ _ _ _ [] rfl (.right _ _ _) (.nil _)
  have hsu : Supply u s n (q ++ [0]) := by
    simpa [Supply, CacheAt, GalilFppMaterialize.QueueAt, u] using hsz
  have hcu : u.pos 2 = position (failure w) p+1 := by simp [u, z, pushed, hC]
  have hsuPos : u.pos 3 = p-failure w p := by simpa [u, z, pushed] using hS
  have hhu : u.pos 2 ≤ n := by simp [u, z, pushed]; omega
  have hau : position (failure w) N+1 ≤ n+(q ++ [0]).length := by simp; omega
  have huu : GalilFppForward.FullUnary (u.tape 3) (u.pos 3) := by simpa [u, z, pushed] using hu
  obtain ⟨y, qs, m, r, hr, hypc, hyC, hyS, hyu, hys, hnm, htotal, hlt, hframe⟩ :=
    scan_candidate w N p u s n (q ++ [0]) hN hp rfl hcu hsuPos hhu hau hsu he huu
  refine ⟨y, [62,61,60] ++ qs, m, r, GalilFppCopy.steps_append (GalilFppCopy.steps_append hpush hm) hr,
    hypc, hyC, hyS, hyu, hys, hnm, ?_, hlt, ?_⟩
  · simpa [Nat.add_assoc] using htotal
  · intro t h2 h3 h5 h6
    simpa [u, z, pushed, h2, h5] using hframe t h2 h3 h5 h6

def generatedPosition (f : ℕ → ℕ) (N p : ℕ) : ℕ :=
  position f N+1+(f N-p)

theorem aligned_ones (s : ℕ → Fin 2) (start count : ℕ)
    (hs : ∀ k, k < count → s (start+k) = 1) :
    Aligned s start (List.replicate count 1) := by
  induction count generalizing start with
  | zero => trivial
  | succ count ih =>
    rw [List.replicate_succ]
    refine ⟨?_, ih (start+1) ?_⟩
    · simpa using (hs 0 (by omega)).symm
    · intro k hk
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs (k+1) (by omega)

/-- After a failed candidate p, every distance bit emitted by its fallback
lies inside the current delta block, not across its zero delimiter. -/
theorem fallback_bits (w : List α) (s : ℕ → Fin 2) (N p : ℕ)
    (he : Encoded s (failure w) (N+1)) (hp : p ≤ failure w N)
    (hnext : failure w (N+1) ≤ failure w p+1) :
    Aligned s (generatedPosition (failure w) N p) (List.replicate (p-failure w p) 1) := by
  apply aligned_ones
  intro k hk
  have hf := failure_le w p
  have hd : failure w N-p+k < delta (failure w) N := by unfold delta; omega
  have hh := he.2 N (by omega) (failure w N-p+k) hd
  simpa [generatedPosition, Nat.add_assoc] using hh

/-- On a hit, the already emitted distance equals delta(N), so the next
reference bit is provably the terminating zero. -/
theorem matched_zero (w : List α) (s : ℕ → Fin 2) (N p : ℕ)
    (he : Encoded s (failure w) (N+1)) (hp : p ≤ failure w N)
    (hnext : failure w (N+1) = p+1) :
    s (generatedPosition (failure w) N p) = 0 := by
  have hd : delta (failure w) N = failure w N-p := by unfold delta; omega
  have hpos := position_step (failure w) N
  have hg : generatedPosition (failure w) N p = position (failure w) (N+1) := by
    unfold generatedPosition
    omega
  rw [hg]
  exact he.1 (N+1) (le_refl _)

/-- Lift the proven whole-fallback tape/queue effects to Supply. The
candidate invariant on the next failure length replaces per-bit assumptions. -/
theorem fallback_supply (w : List α) (s : ℕ → Fin 2) (N p n : ℕ)
    (x y : Config) (q : List (Fin 2)) (hs : Supply x s n q)
    (he : Encoded s (failure w) (N+1)) (hp : p ≤ failure w N)
    (hnext : failure w (N+1) ≤ failure w p+1)
    (hgen : n+q.length = generatedPosition (failure w) N p)
    (ht : y.tape 2 = x.tape 2)
    (hq : GalilFppMaterialize.QueueAt y (q ++ List.replicate (p-failure w p) 1)) :
    Supply y s n (q ++ List.replicate (p-failure w p) 1) ∧
      n+(q ++ List.replicate (p-failure w p) 1).length = generatedPosition (failure w) N (failure w p) := by
  refine ⟨⟨?_, hq, aligned_append s n q _ hs.2.2 ?_⟩, ?_⟩
  · unfold CacheAt
    rw [ht]
    exact hs.1
  · rw [hgen]
    exact fallback_bits w s N p he hp hnext
  · have hf := failure_le w p
    simp only [List.length_append, List.length_replicate]
    unfold generatedPosition at hgen ⊢
    omega

/-- On a semantically correct hit, the generated delta block is completed
and the supplied range becomes exactly the next processed input prefix. -/
theorem matched_generated (w : List α) (N p : ℕ) (x : Config) (s : ℕ → Fin 2)
    (n : ℕ) (q : List (Fin 2)) (hN : 0 < N) (hp : p ≤ failure w N)
    (hpc : x.pc = 62) (hC : x.pos 2 = position (failure w) p)
    (hS : x.pos 3 = p-failure w p) (hcell : x.tape 2 (x.pos 2) = 7)
    (hs : Supply x s n q) (he : Encoded s (failure w) (N+1))
    (hgen : n+q.length = generatedPosition (failure w) N p)
    (hnext : failure w (N+1) = p+1)
    (hu : GalilFppForward.FullUnary (x.tape 3) (x.pos 3)) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧
      y.pos 2 = position (failure w) (p+1) ∧ y.pos 3 = p+1-failure w (p+1) ∧
      GalilFppForward.FullUnary (y.tape 3) (y.pos 3) ∧ Supply y s m r ∧
      n ≤ m ∧ m+r.length = position (failure w) (N+1)+1 ∧ y.pos 2 < m ∧
      (∀ t, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ≠ 6 →
        y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  have heN : Encoded s (failure w) N :=
    ⟨fun k hk => he.1 k (by omega), fun k hk => he.2 k (by omega)⟩
  have ha : position (failure w) N+1 ≤ n+q.length := by
    rw [hgen]
    unfold generatedPosition
    omega
  have hb : s (n+q.length) = 0 := by rw [hgen]; exact matched_zero w s N p he hp hnext
  obtain ⟨y, qs, m, r, hr, hypc, hyC, hyS, hyu, hys, hnm, htotal, hlt, hframe⟩ :=
    matched_lazy w N p x s n q hN hp hpc hC hS hcell ha hs heN hb hu
  refine ⟨y, qs, m, r, hr, hypc, hyC, hyS, hyu, hys, hnm, ?_, hlt, hframe⟩
  have hd : delta (failure w) N = failure w N-p := by unfold delta; omega
  have hpos := position_step (failure w) N
  unfold generatedPosition at hgen
  omega

#print axioms matched_generated
#print axioms fallback_supply
#print axioms matched_zero
#print axioms matched_lazy
#print axioms scan_candidate
#print axioms enqueue_supply
#print axioms failure_scan_available
end PalPeg.GalilFppSupply
