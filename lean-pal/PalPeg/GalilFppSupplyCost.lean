import PalPeg.GalilFppReadCost
import PalPeg.GalilFppSupply

set_option autoImplicit false
namespace PalPeg.GalilFppSupplyCost
open GalilFppInstruction GalilFppCode GalilFppEnqueue GalilFppCache
open GalilFppLazyForward GalilFppDelta GalilFppDeltaTape GalilFppSupply
variable {α : Type} [DecidableEq α]

theorem scan_candidate_cost (w : List α) (N p : ℕ) (x : Config) (s : ℕ → Fin 2)
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
      (∀ t, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      qs.length + 5*y.pos 5 ≤ 11*delta (failure w) p+8+5*x.pos 5 := by
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
  obtain ⟨y,qs,m,r,hr,hypc,hyC,hyS,hyu,hys,hnm,htotal,hlt,hframe,hcost⟩ :=
    GalilFppReadCost.scan_cost (delta (failure w) p) x s n q hpc hh (by omega) hs hu ho hz
  refine ⟨y,qs,m,r,hr,hypc,?_,?_,hyu,hys,hnm,htotal,hlt,hframe,hcost⟩
  · omega
  · have hfl := failure_le w p
    have hg := failure_grows w p
    unfold delta at hyS
    omega

theorem matched_lazy_cost (w : List α) (N p : ℕ) (x : Config) (s : ℕ → Fin 2)
    (n : ℕ) (q : List (Fin 2)) (hN : 0 < N) (hp : p ≤ failure w N)
    (hpc : x.pc = 62) (hC : x.pos 2 = position (failure w) p)
    (hS : x.pos 3 = p-failure w p) (hcell : x.tape 2 (x.pos 2) = 7)
    (ha : position (failure w) N+1 ≤ n+q.length)
    (hs : Supply x s n q) (he : Encoded s (failure w) N) (hb : s (n+q.length) = 0)
    (hu : GalilFppForward.FullUnary (x.tape 3) (x.pos 3)) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧
      y.pos 2 = position (failure w) (p+1) ∧ y.pos 3 = p+1-failure w (p+1) ∧
      GalilFppForward.FullUnary (y.tape 3) (y.pos 3) ∧ Supply y s m r ∧
      n ≤ m ∧ m+r.length = n+q.length+1 ∧ y.pos 2 < m ∧
      (∀ t, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      qs.length + 5*y.pos 5 ≤ 11*delta (failure w) p+16+5*x.pos 5 := by
  have hinside : x.pos 2 < n := by
    by_contra h
    have hblank := hs.1.2 (x.pos 2) (by omega)
    rw [hcell] at hblank
    contradiction
  let z := pushed 0 60 x
  let u : Config := {z with pc := 39,pos := Function.update z.pos 2 (z.pos 2+1)}
  obtain ⟨hpush,hsz,_⟩ := enqueue_supply 0 x s n q hpc hs hb.symm
  change Supply z s n (q ++ [0]) at hsz
  have hm : Steps code z [60] u := .step _ _ _ _ [] rfl (.right _ _ _) (.nil _)
  have hsu : Supply u s n (q ++ [0]) := by
    simpa [Supply,CacheAt,GalilFppMaterialize.QueueAt,u] using hsz
  have hcu : u.pos 2 = position (failure w) p+1 := by simp [u,z,pushed,hC]
  have hsuPos : u.pos 3 = p-failure w p := by simpa [u,z,pushed] using hS
  have hhu : u.pos 2 ≤ n := by simp [u,z,pushed]; omega
  have hau : position (failure w) N+1 ≤ n+(q ++ [0]).length := by simp; omega
  have huu : GalilFppForward.FullUnary (u.tape 3) (u.pos 3) := by simpa [u,z,pushed] using hu
  obtain ⟨y,qs,m,r,hr,hypc,hyC,hyS,hyu,hys,hnm,htotal,hlt,hframe,hcost⟩ :=
    scan_candidate_cost w N p u s n (q ++ [0]) hN hp rfl hcu hsuPos hhu hau hsu he huu
  refine ⟨y,[62,61,60] ++ qs,m,r,
    GalilFppCopy.steps_append (GalilFppCopy.steps_append hpush hm) hr,
    hypc,hyC,hyS,hyu,hys,hnm,?_,hlt,?_,?_⟩
  · simpa [Nat.add_assoc] using htotal
  · intro t h2 h3 h5 h6
    simpa [u,z,pushed,h2,h5] using hframe t h2 h3 h5 h6
  · have hB : u.pos 5 = x.pos 5+1 := by simp [u,z,pushed]
    rw [hB] at hcost
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

theorem matched_generated_cost (w : List α) (N p : ℕ) (x : Config) (s : ℕ → Fin 2)
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
      (∀ t, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      qs.length + 5*y.pos 5 ≤ 11*delta (failure w) p+16+5*x.pos 5 := by
  have heN : Encoded s (failure w) N :=
    ⟨fun k hk => he.1 k (by omega),fun k hk => he.2 k (by omega)⟩
  have ha : position (failure w) N+1 ≤ n+q.length := by
    rw [hgen]; unfold generatedPosition; omega
  have hb : s (n+q.length) = 0 := by rw [hgen]; exact matched_zero w s N p he hp hnext
  obtain ⟨y,qs,m,r,hr,hypc,hyC,hyS,hyu,hys,hnm,htotal,hlt,hframe,hcost⟩ :=
    matched_lazy_cost w N p x s n q hN hp hpc hC hS hcell ha hs heN hb hu
  refine ⟨y,qs,m,r,hr,hypc,hyC,hyS,hyu,hys,hnm,?_,hlt,hframe,hcost⟩
  have hd : delta (failure w) N = failure w N-p := by unfold delta; omega
  have hpos := position_step (failure w) N
  unfold generatedPosition at hgen
  omega

#print axioms matched_generated_cost
#print axioms matched_lazy_cost
#print axioms scan_candidate_cost
end PalPeg.GalilFppSupplyCost
