import MacroPeg.CBV.CaptureTransitionProfile

/-! Finite descriptors of unbounded repetitions of one captured-word
transition. The descriptors will be rendered inline, preserving parameters. -/
namespace Shallot.MacroPeg.CBV.CaptureOrbit

def orbit (f : Nat → Nat) (q : Nat) : Nat → Nat
  | 0 => q
  | n+1 => f (orbit f q n)

theorem orbit_add (f : Nat → Nat) (q n m : Nat) :
    orbit f q (n+m)=orbit f (orbit f q n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change f (orbit f q (n+m))=f (orbit f (orbit f q n) m)
    exact congrArg f ih

theorem orbit_bound (f : Nat → Nat) (W : Nat) (hf : ∀ q, q<W → f q<W)
    (q : Nat) (hq : q<W) : ∀ n, orbit f q n<W
  | 0 => hq
  | n+1 => hf _ (orbit_bound f W hf q hq n)

theorem nodup_subset_length (xs ys : List Nat) (hx : xs.Nodup) (hs : ∀ a∈xs, a∈ys) :
    xs.length≤ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have hn := List.nodup_cons.mp hx
    have ha := hs a (by simp)
    have ht : ∀ b∈xs, b∈ys.erase a := by
      intro b hb
      have hne : b≠a := by intro he; subst b; exact hn.1 hb
      exact (List.mem_erase_of_ne hne).mpr (hs b (by simp [hb]))
    have hl := ih _ hn.2 ht
    rw [List.length_erase_of_mem ha] at hl
    simp only [List.length_cons]
    have hy : 0<ys.length := List.length_pos_of_mem ha
    omega

/-- A bounded state path has a repeated pair among its first W+1 states. -/
theorem bounded_collision (g : Nat → Nat) (W : Nat) (hg : ∀ i, i≤W → g i<W) :
    ∃ a b, a<b ∧ b≤W ∧ g a=g b := by
  classical
  by_cases he : ∃ a b, a<b ∧ b≤W ∧ g a=g b
  · exact he
  · have hn : ((List.range (W+1)).map g).Nodup := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      simp only [List.length_map,List.length_range] at hi hj
      simp only [List.getElem_map,List.getElem_range]
      exact fun h => he ⟨i,j,hij,by omega,h⟩
    have hl := nodup_subset_length _ (List.range W) hn (by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      exact List.mem_range.mpr (hg i (by have := List.mem_range.mp hi; omega)))
    simp only [List.length_map,List.length_range] at hl
    omega

theorem orbit_shift (f : Nat → Nat) (q a b : Nat) (he : orbit f q a=orbit f q b) (t : Nat) :
    orbit f q (a+t)=orbit f q (b+t) := by rw [orbit_add,orbit_add,he]

theorem loop_mul (f : Nat → Nat) (r l : Nat) (hl : orbit f r l=r) :
    ∀ m, orbit f r (l*m)=r
  | 0 => rfl
  | m+1 => by rw [Nat.mul_succ,orbit_add,loop_mul f r l hl m,hl]

/-- k is a short prefix count; l=0 means an exact finite count, while
positive l describes any number of complete l-copy blocks after k. -/
def Fits (n k l : Nat) : Prop := if l=0 then n=k else ∃ m, n=k+l*m

def descriptors (f : Nat → Nat) (W q r : Nat) : List (Nat × Nat) :=
  ((List.range W).filter (fun k => orbit f q k==r)).map (fun k => (k,0)) ++
    (List.range W).flatMap (fun k => ((List.range W).filterMap (fun j =>
      if orbit f q k=r ∧ orbit f r (j+1)=r then some (k,j+1) else none)))

theorem mem_descriptors (f : Nat → Nat) (W q r k l : Nat) :
    (k,l)∈descriptors f W q r ↔
      k<W ∧ orbit f q k=r ∧ (l=0 ∨ (0<l ∧ l≤W ∧ orbit f r l=r)) := by
  simp only [descriptors,List.mem_append,List.mem_map,List.mem_filter,List.mem_range,beq_iff_eq,
    Prod.mk.injEq,List.mem_flatMap,List.mem_filterMap]
  constructor
  · intro h
    rcases h with ⟨i,⟨hi,hr⟩,he,hl⟩ | ⟨i,hi,j,hj,he⟩
    · subst i; subst l; exact ⟨hi,hr,Or.inl rfl⟩
    · split at he
      · rename_i hs
        cases he
        exact ⟨hi,hs.1,Or.inr ⟨by omega,by omega,hs.2⟩⟩
      · contradiction
  · rintro ⟨hk,hr,hl | ⟨hl,hW,hloop⟩⟩
    · subst l; exact Or.inl ⟨k,⟨hk,hr⟩,rfl,rfl⟩
    · refine Or.inr ⟨k,hk,l-1,by omega,?_⟩
      rw [show l-1+1=l by omega,if_pos ⟨hr,hloop⟩]

theorem descriptors_sound (f : Nat → Nat) (W q r k l n : Nat)
    (hd : (k,l)∈descriptors f W q r) (hn : Fits n k l) : orbit f q n=r := by
  obtain ⟨_,hk,hl⟩ := (mem_descriptors f W q r k l).mp hd
  by_cases hz : l=0
  · have he : n=k := by simpa [Fits,hz] using hn
    rw [he]
    exact hk
  · obtain ⟨m,rfl⟩ := (show ∃ m, n=k+l*m from by simpa only [Fits,if_neg hz] using hn)
    rw [orbit_add,hk,loop_mul f r l (hl.resolve_left hz).2.2 m]

/-- Every repetition count is covered by a finite prefix/cycle descriptor,
with both lengths bounded by the number of states. -/
theorem descriptors_complete (f : Nat → Nat) (W : Nat) (hf : ∀ q, q<W → f q<W)
    (q : Nat) (hq : q<W) (n : Nat) :
    ∃ k l, (k,l)∈descriptors f W q (orbit f q n) ∧ Fits n k l := by
  by_cases hn : n<W
  · exact ⟨n,0,(mem_descriptors _ _ _ _ _ _).mpr ⟨hn,rfl,Or.inl rfl⟩,by simp [Fits]⟩
  · obtain ⟨a,b,hab,hb,he⟩ := bounded_collision (orbit f q) W (fun i _ => orbit_bound f W hf q hq i)
    let l := b-a
    have hl : 0<l := by dsimp [l]; omega
    have hbl : a+l=b := by dsimp [l]; omega
    have hna : a≤n := by omega
    let t := (n-a)%l
    let k := a+t
    have ht : t<l := Nat.mod_lt _ hl
    have hk : k<W := by dsimp [k]; omega
    have hloop : orbit f (orbit f q a) l=orbit f q a := by rw [←orbit_add,hbl,←he]
    have hdiv := Nat.mod_add_div (n-a) l
    have hnrep : n=k+l*((n-a)/l) := by dsimp [k,t]; omega
    have heq : orbit f q n=orbit f q k := by
      rw [show n=a+(l*((n-a)/l)+t) by dsimp [k] at hnrep; omega,
        orbit_add,orbit_add,loop_mul f _ l hloop,←orbit_add]
    have hkloop : orbit f (orbit f q k) l=orbit f q k := by
      have hh := orbit_shift f q a b he t
      rw [←orbit_add]
      have hkl : b+t=k+l := by dsimp [k]; omega
      simpa only [←hkl] using hh.symm
    refine ⟨k,l,(mem_descriptors _ _ _ _ _ _).mpr ⟨hk,heq.symm,Or.inr ⟨hl,by dsimp [l]; omega,?_⟩⟩,?_⟩
    · simpa only [heq] using hkloop
    · exact (if_neg (Nat.ne_of_gt hl)).mpr ⟨(n-a)/l,hnrep⟩

theorem descriptors_iff (f : Nat → Nat) (W : Nat) (hf : ∀ q, q<W → f q<W)
    (q : Nat) (hq : q<W) (r n : Nat) :
    orbit f q n=r ↔ ∃ k l, (k,l)∈descriptors f W q r ∧ Fits n k l := by
  constructor
  · intro he; rw [←he]; exact descriptors_complete f W hf q hq n
  · rintro ⟨k,l,hd,hn⟩; exact descriptors_sound f W q r k l n hd hn

end Shallot.MacroPeg.CBV.CaptureOrbit
