import MacroPeg.CBV.UniversalCaptureProfiles

namespace Shallot.MacroPeg.CBV.FiniteProfileClosure
open RecursiveCaptureProfiles
open CaptureTransitionProfile (profile profiles compose)
open UniversalCaptureProfiles (AllIn compose_mem rounds_all)

private theorem nodup_dedup {α : Type} [BEq α] [LawfulBEq α] : ∀ xs : List α, xs.eraseDups.Nodup := by
  intro xs
  induction h : xs.length using Nat.strongRecOn generalizing xs with
  | ind k ih =>
    cases xs with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons,List.nodup_cons]
      refine ⟨?_,ih _ (by have hf := List.length_filter_le (fun b => !b==a) as; simp at h; omega) _ rfl⟩
      simp only [List.mem_eraseDups,List.mem_filter]
      simp

private theorem nodup_subset_length {α : Type} [BEq α] [LawfulBEq α] (xs ys : List α)
    (hn : xs.Nodup) (hs : xs⊆ys) : xs.length≤ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ha : a∈ys := hs (by simp)
    have hxs : xs⊆ys.erase a := by
      intro b hb
      have hba : b≠a := by intro he; subst b; exact (List.nodup_cons.mp hn).1 hb
      exact (List.mem_erase_of_ne hba).mpr (hs (by simp [hb]))
    have he := ih (ys.erase a) (List.nodup_cons.mp hn).2 hxs
    rw [List.length_erase_of_mem ha] at he
    have hp : 0<ys.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

theorem check_iff (D : RegularCaptureProduct.Machine) (A C : List (List Nat)) :
    closureCheck D A C=true ↔ profile D []∈C ∧ product A C⊆C := by
  simp only [closureCheck,Bool.and_eq_true_iff,List.contains_iff_mem,List.all_eq_true]
  constructor
  · rintro ⟨hi,h⟩
    refine ⟨hi,?_⟩
    intro R hR
    obtain ⟨P,hP,hR⟩ := List.mem_flatMap.mp hR
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hR
    exact h P hP Q hQ
  · rintro ⟨hi,h⟩
    exact ⟨hi,fun P hP Q hQ => h (List.mem_flatMap.mpr ⟨P,hP,List.mem_map.mpr ⟨Q,hQ,rfl⟩⟩)⟩

theorem grow_contains (A C : List (List Nat)) : C⊆grow A C := by
  intro P hP
  exact List.mem_eraseDups.mpr (List.mem_append_left _ hP)

theorem grow_checked (D : RegularCaptureProduct.Machine) (A C : List (List Nat))
    (h : closureCheck D A C=true) : closureCheck D A (grow A C)=true := by
  have hc := (check_iff D A C).mp h
  have hback : grow A C⊆C := by
    intro P hP
    rcases List.mem_append.mp (List.mem_eraseDups.mp hP) with hP | hP
    · exact hP
    · exact hc.2 hP
  apply (check_iff D A _).mpr
  refine ⟨grow_contains A C hc.1,?_⟩
  intro R hR
  obtain ⟨P,hP,hR⟩ := List.mem_flatMap.mp hR
  obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hR
  apply grow_contains A C
  exact hc.2 (List.mem_flatMap.mpr ⟨P,hP,List.mem_map.mpr ⟨Q,hback hQ,rfl⟩⟩)

theorem rounds_identity (D : RegularCaptureProduct.Machine) (A : List (List Nat)) :
    ∀ k, profile D []∈rounds A k [profile D []]
  | 0 => by simp [rounds]
  | k+1 => grow_contains A _ (rounds_identity D A k)

theorem rounds_nodup (D : RegularCaptureProduct.Machine) (A : List (List Nat)) :
    ∀ k, (rounds A k [profile D []]).Nodup
  | 0 => by simp [rounds]
  | _+1 => nodup_dedup _

theorem checked_later (D : RegularCaptureProduct.Machine) (A : List (List Nat))
    (k l : Nat) (hkl : k≤l) (hk : closureCheck D A (rounds A k [profile D []])=true) :
    closureCheck D A (rounds A l [profile D []])=true := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction d with
  | zero => exact hk
  | succ d ih => exact grow_checked D A _ ih

theorem grow_strict (D : RegularCaptureProduct.Machine) (A C : List (List Nat))
    (hn : C.Nodup) (hi : profile D []∈C) (hc : closureCheck D A C≠true) : C.length<(grow A C).length := by
  have hs : ¬product A C⊆C := fun hs => hc ((check_iff D A C).mpr ⟨hi,hs⟩)
  have hx : ∃ P, P∈product A C ∧ P∉C := by
    classical
    apply Classical.byContradiction
    intro hn
    apply hs
    intro P hP
    apply Classical.byContradiction
    intro hp
    exact hn ⟨P,hP,hp⟩
  obtain ⟨P,hP,hnot⟩ := hx
  have hp : P∈grow A C := List.mem_eraseDups.mpr (List.mem_append_right _ hP)
  have hlen := nodup_subset_length (P::C) (grow A C) (List.nodup_cons.mpr ⟨hnot,hn⟩)
    (by intro Q hQ; rcases List.mem_cons.mp hQ with rfl | hQ; exact hp; exact grow_contains A C hQ)
  simp only [List.length_cons] at hlen
  omega

/-- Every valid finite profile generator stabilizes within the existing
finite-universe bound. The conservative fallback is unreachable here. -/
theorem converges (D : RegularCaptureProduct.Machine) (hD : D.Valid)
    (A : List (List Nat)) (hA : AllIn D A) :
    closureCheck D A (rounds A (profiles D).length [profile D []])=true := by
  apply Classical.byContradiction
  intro hc
  have hnot (k : Nat) (hk : k≤(profiles D).length) :
      closureCheck D A (rounds A k [profile D []])≠true := by
    intro h
    exact hc (checked_later D A k _ hk h)
  have hg : ∀ k, k≤(profiles D).length → k+1≤(rounds A k [profile D []]).length := by
    intro k
    induction k with
    | zero => simp [rounds]
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hs := grow_strict D A _ (rounds_nodup D A k) (rounds_identity D A k) (hnot k (by omega))
      change k+1+1≤(grow A (rounds A k [profile D []])).length
      omega
  have hmem := rounds_all D A hA (profiles D).length [profile D []]
    (by intro P hP; simp only [List.mem_singleton] at hP; subst P; exact CaptureTransitionProfile.profile_mem D hD [])
  have hlen := nodup_subset_length _ _ (rounds_nodup D A (profiles D).length) hmem
  have hg := hg (profiles D).length (Nat.le_refl _)
  omega

theorem closure_eq_rounds (D : RegularCaptureProduct.Machine) (hD : D.Valid)
    (A : List (List Nat)) (hA : AllIn D A) :
    closure D A=rounds A (profiles D).length [profile D []] := by
  exact if_pos (converges D hD A hA)

/-- A closed finite domain is preserved by arbitrary repetition effects. -/
theorem closure_subset (D : RegularCaptureProduct.Machine) (hD : D.Valid)
    (A C : List (List Nat)) (hA : AllIn D A) (hi : profile D []∈C)
    (hAC : A⊆C) (hm : ∀ P∈C, ∀ Q∈C, compose P Q∈C) : closure D A⊆C := by
  rw [closure_eq_rounds D hD A hA]
  have h : ∀ k, rounds A k [profile D []]⊆C := by
    intro k
    induction k with
    | zero => simpa [rounds] using hi
    | succ k ih =>
      intro R hR
      rcases List.mem_append.mp (List.mem_eraseDups.mp hR) with hR | hR
      · exact ih hR
      · obtain ⟨P,hP,hR⟩ := List.mem_flatMap.mp hR
        obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hR
        exact hm P (hAC hP) Q (ih hQ)
  exact h _

end Shallot.MacroPeg.CBV.FiniteProfileClosure
