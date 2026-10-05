import Complexity.NStackIO

/-!
# Space from time for stack machines over numbers

A step raises a number by at most one and a stack's encoding by at most the largest number plus one. So a run of `t`
steps from a state whose numbers are at most `m` and whose encoded stacks are at most `e` long stays within
`e + t (m + t + 1)` (`nexec_space`): programs only need time bounds; the space bound (`NFits`) follows.
-/

namespace Complexity

variable {K : Nat}

/-- Numbers at most `m`, encoded stacks at most `e` long. -/
def Bnd (m e : Nat) (S : Lists K) : Prop := (∀ i, ∀ v ∈ S i, v ≤ m) ∧ ∀ i, (encS (S i)).length ≤ e

theorem Bnd.mono {m e m' e' : Nat} {S : Lists K} (h : Bnd m e S) (hm : m ≤ m') (he : e ≤ e') : Bnd m' e' S :=
  ⟨fun i v hv => Nat.le_trans (h.1 i v hv) hm, fun i => Nat.le_trans (h.2 i) he⟩

theorem length_encS_le (l : List Nat) (m : Nat) (h : ∀ v ∈ l, v ≤ m) : ∀ v ∈ l, (encN v).length ≤ m + 1 := by
  intro v hv; have := h v hv; simp [encN]; omega

theorem length_encS_append (l l' : List Nat) : (encS (l ++ l')).length = (encS l).length + (encS l').length := by
  simp [encS, List.flatMap_append]

theorem length_encS_dropLast_le (l : List Nat) : (encS l.dropLast).length ≤ (encS l).length := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', v, rfl⟩
  · simp
  · rw [List.concat_eq_append, List.dropLast_concat, length_encS_append]; omega

theorem mem_of_mem_dropLast' {l : List Nat} {v : Nat} (h : v ∈ l.dropLast) : v ∈ l :=
  (List.dropLast_sublist l).subset h

theorem mem_mapTop {f : Nat → Nat} {l : List Nat} {v : Nat} (h : v ∈ mapTop f l) :
    v ∈ l ∨ ∃ u ∈ l, v = f u := by
  simp only [mapTop, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at h
  rcases h with h | ⟨u, hu, rfl⟩
  · exact .inl (mem_of_mem_dropLast' h)
  · exact .inr ⟨u, List.mem_of_getLast? hu, rfl⟩

theorem length_encS_mapTop (f : Nat → Nat) (hf : ∀ v, f v ≤ v + 1) (l : List Nat) :
    (encS (mapTop f l)).length ≤ (encS l).length + 1 := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', v, rfl⟩
  · simp [mapTop]
  · rw [List.concat_eq_append, mapTop_snoc, length_encS_snoc, length_encS_snoc]
    have := hf v; omega

/-- **One primitive step.** -/
theorem prim_bnd (a : NPrim K) {m e : Nat} {S : Lists K} (h : Bnd m e S) : Bnd (m + 1) (e + m + 1) (a.apply S) := by
  have hset : ∀ (i : Fin K) (l : List Nat), (∀ v ∈ l, v ≤ m + 1) → (encS l).length ≤ e + m + 1 →
      Bnd (m + 1) (e + m + 1) (S.set i l) := fun i l hl hle => by
    constructor
    · intro x v hv
      by_cases hx : x = i
      · subst hx; rw [Lists.set_same] at hv; exact hl v hv
      · rw [Lists.set_ne _ _ hx] at hv; have := h.1 x v hv; omega
    · intro x
      by_cases hx : x = i
      · subst hx; rw [Lists.set_same]; exact hle
      · rw [Lists.set_ne _ _ hx]; have := h.2 x; omega
  cases a with
  | pushZ i =>
    refine hset i _ (fun v hv => ?_) ?_
    · rcases List.mem_append.1 hv with hv | hv
      · have := h.1 i v hv; omega
      · simp at hv; omega
    · rw [length_encS_snoc]; have := h.2 i; omega
  | inc i =>
    refine hset i _ (fun v hv => ?_) ?_
    · rcases mem_mapTop hv with hv | ⟨u, hu, rfl⟩
      · have := h.1 i v hv; omega
      · have := h.1 i u hu; omega
    · have := length_encS_mapTop (fun x => x + 1) (fun v => Nat.le_refl _) (S i)
      have := h.2 i; omega
  | dec i =>
    refine hset i _ (fun v hv => ?_) ?_
    · rcases mem_mapTop hv with hv | ⟨u, hu, rfl⟩
      · have := h.1 i v hv; omega
      · have := h.1 i u hu; omega
    · have := length_encS_mapTop (fun x => x - 1) (fun v => by omega) (S i)
      have := h.2 i; omega
  | pop i =>
    refine hset i _ (fun v hv => ?_) ?_
    · have := h.1 i v (mem_of_mem_dropLast' hv); omega
    · have := length_encS_dropLast_le (S i); have := h.2 i; omega
  | dup i j _ =>
    refine hset j _ (fun v hv => ?_) ?_
    · rcases List.mem_append.1 hv with hv | hv
      · have := h.1 j v hv; omega
      · simp only [Option.mem_toList] at hv
        have := h.1 i v (List.mem_of_getLast? hv); omega
    · have hj := h.2 j
      cases hl : (S i).getLast? with
      | none => simp only [Option.toList_none, List.append_nil]; omega
      | some v =>
        have := h.1 i v (List.mem_of_getLast? hl)
        simp only [Option.toList_some]
        rw [length_encS_snoc]; omega

/-- The growth over `t` steps. -/
def grow (m t : Nat) : Nat := t * (m + t + 1)

theorem grow_add (m t₁ t₂ : Nat) : grow m t₁ + grow (m + t₁) t₂ ≤ grow m (t₁ + t₂) := by
  simp only [grow]
  have h₁ : t₁ * (m + t₁ + 1) ≤ t₁ * (m + (t₁ + t₂) + 1) := Nat.mul_le_mul_left _ (by omega)
  have h₂ : t₂ * (m + t₁ + t₂ + 1) = t₂ * (m + (t₁ + t₂) + 1) := by congr 1; omega
  rw [Nat.add_mul t₁ t₂]; omega

theorem grow_mono {m t t' : Nat} (h : t ≤ t') : grow m t ≤ grow m t' :=
  Nat.mul_le_mul h (by omega)

theorem grow_one (m : Nat) : m + 1 ≤ grow m 1 := by simp [grow]

def LOutcome.state : LOutcome K → Lists K
  | .cont S => S
  | .stop _ S => S

/-- **Space from time.** -/
theorem nexec_space {p : NProg K} {S : Lists K} {t : Nat} {o : LOutcome K}
    (hx : NExec (fun _ => True) p S t o) : ∀ m e, Bnd m e S →
      Bnd (m + t) (e + grow m t) o.state ∧ ∀ B, e + grow m t + 2 ≤ B → NExec (NFits B) p S t o := by
  have fits : ∀ {B e m : Nat} {S : Lists K}, Bnd m e S → e + 2 ≤ B → NFits B S := fun hb he =>
    ⟨by omega, fun i => by have := hb.2 i; omega⟩
  induction hx with
  | @prim a S _ _ =>
    intro m e hb
    have h1 := prim_bnd a hb
    have := grow_one m
    exact ⟨h1.mono (Nat.le_refl _) (by omega), fun B hB => .prim (fits hb (by omega)) (fits h1 (by omega))⟩
  | halt _ =>
    intro m e hb
    exact ⟨hb.mono (by omega) (by omega), fun B hB => .halt (fits hb (by omega))⟩
  | @seqC p q S S₁ t₁ t₂ o _ _ ih₁ ih₂ =>
    intro m e hb
    obtain ⟨hb₁, hx₁⟩ := ih₁ m e hb
    obtain ⟨hb₂, hx₂⟩ := ih₂ (m + t₁) (e + grow m t₁) hb₁
    have hg := grow_add m t₁ t₂
    refine ⟨hb₂.mono (by omega) (by omega), fun B hB => .seqC (hx₁ B ?_) (hx₂ B (by omega))⟩
    have := grow_mono (m := m) (show t₁ ≤ t₁ + t₂ by omega); omega
  | seqS _ ih =>
    intro m e hb
    obtain ⟨hb₁, hx₁⟩ := ih m e hb
    exact ⟨hb₁, fun B hB => .seqS (hx₁ B hB)⟩
  | @iteT i c p q S t o _ hc _ ih =>
    intro m e hb
    obtain ⟨hb₁, hx₁⟩ := ih m e hb
    have := grow_mono (m := m) (show t ≤ t + 1 by omega)
    exact ⟨hb₁.mono (by omega) (by omega), fun B hB => .iteT (fits hb (by omega)) hc (hx₁ B (by omega))⟩
  | @iteF i c p q S t o _ hc _ ih =>
    intro m e hb
    obtain ⟨hb₁, hx₁⟩ := ih m e hb
    have := grow_mono (m := m) (show t ≤ t + 1 by omega)
    exact ⟨hb₁.mono (by omega) (by omega), fun B hB => .iteF (fits hb (by omega)) hc (hx₁ B (by omega))⟩
  | loopF _ hc =>
    intro m e hb
    exact ⟨hb.mono (by omega) (by omega), fun B hB => .loopF (fits hb (by omega)) hc⟩
  | @loopC i c p S S₁ t₁ t₂ o _ hc _ _ ih₁ ih₂ =>
    intro m e hb
    obtain ⟨hb₁, hx₁⟩ := ih₁ m e hb
    obtain ⟨hb₂, hx₂⟩ := ih₂ (m + t₁) (e + grow m t₁) hb₁
    have hg := grow_add m t₁ t₂
    have h1 := grow_mono (m := m) (show t₁ + t₂ ≤ t₁ + 1 + t₂ by omega)
    have h2 := grow_mono (m := m) (show t₁ ≤ t₁ + 1 + t₂ by omega)
    refine ⟨hb₂.mono (by omega) (by omega), fun B hB => .loopC (fits hb (by omega)) hc (hx₁ B (by omega))
      (hx₂ B (by omega))⟩
  | @loopS i c p S S₁ t₁ b _ hc _ ih =>
    intro m e hb
    obtain ⟨hb₁, hx₁⟩ := ih m e hb
    have := grow_mono (m := m) (show t₁ ≤ t₁ + 1 by omega)
    exact ⟨hb₁.mono (by omega) (by omega), fun B hB => .loopS (fits hb (by omega)) hc (hx₁ B (by omega))⟩

/-- The initial state: bits, encoded within `2 n`. -/
theorem bnd_nInit (w : List Bool) : Bnd 1 (2 * w.length) (nInit K w) := by
  constructor
  · intro i v hv
    simp only [nInit] at hv
    split at hv
    · simp only [List.mem_reverse, List.mem_map] at hv
      obtain ⟨b, _, rfl⟩ := hv
      cases b <;> simp [bitElem]
    · simp at hv
  · intro i
    simp only [nInit]
    split
    · have hb : ∀ e ∈ (w.map bitElem).reverse, e ≤ 1 := by
        intro e he
        simp only [List.mem_reverse, List.mem_map] at he
        obtain ⟨b, _, rfl⟩ := he
        cases b <;> simp [bitElem]
      have : ∀ l : List Nat, (∀ e ∈ l, e ≤ 1) → (encS l).length ≤ 2 * l.length := by
        intro l hl
        induction l with
        | nil => simp [encS]
        | cons a l ih =>
          have ha := hl a List.mem_cons_self
          have := ih (fun e he => hl e (List.mem_cons_of_mem _ he))
          have e : encS (a :: l) = encN a ++ encS l := rfl
          rw [e, List.length_append]; simp only [encN, List.length_cons, List.length_replicate]; omega
      have := this _ hb
      simpa using this
    · simp [encS]

end Complexity
