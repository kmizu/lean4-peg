import Complexity.ListCompile
import Complexity.ListIOSpec

/-!
# From list programs to PSPACE and polynomial-time computability

* `lm_pspace`: a list program that decides `L` with lists of polynomial length (from `initLists w`) gives `PSPACE L`.
* `lm_polytime`: a list program that, within polynomially many steps and with lists of polynomial length, leaves
  `f w` (as bits) in list `o` and list `0` empty gives `PolyTimeComputable f`.
-/

namespace Complexity

variable {k : Nat}

theorem Exec.mono {P P' : Tapes k → Prop} (hP : ∀ τ, P τ → P' τ) {p : Prog k} {τ : Tapes k} {t : Nat}
    {o : Outcome k} (h : Exec P p τ t o) : Exec P' p τ t o := by
  induction h with
  | act h₁ h₂ => exact .act (hP _ h₁) (hP _ h₂)
  | halt h₁ => exact .halt (hP _ h₁)
  | seqC _ _ ih₁ ih₂ => exact .seqC ih₁ ih₂
  | seqS _ ih => exact .seqS ih
  | iteT h₁ h₂ _ ih => exact .iteT (hP _ h₁) h₂ ih
  | iteF h₁ h₂ _ ih => exact .iteF (hP _ h₁) h₂ ih
  | loopF h₁ h₂ => exact .loopF (hP _ h₁) h₂
  | loopC h₁ h₂ _ _ ih₁ ih₂ => exact .loopC (hP _ h₁) h₂ ih₁ ih₂
  | loopS h₁ h₂ _ ih => exact .loopS (hP _ h₁) h₂ ih

theorem TFits.mono {B B' : Nat} (hB : B ≤ B') {τ : Tapes k} (h : TFits B τ) : TFits B' τ :=
  fun i => ⟨Nat.lt_of_lt_of_le (h i).1 hB, fun j hj => (h i).2 j (Nat.le_trans hB hj)⟩

theorem LenOK.mono {B B' : Nat} (hB : B ≤ B') {L : Lists k} (h : LenOK B L) : LenOK B' L :=
  fun i => Nat.le_trans (h i) hB

theorem isPoly_add {f g : Nat → Nat} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun n => f n + g n) := by
  obtain ⟨c, d, hc⟩ := hf
  obtain ⟨c', d', hc'⟩ := hg
  refine ⟨c + c', max d d', fun n => ?_⟩
  have h1 : (n + 1) ^ d ≤ (n + 1) ^ max d d' := Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left _ _)
  have h2 : (n + 1) ^ d' ≤ (n + 1) ^ max d d' := Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right _ _)
  have := hc n; have := hc' n
  have := Nat.mul_le_mul_left c h1; have := Nat.mul_le_mul_left c' h2
  show f n + g n ≤ _
  rw [Nat.add_mul]; omega

theorem isPoly_mul {f g : Nat → Nat} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun n => f n * g n) := by
  obtain ⟨c, d, hc⟩ := hf
  obtain ⟨c', d', hc'⟩ := hg
  refine ⟨c * c', d + d', fun n => ?_⟩
  calc f n * g n ≤ (c * (n + 1) ^ d) * (c' * (n + 1) ^ d') := Nat.mul_le_mul (hc n) (hc' n)
    _ = c * c' * (n + 1) ^ (d + d') := by rw [Nat.pow_add]; ac_rfl

theorem isPoly_const (a : Nat) : IsPoly (fun _ => a) := ⟨a, 0, fun n => by simp⟩

theorem isPoly_id : IsPoly (fun n => n) := ⟨1, 1, fun n => by simp⟩

theorem lm_pspace (h1 : 1 < k) (lp : LProg k) (E : Nat) (hE : 2 ≤ E) (hc : lp.ConstOK E) (L : Lang)
    (s : Nat → Nat) (hs : IsPoly s)
    (h : ∀ w, ∃ t b L', LExec (LenOK (s w.length)) lp (initLists k w) t (.stop b L') ∧ (b = true ↔ L w)) :
    PSPACE L := by
  let p : Prog k := .seq (initP h1) lp.compile
  have hsym : p.SymOK (E + 4) := ⟨initP_symOK h1 _ (by omega), compile_symOK E lp hc⟩
  let s' : Nat → Nat := fun n => s n + (n + 2)
  have hs' : IsPoly s' := isPoly_add hs (isPoly_add isPoly_id (isPoly_const 2))
  obtain ⟨hdec, hsp⟩ := p.decides_of_exec (E + 4) (by omega) hsym L s' (fun w => by
    obtain ⟨t, b, L', hex, hb⟩ := h w
    obtain ⟨t₀, τ₀, _, hex₀, hR₀⟩ := initP_spec h1 w
    have hQ : ∀ L₁ : Lists k, LenOK (s w.length) L₁ → LenOK (s' w.length) L₁ := fun _ hL => hL.mono (by simp [s'])
    obtain ⟨t', o', _, hex', hr'⟩ := (compile_exec (B := s' w.length) hQ hex).1 τ₀ hR₀
    cases o' with
    | cont _ => exact hr'.elim
    | stop b' τ' =>
      obtain ⟨rfl, _⟩ := hr'
      exact ⟨t₀ + t', b, τ', Exec.seqC (hex₀.mono (fun _ ht => ht.mono (by simp [s']))) hex', hb⟩)
  exact ⟨k, p.machine (E + 4) (by omega) hsym, s', hs', hdec, hsp⟩

theorem lm_polytime (h1 : 1 < k) (o : Fin k) (ho : o.val ≠ 0) (lp : LProg k) (E : Nat) (hE : 2 ≤ E)
    (hc : lp.ConstOK E) (f : List Bool → List Bool) (s T : Nat → Nat) (hs : IsPoly s) (hT : IsPoly T)
    (h : ∀ w, ∃ t L', t ≤ T w.length ∧ LExec (LenOK (s w.length)) lp (initLists k w) t (.cont L') ∧
      L' ⟨0, by omega⟩ = [] ∧ L' o = (f w).map bitElem) :
    PolyTimeComputable f := by
  have h0 : 0 < k := by omega
  let p : Prog k := .seq (initP h1) (.seq lp.compile (finishP o))
  have hsym : p.SymOK (E + 4) := ⟨initP_symOK h1 _ (by omega), compile_symOK E lp hc, finishP_symOK o _⟩
  let B : Nat → Nat := fun n => s n + (n + 2)
  have hB : IsPoly B := isPoly_add hs (isPoly_add isPoly_id (isPoly_const 2))
  let T' : Nat → Nat := fun n => (4 * n + 8) + T n * (8 * B n + 20) + (2 * B n + 4)
  have hT' : IsPoly T' := isPoly_add (isPoly_add (isPoly_add (isPoly_mul (isPoly_const 4) isPoly_id)
    (isPoly_const 8)) (isPoly_mul hT (isPoly_add (isPoly_mul (isPoly_const 8) hB) (isPoly_const 20))))
    (isPoly_add (isPoly_mul (isPoly_const 2) hB) (isPoly_const 4))
  refine p.polytime_of_exec h0 (E + 4) (by omega) hsym f T' hT' (fun w => ?_)
  obtain ⟨t, L', ht, hex, hL0, hLo⟩ := h w
  obtain ⟨t₀, τ₀, ht₀, hex₀, hR₀⟩ := initP_spec h1 w
  have hQ : ∀ L₁ : Lists k, LenOK (s w.length) L₁ → LenOK (B w.length) L₁ := fun _ hL => hL.mono (by simp [B])
  obtain ⟨t', o', ht', hex', hr'⟩ := (compile_exec (B := B w.length) hQ hex).1 τ₀ hR₀
  cases o' with
  | stop _ _ => exact hr'.elim
  | cont τ₁ =>
    have hlen : LenOK (B w.length) L' := hQ _ (hex.q_end L' (Or.inl rfl))
    obtain ⟨t₂, τ₂, ht₂, hex₂, hout⟩ := finishP_spec h0 o ho hr' hlen hL0 (f w) hLo
    have hfl : (f w).length + 2 ≤ B w.length := by
      have := hlen o; rw [hLo, List.length_map] at this; exact this
    refine ⟨t₀ + (t' + t₂), τ₂, ?_, Exec.seqC (hex₀.mono (fun _ _ => trivial))
      (Exec.seqC (hex'.mono (fun _ _ => trivial)) (hex₂.mono (fun _ _ => trivial))), hout⟩
    have : t * lcost (B w.length) ≤ T w.length * (8 * B w.length + 20) := Nat.mul_le_mul_right _ ht
    simp only [lcost] at ht' this
    show t₀ + (t' + t₂) ≤ (4 * w.length + 8) + T w.length * (8 * B w.length + 20) + (2 * B w.length + 4)
    omega

end Complexity
