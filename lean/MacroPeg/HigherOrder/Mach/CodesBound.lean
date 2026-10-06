import MacroPeg.HigherOrder.Mach.EvalBound
import MacroPeg.HigherOrder.Mach.CodesNum

/-!
# The codes stay small

Every code the evaluator produces is at most `N + 2` (`N` the length of the input), when the codes it is given are
(`stepT_codes`): the parser operations only copy codes or make new ones of positions `q ≤ N`, and the rows of the
types are made of such codes.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-- All numbers are at most `B`. -/
def Small (B : Nat) (l : List Nat) : Prop := ∀ c ∈ l, c ≤ B

theorem getD_small {B : Nat} {l : List Nat} (h : Small B l) (q : Nat) : l.getD q 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases hq : l[q]? with _ | c
  · simp
  · exact h c (List.mem_of_getElem? hq)

theorem seqC_small {N B : Nat} {ca cb : List Nat} (ha : Small B ca) (hb : Small B cb) : Small B (seqC N ca cb) := by
  intro c hc
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hc
  dsimp only
  split
  · exact getD_small hb _
  · exact getD_small ha _

theorem altC_small {N B : Nat} {ca cb : List Nat} (ha : Small B ca) (hb : Small B cb) : Small B (altC N ca cb) := by
  intro c hc
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hc
  dsimp only
  split
  · exact getD_small hb _
  · exact getD_small ha _

theorem notC_small {N B : Nat} (hB : N + 2 ≤ B) {ca : List Nat} : Small B (notC N ca) := by
  intro c hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
  have := List.mem_range.1 hq
  dsimp only
  split
  · omega
  · split <;> omega

theorem starAt_le {N : Nat} (ca : List Nat) : ∀ q, q ≤ N → starAt ca q ≤ N + 2
  | q, hq => by
    rw [starAt]
    split
    · split
      · exact starAt_le ca _ (by omega)
      · omega
    · split <;> omega
termination_by q => q

theorem starC_small {N B : Nat} (hB : N + 2 ≤ B) {ca : List Nat} : Small B (starC N ca) := by
  intro c hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
  have := starAt_le (N := N) ca q (by have := List.mem_range.1 hq; omega)
  omega

theorem epsC_small (N : Nat) : Small (N + 2) (epsC N) := by
  intro c hc; obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc; have := List.mem_range.1 hq; omega

theorem anyC_small (N : Nat) : Small (N + 2) (anyC N) := by
  intro c hc; obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc; have := List.mem_range.1 hq; split <;> omega

theorem chrC_small (xs : List Nat) (p : Nat → Bool) : Small (xs.length + 2) (chrC xs p) := by
  intro c hc; obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc; have := List.mem_range.1 hq; split <;> omega

theorem litC_small (xs s : List Nat) : Small (xs.length + 2) (litC xs s) := by
  intro c hc; obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc; have := List.mem_range.1 hq; split <;> omega

/-- The leaves an item can be are small. -/
theorem leaf_small (x : List Char) {tt : List (Nat × Nat)} {lt : List (List Nat)} {it : MItem} {e : HExp}
    (h : opOf tt lt it = some (.leaf e)) : Small (x.length + 2) (leafCodes x e) := by
  unfold opOf at h
  split at h
  all_goals first
    | (cases h; first
        | (rw [leafCodes_eps]; exact epsC_small _)
        | (rw [leafCodes_any]; exact anyC_small _)
        | (rw [leafCodes_chr]; have := chrC_small (x.map Char.toNat) (fun d => d == (Char.ofNat it.a).toNat)
           simpa using this)
        | (rw [leafCodes_range]; have := chrC_small (x.map Char.toNat)
             (fun d => decide ((Char.ofNat it.a).toNat ≤ d ∧ d ≤ (Char.ofNat it.b).toNat))
           simpa using this))
    | (rcases hl : litOf lt it.a with _ | str
       · rw [hl] at h; cases h
       · rw [hl] at h; cases h
         rw [leafCodes_lit]; have := litC_small (x.map Char.toNat) (str.map Char.toNat)
         simpa using this)
    | (split at h <;> cases h)
    | cases h

theorem flatVal_small {N : Nat} : ∀ (τ : HO.Ty) {d : Dom τ}, d ∈ elems N τ → Small (N + 2) (flatVal N τ d)
  | .p, d, hd => by
    intro c hc
    rw [flatVal] at hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    have hres : r ∈ resElems N := ((mem_allVecs _ _ _).1 hd).2 r hr
    simp only [resElems, List.mem_cons, List.mem_map, List.mem_range] at hres
    rcases hres with rfl | rfl | ⟨q, hq, rfl⟩ <;> simp [resCode] <;> omega
  | .arr a b, f, hf => by
    intro c hc
    rw [flatVal] at hc
    obtain ⟨d, hd, hcd⟩ := List.mem_flatMap.1 hc
    exact flatVal_small b ((mem_elems_arr' hf).2 d hd) c hcd

theorem rowsT_small {j cap N : Nat} {tt : List (Nat × Nat)} (hw : TTWF tt) {t : Nat} (ht : t ≤ tt.length) :
    ∀ r ∈ rowsT j cap N tt t, Small (N + 2) r := by
  intro r hr
  unfold rowsT at hr
  split at hr
  · obtain ⟨τ, hτ⟩ := tyOf_some hw t ht
    rw [rowsNum_eq N t hτ, eRows] at hr
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
    exact flatVal_small τ hd
  · simp at hr

theorem small_flatten {B : Nat} {L : List (List Nat)} (h : ∀ l ∈ L, Small B l) : Small B L.flatten := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
  exact h l hl c hcl

theorem small_chunks {B m : Nat} : ∀ (n : Nat) {l : List Nat}, Small B l → ∀ c ∈ chunksN m n l, Small B c
  | 0, _, _, c, hc => by simp [chunksN] at hc
  | n + 1, l, h, c, hc => by
    simp only [chunksN, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact fun x hx => h x (List.mem_of_mem_take hx)
    · exact small_chunks n (fun x hx => h x (List.mem_of_mem_drop hx)) c hc

theorem mem_zipWith' {α β γ : Type} {f : α → β → γ} {c : γ} : ∀ {l₁ : List α} {l₂ : List β},
    c ∈ List.zipWith f l₁ l₂ → ∃ a b, a ∈ l₁ ∧ b ∈ l₂ ∧ c = f a b
  | [], _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, b, List.mem_cons_self, List.mem_cons_self, rfl⟩
    · obtain ⟨a', b', ha, hb, rfl⟩ := mem_zipWith' h
      exact ⟨a', b', List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, rfl⟩

theorem small_zip_out {B m n : Nat} {f : List Nat → List Nat → List Nat}
    (hf : ∀ a b, Small B a → Small B b → Small B (f a b)) {va vb : List Nat} (ha : Small B va) (hb : Small B vb) :
    Small B (List.zipWith f (chunksN m n va) (chunksN m n vb)).flatten := by
  refine small_flatten (fun l hl => ?_)
  obtain ⟨a, b, ha', hb', rfl⟩ := mem_zipWith' hl
  exact hf a b (small_chunks n ha a ha') (small_chunks n hb b hb')

theorem small_getD {B : Nat} {L : List (List Nat)} (h : ∀ l ∈ L, Small B l) (k : Nat) : Small B (L.getD k []) := by
  rw [List.getD_eq_getElem?_getD]
  rcases hk : L[k]? with _ | l
  · simp [Small]
  · exact h l (List.mem_of_getElem? hk)

/-- **The codes stay at most `N + 2`.** -/
theorem stepT_codes {j cap : Nat} {x : List Char} {tt ct : List (Nat × Nat)} {lt Tf : List (List Nat)} {it : MItem}
    (hw : TTWF tt) (hc : CTWF tt ct) (hcx : it.ctx ≤ ct.length) {vs : List (List Nat)}
    (hvs : ∀ v ∈ vs, Small (x.length + 2) v) (hTf : ∀ f ∈ Tf, Small (x.length + 2) f) :
    ∀ v ∈ stepT j cap x tt ct lt Tf it vs, Small (x.length + 2) v := by
  have tail : ∀ {a : List Nat} {r : List (List Nat)}, Small (x.length + 2) a → (∀ v ∈ r, Small (x.length + 2) v) →
      ∀ v ∈ a :: r, Small (x.length + 2) v := fun ha hr v hv => by
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ha
    · exact hr v hv
  unfold stepT
  dsimp only
  split
  · refine tail (small_zip_out (fun a b ha hb => by rw [seqCodes_eq]; exact seqC_small ha hb)
      (hvs _ (by simp)) (hvs _ (by simp))) (fun v hv => hvs v (by simp [hv]))
  · refine tail (small_zip_out (fun a b ha hb => by rw [altCodes_eq]; exact altC_small ha hb)
      (hvs _ (by simp)) (hvs _ (by simp))) (fun v hv => hvs v (by simp [hv]))
  · refine tail (small_flatten (fun l hl => ?_)) (fun v hv => hvs v (by simp [hv]))
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hl
    rw [starCodes_eq]; exact starC_small (Nat.le_refl _)
  · refine tail (small_flatten (fun l hl => ?_)) (fun v hv => hvs v (by simp [hv]))
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hl
    rw [notCodes_eq]; exact notC_small (Nat.le_refl _)
  · refine tail (small_flatten (fun l hl => ?_)) hvs
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hl
    exact small_getD (rowsT_small hw (varTy_type_le hc hcx it.a)) k
  · refine tail (small_flatten (fun l hl => ?_)) hvs
    rw [List.eq_of_mem_replicate hl]; exact small_getD hTf _
  · exact hvs
  · refine tail (small_flatten (fun l hl => ?_)) (fun v hv => hvs v (by simp [hv]))
    obtain ⟨fv, yv, hfv, _, rfl⟩ := mem_zipWith' hl
    intro c hc'
    exact small_chunks _ (hvs _ (by simp)) fv hfv c (List.mem_of_mem_drop (List.mem_of_mem_take hc'))
  · split
    · rename_i e hop
      refine tail (small_flatten (fun l hl => ?_)) hvs
      rw [List.eq_of_mem_replicate hl]; exact leaf_small x hop
    · exact hvs

end Shallot.MacroPeg.Mach
