import MacroPeg.HigherOrder.Flat.Index

/-!
# Environments as numbers

The values of an environment `ρ : Env Γ` vary over `envs N Γ`, listed with the innermost variable varying fastest, so
the environments of `a :: Γ` come in blocks of `|elems a|` (one block per environment of `Γ`): the table of a lambda
at `ρ` is one block of its body's vector (`chunksN`).

* `elems_nodup`: the well-formed values are listed without repetition, so value number `k` has number `k`
  (`map_vIdx_elems`).
* `varVec_eq`: the numbers of variable `i` over all environments, by a closed formula.
-/

namespace Shallot.MacroPeg.Flat

open Shallot.MacroPeg.HO

/-! ## No repetitions -/

theorem nodup_map_inj {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_inj f hf h.2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    exact h.1 (hf b a e ▸ hb)

theorem nodup_filter {α : Type} (p : α → Bool) : ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.filter_cons]
    split
    · rw [List.nodup_cons]
      exact ⟨fun hm => h.1 (List.mem_filter.1 hm).1, nodup_filter p h.2⟩
    · exact nodup_filter p h.2

/-- Prefixing each first element to every tail keeps a list without repetitions. -/
theorem nodup_flatMap_cons {α : Type} {ys : List (List α)} (hy : ys.Nodup) :
    ∀ {xs : List α}, xs.Nodup → (xs.flatMap (fun a => ys.map (a :: ·))).Nodup
  | [], _ => by simp
  | a :: xs, hxs => by
    rw [List.nodup_cons] at hxs
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨nodup_map_inj _ (fun _ _ e => (List.cons.inj e).2) hy, nodup_flatMap_cons hy hxs.2, ?_⟩
    intro u hu v hv e
    obtain ⟨u', _, rfl⟩ := List.mem_map.1 hu
    obtain ⟨b, hb, hv⟩ := List.mem_flatMap.1 hv
    obtain ⟨v', _, rfl⟩ := List.mem_map.1 hv
    exact hxs.1 ((List.cons.inj e).1 ▸ hb)

theorem nodup_allVecs {α : Type} {xs : List α} (hxs : xs.Nodup) : ∀ m, (allVecs xs m).Nodup
  | 0 => by simp [allVecs]
  | m + 1 => nodup_flatMap_cons (nodup_allVecs hxs m) hxs

theorem nodup_resElems (N : Nat) : (resElems N).Nodup := by
  simp only [resElems, List.nodup_cons, List.mem_cons, List.mem_map, List.mem_range]
  refine ⟨by simp, by simp, nodup_map_inj _ (fun _ _ e => by simpa using e) List.nodup_range⟩

theorem elems_nodup (N : Nat) : ∀ τ : HO.Ty, (elems N τ).Nodup
  | .p => nodup_allVecs (nodup_resElems N) _
  | .arr _ b => nodup_filter _ (nodup_allVecs (elems_nodup N b) _)

theorem indexIn_getElem {α : Type} [DecidableEq α] : ∀ {l : List α}, l.Nodup → ∀ k (h : k < l.length),
    indexIn l[k] l = k
  | [], _, _, h => by simp at h
  | _ :: _, _, 0, _ => by simp [indexIn]
  | a :: l, hl, k + 1, h => by
    rw [List.nodup_cons] at hl
    have hk : k < l.length := by simp at h; omega
    have e : (a :: l)[k + 1] = l[k] := rfl
    rw [e]
    have hne : a ≠ l[k] := fun e => hl.1 (e ▸ List.getElem_mem _)
    simp only [indexIn, hne, if_false]
    rw [indexIn_getElem hl.2 k hk]

/-- Value number `k` has number `k`. -/
theorem map_vIdx_elems (N : Nat) (τ : HO.Ty) : (elems N τ).map (vIdx N τ) = List.range (elems N τ).length := by
  apply List.ext_getElem (by simp)
  intro k h₁ _
  simp only [List.getElem_map, List.getElem_range, vIdx]
  exact indexIn_getElem (elems_nodup N τ) k (by simpa using h₁)

/-! ## All environments -/

/-- The environments of `Γ`, the innermost variable varying fastest. -/
def envs (N : Nat) : (Γ : List HO.Ty) → List (HO.Env Γ)
  | [] => [()]
  | τ :: Γ => (envs N Γ).flatMap (fun ρ => (elems N τ).map (fun d => (d, ρ)))

/-- The number of environments of `Γ`. -/
def envSize (N : Nat) : List HO.Ty → Nat
  | [] => 1
  | τ :: Γ => envSize N Γ * (elems N τ).length

theorem length_flatMap_const {α β : Type} (f : α → List β) (k : Nat) :
    ∀ l : List α, (∀ a ∈ l, (f a).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      length_flatMap_const f k l (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    simp [Nat.succ_mul, Nat.add_comm]

theorem envs_length (N : Nat) : ∀ Γ : List HO.Ty, (envs N Γ).length = envSize N Γ
  | [] => rfl
  | τ :: Γ => by
    simp only [envs, envSize]
    rw [length_flatMap_const _ (elems N τ).length _ (fun _ _ => by simp), envs_length N Γ]

theorem envs_mem (N : Nat) : ∀ {Γ : List HO.Ty} {ρ : HO.Env Γ}, ρ ∈ envs N Γ → Env.Mem N ρ
  | [], _, _ => trivial
  | τ :: Γ, (d, ρ), h => by
    simp only [envs, List.mem_flatMap, List.mem_map] at h
    obtain ⟨ρ', hρ', d', hd', rfl, rfl⟩ := h
    exact ⟨hd', envs_mem N hρ'⟩

/-! ## Variables -/

/-- The numbers of variable `i` over the environments of `Γ`. -/
def varVec (N : Nat) : List HO.Ty → Nat → List Nat
  | [], _ => []
  | τ :: Γ, 0 => (List.replicate (envSize N Γ) (List.range (elems N τ).length)).flatten
  | τ :: Γ, i + 1 => (varVec N Γ i).flatMap (fun v => List.replicate (elems N τ).length v)

theorem flatMap_const_list {α β : Type} (u : List β) : ∀ l : List α,
    l.flatMap (fun _ => u) = (List.replicate l.length u).flatten
  | [] => rfl
  | _ :: l => by simp [List.replicate_succ, flatMap_const_list u l]

theorem varVec_eq (N : Nat) : ∀ (Γ : List HO.Ty) (i : Nat) {τ : HO.Ty} (h : Γ[i]? = some τ),
    varVec N Γ i = (envs N Γ).map (fun ρ => vIdx N τ (Env.get ρ i h))
  | [], _, _, h => by simp at h
  | σ :: Γ, 0, τ, h => by
    obtain rfl : σ = τ := by simpa using h
    simp only [varVec, envs, List.map_flatMap, List.map_map]
    have : ∀ ρ : HO.Env Γ, (elems N σ).map ((fun ρ : HO.Env (σ :: Γ) => vIdx N σ (Env.get ρ 0 h)) ∘ (fun d => (d, ρ))) =
        List.range (elems N σ).length := fun ρ => by
      rw [← map_vIdx_elems]; rfl
    simp only [this]
    rw [flatMap_const_list, envs_length]
  | σ :: Γ, i + 1, τ, h => by
    simp only [varVec, envs, List.map_flatMap, List.map_map]
    rw [varVec_eq N Γ i h, List.flatMap_map]
    congr 1
    funext ρ
    simp only [Function.comp_def, Env.get]
    rw [List.map_const']

/-! ## Blocks -/

/-- Cut a list into `n` blocks of length `k`. -/
def chunksN (k : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | n + 1, l => l.take k :: chunksN k n (l.drop k)

theorem chunksN_flatten (k : Nat) : ∀ (ls : List (List Nat)), (∀ l ∈ ls, l.length = k) →
    chunksN k ls.length ls.flatten = ls
  | [], _ => rfl
  | l :: ls, h => by
    have hl := h l List.mem_cons_self
    simp only [List.length_cons, List.flatten_cons, chunksN]
    rw [List.take_left' hl, List.drop_left' hl, chunksN_flatten k ls (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]

end Shallot.MacroPeg.Flat
