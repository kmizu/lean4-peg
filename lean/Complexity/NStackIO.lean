import Complexity.NStackSpec
import Complexity.ListIO

/-!
# Input for stack machines over numbers

`importP` turns the input of a list program (`initLists`: the bits on list `1`) into an encoded stack state: stack `0`
holds the bits as numbers `0`/`1`, the first bit on top (`nInit`), every other stack is empty (`import_runs`).
`NProg.compile_constOK`: translated programs push only `1` and `2`.
-/

namespace Complexity

variable {K : Nat}

/-- The initial state of a stack machine on input `w`: the bits on stack `0`, the first bit on top. -/
def nInit (K : Nat) (w : List Bool) : Lists K := fun i => if i.val = 0 then (w.map bitElem).reverse else []

/-- List `0` and list `1` of the translated program. -/
def i0 (h : 1 < K) : Fin (K + 1) := ⟨0, by omega⟩
def i1 (h : 1 < K) : Fin (K + 1) := ⟨1, by omega⟩

/-- Move the raw bits of list `1` onto list `0`, encoded. -/
def importP (h : 1 < K) : LProg (K + 1) :=
  .loop (i1 h) (· != 3)
    (.ite (i1 h) (· == 4) (.seq (.pop (i1 h)) (.push (i0 h) 2))
      (.seq (.pop (i1 h)) (.seq (.push (i0 h) 2) (.push (i0 h) 1))))

theorem encN_bitElem (b : Bool) : encN (bitElem b) = if b then [2, 1] else [2] := by
  cases b <;> rfl

section Import

variable (h : 1 < K) (w : List Bool)

theorem i0_ne_i1 : i0 h ≠ i1 h := by simp [i0, i1]

theorem lists_ext2 {k : Nat} {L L' : Lists k} (a b : Fin k) (ha : L a = L' a) (hb : L b = L' b)
    (ho : ∀ x, x ≠ a → x ≠ b → L x = L' x) : L = L' := by
  funext x
  by_cases hxa : x = a
  · subst hxa; exact ha
  by_cases hxb : x = b
  · subst hxb; exact hb
  exact ho x hxa hxb

theorem val_ne_of_ne {x : Fin (K + 1)} {n : Nat} {hn : n < K + 1} (hx : x ≠ ⟨n, hn⟩) : x.val ≠ n :=
  fun e => hx (Fin.ext e)

/-- After `m` bits: the first `n - m` raw bits remain, the last `m` are encoded on list `0`. -/
def importState (m : Nat) : Lists (K + 1) :=
  ((initLists (K + 1) w).set (i1 h) ((w.map bitElem).take (w.length - m))).set (i0 h)
    (encS ((w.map bitElem).drop (w.length - m)).reverse)

theorem importState_list0 (m : Nat) :
    importState h w m (i0 h) = encS ((w.map bitElem).drop (w.length - m)).reverse := by
  simp only [importState, Lists.set_same]

theorem importState_list1 (m : Nat) : importState h w m (i1 h) = (w.map bitElem).take (w.length - m) := by
  simp only [importState]
  rw [Lists.set_ne _ _ (i0_ne_i1 h).symm, Lists.set_same]

theorem importState_other (m : Nat) (x : Fin (K + 1)) (h0 : x ≠ i0 h) (h1 : x ≠ i1 h) : importState h w m x = [] := by
  simp only [importState]
  rw [Lists.set_ne _ _ h0, Lists.set_ne _ _ h1]
  simp [initLists, val_ne_of_ne (show x ≠ ⟨1, _⟩ from h1)]

theorem importState_zero : importState h w 0 = initLists (K + 1) w := by
  apply lists_ext2 (i0 h) (i1 h)
  · rw [importState_list0, Nat.sub_zero, List.drop_of_length_le (by simp)]; simp [initLists, i0, encS]
  · rw [importState_list1, Nat.sub_zero, List.take_of_length_le (by simp)]; simp [initLists, i1]
  · intro x h0 h1
    rw [importState_other h w 0 x h0 h1]
    simp [initLists, val_ne_of_ne (show x ≠ ⟨1, _⟩ from h1)]

theorem importState_end : importState h w w.length = encL (nInit K w) := by
  apply lists_ext2 (i0 h) (i1 h)
  · rw [importState_list0, Nat.sub_self, List.drop_zero]; simp [encL, nInit, i0]; omega
  · rw [importState_list1, Nat.sub_self, List.take_zero]; simp [encL, nInit, i1, encS]
  · intro x h0 h1
    rw [importState_other h w _ x h0 h1]
    simp only [encL, nInit, val_ne_of_ne (show x ≠ ⟨0, _⟩ from h0)]
    split <;> simp [encS]

theorem encS_length_bits : ∀ l : List Nat, (∀ e ∈ l, e ≤ 1) → (encS l).length ≤ 2 * l.length
  | [], _ => by simp [encS]
  | a :: l, hl => by
    have ha := hl a List.mem_cons_self
    have := encS_length_bits l (fun e he => hl e (List.mem_cons_of_mem _ he))
    have e : encS (a :: l) = encN a ++ encS l := rfl
    rw [e, List.length_append]
    simp only [encN, List.length_cons, List.length_replicate, List.length_cons]
    omega

theorem importState_lenOK {B : Nat} (hB : 2 * w.length + 2 ≤ B) (m : Nat) : LenOK B (importState h w m) := by
  intro x
  by_cases h0 : x = i0 h
  · subst h0
    rw [importState_list0]
    have hb : ∀ e ∈ ((w.map bitElem).drop (w.length - m)).reverse, e ≤ 1 := by
      intro e he
      simp only [List.mem_reverse] at he
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop he)
      cases b <;> simp [bitElem]
    have := encS_length_bits _ hb
    simp only [List.length_reverse, List.length_drop, List.length_map] at this
    omega
  by_cases h1 : x = i1 h
  · subst h1; rw [importState_list1]; simp; omega
  · rw [importState_other h w m x h0 h1]; simp; omega

theorem import_runs {B : Nat} (hB : 2 * w.length + 2 ≤ B) :
    Runs (LenOK B) (importP h) (initLists (K + 1) w) (encL (nInit K w)) ((w.length + 1) * 5) := by
  rw [← importState_zero h w, ← importState_end h w]
  have hQ := importState_lenOK h w hB
  have := runs_family (Q := LenOK B) (i := i1 h) (c := (· != 3)) (importState h w) w.length 4
    (fun m _ => hQ m)
    (fun m hm => by
      rw [importState_list1]
      have hne : (w.map bitElem).take (w.length - m) ≠ [] :=
        List.ne_nil_of_length_pos (by simp; omega)
      have := mt lastSym_eq_three.1 hne
      simpa using this)
    (by rw [importState_list1, Nat.sub_self]; rfl)
    (fun m hm => by
      obtain ⟨r, hr⟩ : ∃ r, w.length - m = r + 1 := ⟨w.length - m - 1, by omega⟩
      have hrl : r < w.length := by omega
      have hm1 : w.length - (m + 1) = r := by omega
      have htake : (w.map bitElem).take (r + 1) = (w.map bitElem).take r ++ [bitElem w[r]] := by
        rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hrl]; rfl
      have hdrop : ((w.map bitElem).drop r).reverse =
          ((w.map bitElem).drop (r + 1)).reverse ++ [bitElem w[r]] := by
        rw [List.drop_eq_getElem_cons (by simpa using hrl)]; simp
      have hL1 : importState h w m (i1 h) = (w.map bitElem).take r ++ [bitElem w[r]] := by
        rw [importState_list1, hr, htake]
      -- the state after appending `l` to list `0` and popping list `1`
      let Pl : List Nat → Lists (K + 1) := fun l =>
        ((importState h w m).set (i1 h) ((w.map bitElem).take r)).set (i0 h)
          (encS ((w.map bitElem).drop (r + 1)).reverse ++ l)
      have hPl : ∀ l, (encS ((w.map bitElem).drop (r + 1)).reverse ++ l) = encS ((w.map bitElem).drop r).reverse →
          Pl l = importState h w (m + 1) := fun l hl => by
        apply lists_ext2 (i0 h) (i1 h)
        · simp only [Pl, Lists.set_same]; rw [hl, importState_list0, hm1]
        · simp only [Pl]; rw [Lists.set_ne _ _ (i0_ne_i1 h).symm, Lists.set_same, importState_list1, hm1]
        · intro x h0 h1
          simp only [Pl]; rw [Lists.set_ne _ _ h0, Lists.set_ne _ _ h1, importState_other h w _ x h0 h1,
            importState_other h w _ x h0 h1]
      have hlen0 : ∀ l, l.length ≤ 2 → LenOK B (Pl l) := fun l hl => by
        apply lenOK_set (lenOK_set (hQ m) _ (by simp; omega))
        have hb : ∀ e ∈ ((w.map bitElem).drop (r + 1)).reverse, e ≤ 1 := by
          intro e he
          simp only [List.mem_reverse] at he
          obtain ⟨b, _, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop he)
          cases b <;> simp [bitElem]
        have := encS_length_bits _ hb
        simp only [List.length_reverse, List.length_drop, List.length_map] at this
        simp only [List.length_append]; omega
      have hpop : Runs (LenOK B) (.pop (i1 h)) (importState h w m) (Pl []) 1 := by
        have e : (importState h w m).set (i1 h) (importState h w m (i1 h)).dropLast = Pl [] := by
          apply lists_ext2 (i0 h) (i1 h)
          · simp only [Pl, Lists.set_same, List.append_nil]
            rw [Lists.set_ne _ _ (i0_ne_i1 h), importState_list0, hr]
          · simp only [Pl, Lists.set_same]
            rw [Lists.set_ne _ _ (i0_ne_i1 h).symm, Lists.set_same, hL1, List.dropLast_concat]
          · intro x h0 h1; simp only [Pl]; rw [Lists.set_ne _ _ h0, Lists.set_ne _ _ h1, Lists.set_ne _ _ h1]
        have := runs_pop (Q := LenOK B) (hQ m) (by rw [e]; exact hlen0 [] (by simp))
        rw [e] at this; exact this
      have hpush : ∀ l (e : Nat), l.length + 1 ≤ 2 →
          Runs (LenOK B) (.push (i0 h) e) (Pl l) (Pl (l ++ [e])) 1 := fun l e hl => by
        have eq : (Pl l).set (i0 h) (Pl l (i0 h) ++ [e]) = Pl (l ++ [e]) := by
          simp only [Pl, Lists.set_same, Lists.set_set_u, List.append_assoc]
        have := runs_push (Q := LenOK B) (i := i0 h) (e := e) (hlen0 l (by omega))
          (by rw [eq]; exact hlen0 _ (by simp; omega))
        rw [eq] at this; exact this
      have henc : encS ((w.map bitElem).drop r).reverse =
          encS ((w.map bitElem).drop (r + 1)).reverse ++ encN (bitElem w[r]) := by rw [hdrop, encS_snoc]
      cases hb : w[r] with
      | false =>
        have e := hPl [2] (by rw [henc, hb]; rfl)
        have r₂ := hpush [] 2 (by simp)
        rw [show ([] : List Nat) ++ [2] = [2] from rfl, e] at r₂
        refine (Runs.iteT (i := i1 h) (c := (· == 4))
          (q := .seq (.pop (i1 h)) (.seq (.push (i0 h) 2) (.push (i0 h) 1))) (hQ m) ?_ (hpop.seq r₂)).mono (by omega)
        rw [hL1, lastSym_append, hb]; rfl
      | true =>
        have e := hPl [2, 1] (by rw [henc, hb]; rfl)
        have r₂ := hpush [] 2 (by simp)
        have r₃ := hpush [2] 1 (by simp)
        rw [show ([] : List Nat) ++ [2] = [2] from rfl] at r₂
        rw [show ([2] : List Nat) ++ [1] = [2, 1] from rfl, e] at r₃
        refine (Runs.iteF (i := i1 h) (c := (· == 4)) (p := .seq (.pop (i1 h)) (.push (i0 h) 2))
          (hQ m) ?_ (hpop.seq (r₂.seq r₃))).mono (by omega)
        rw [hL1, lastSym_append, hb]; rfl) w.length 0 (by omega)
  exact this.mono (by omega)

end Import

theorem NPrim.compile_constOK (a : NPrim K) : a.compile.ConstOK 3 := by
  cases a <;> simp [NPrim.compile, LProg.ConstOK, skipP, onesOut, onesBack, moveTop]

theorem NProg.compile_constOK : ∀ p : NProg K, p.compile.ConstOK 3
  | .prim a => a.compile_constOK
  | .seq p q => ⟨p.compile_constOK, q.compile_constOK⟩
  | .ite _ _ p q => ⟨p.compile_constOK, q.compile_constOK⟩
  | .loop _ _ p => p.compile_constOK
  | .halt _ => trivial

theorem importP_constOK (h : 1 < K) : (importP h).ConstOK 3 := by
  simp [importP, LProg.ConstOK]

theorem NExec.mono {Q Q' : Lists K → Prop} (hQ : ∀ S, Q S → Q' S) {p : NProg K} {S : Lists K} {t : Nat}
    {o : LOutcome K} (h : NExec Q p S t o) : NExec Q' p S t o := by
  induction h with
  | prim h₁ h₂ => exact .prim (hQ _ h₁) (hQ _ h₂)
  | halt h₁ => exact .halt (hQ _ h₁)
  | seqC _ _ ih₁ ih₂ => exact .seqC ih₁ ih₂
  | seqS _ ih => exact .seqS ih
  | iteT h₁ hc _ ih => exact .iteT (hQ _ h₁) hc ih
  | iteF h₁ hc _ ih => exact .iteF (hQ _ h₁) hc ih
  | loopF h₁ hc => exact .loopF (hQ _ h₁) hc
  | loopC h₁ hc _ _ ih₁ ih₂ => exact .loopC (hQ _ h₁) hc ih₁ ih₂
  | loopS h₁ hc _ ih => exact .loopS (hQ _ h₁) hc ih

theorem NFits.mono {B B' : Nat} (hB : B ≤ B') {S : Lists K} (h : NFits B S) : NFits B' S :=
  ⟨by have := h.1; omega, fun i => by have := h.2 i; omega⟩

/-- **Stack machines decide in list-program time**: the import, then the translated program. -/
theorem nprog_lexec (h : 1 < K) (p : NProg K) (w : List Bool) {B t : Nat} {b : Bool} {S' : Lists K}
    (hB : 2 * w.length + 2 ≤ B) (hx : NExec (NFits B) p (nInit K w) t (.stop b S')) :
    ∃ t', t' ≤ (w.length + 1) * 5 + t * ncost B ∧
      LExec (LenOK B) (.seq (importP h) p.compile) (initLists (K + 1) w) t' (.stop b (encL S')) := by
  obtain ⟨t₀, ht₀, x₀⟩ := import_runs h w hB
  obtain ⟨t₁, ht₁, x₁⟩ := nexec_compile (fun _ hS => hS) hx
  exact ⟨t₀ + t₁, by omega, .seqC x₀ x₁⟩

theorem nprog_constOK (h : 1 < K) (p : NProg K) : (LProg.seq (importP h) p.compile).ConstOK 3 :=
  ⟨importP_constOK h, p.compile_constOK⟩

end Complexity
