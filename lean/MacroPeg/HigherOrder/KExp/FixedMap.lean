import MacroPeg.HigherOrder.KExp.UniformHard

/-!
# The input map of a fixed grammar is computable in polynomial time

For a fixed grammar `g` and start `s`, `fixedMap g s` sends the bits `w` (read as 4-bit tokens, each token a character
by `tokChar`) to the bits of the uniform instance `serIn g s …`. Output templates cannot find the 4-bit token
boundaries (their conditions only compare counters), so this is a direct list program `fixLP`: reverse the input,
write the constant prefix, then repeatedly read up to four bits and write the serialized character, and finally the
end of the string.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.Tableau

/-- The map from the input of a fixed grammar to the input of the uniform problem. -/
def fixedMap (g : HGrammar) (s : HExp) (w : List Bool) : List Bool :=
  toBits (serIn g s ((ofBits w).map tokChar))

/-! ## The program -/

/-- Push the constants `es` onto list `i`, in order. -/
def pushL (i : Fin 4) : List Nat → LProg 4
  | [] => skipP i
  | e :: es => .seq (.push i e) (pushL i es)

/-- The token read from four bits (most significant first). -/
def tokOf : List Bool → Nat
  | [b₃, b₂, b₁, b₀] => bitsTok b₃ b₂ b₁ b₀
  | _ => 0

/-- The output bits of one token. -/
def emitL (bs : List Bool) : List Nat := (toBits (charTok (tokOf bs))).map bitElem

/-- Read up to `r` more bits from list `3` (bits read so far: `acc`); if all were there, write the token. -/
def rd : Nat → List Bool → LProg 4
  | 0, acc => pushL 2 (emitL acc)
  | r + 1, acc => .ite 3 (· == 5) (.seq (.pop 3) (rd r (acc ++ [true])))
      (.ite 3 (· == 4) (.seq (.pop 3) (rd r (acc ++ [false]))) (skipP 3))

/-- The constant prefix: rule types, rule bodies, start expression. -/
def preT (g : HGrammar) (s : HExp) : List Nat :=
  serTys (g.rules.map HRule.ty) ++ (serBodies (g.rules.map HRule.body) ++ serE s)

def fixLP (g : HGrammar) (s : HExp) : LProg 4 :=
  .seq (moveAll 1 3) (.seq (pushL 2 ((toBits (preT g s)).map bitElem))
    (.seq (.loop 3 (· != 3) (rd 4 [])) (pushL 2 ((toBits [0]).map bitElem))))

/-! ## States -/

/-- The state: output `out` on list `2`, the unread bits `u` on list `3` (first bit on top). -/
def St (u : List Bool) (out : List Nat) : Lists 4 :=
  fun j => if j.val = 2 then out else if j.val = 3 then (u.map bitElem).reverse else []

theorem St_two (u : List Bool) (out : List Nat) : St u out 2 = out := rfl
theorem St_three (u : List Bool) (out : List Nat) : St u out 3 = (u.map bitElem).reverse := rfl

theorem St_set2 (u : List Bool) (out l : List Nat) : (St u out).set 2 l = St u l := by
  funext j
  unfold St Lists.set
  by_cases h : j.val = 2
  · have : j = 2 := Fin.ext h
    subst this; simp
  · have : j ≠ 2 := fun e => h (by rw [e]; rfl)
    simp [this, h]

theorem St_pop (b : Bool) (u : List Bool) (out : List Nat) :
    (St (b :: u) out).set 3 (St (b :: u) out 3).dropLast = St u out := by
  funext j
  unfold Lists.set
  by_cases h : j.val = 3
  · have : j = 3 := Fin.ext h
    subst this
    simp only [if_true]
    rw [St_three, St_three]
    simp
  · have : j ≠ 3 := fun e => h (by rw [e]; rfl)
    simp only [this, if_false]
    simp [St, h]

theorem lenOK_St {B : Nat} {u : List Bool} {out : List Nat} (h1 : out.length + 2 ≤ B) (h2 : u.length + 2 ≤ B) :
    LenOK B (St u out) := by
  intro j
  unfold St
  split
  · exact h1
  split
  · simpa using h2
  · simp; omega

/-! ## Pushing constants -/

theorem pushL_spec {B : Nat} (i : Fin 4) : ∀ (es : List Nat) (L : Lists 4), LenOK B L →
    (L i ++ es).length + 2 ≤ B → Runs (LenOK B) (pushL i es) L (L.set i (L i ++ es)) (es.length + 1)
  | [], L, hL, _ => by
    simp only [List.append_nil, Lists.set_get_self]
    exact runs_skip i hL
  | e :: es, L, hL, hb => by
    have hL1 : LenOK B (L.set i (L i ++ [e])) := hL.set i (by simp at hb ⊢; omega)
    have h1 := runs_push (Q := LenOK B) (i := i) (e := e) hL hL1
    have h2 := pushL_spec i es _ hL1 (by simp at hb ⊢; omega)
    simp only [Lists.set_same, Lists.set_set_u, List.append_assoc, List.singleton_append] at h2
    have := h1.seq h2
    simp only [List.length_cons] at this ⊢
    exact this.mono (by omega)

/-! ## Reading one token -/

theorem toBits_length : ∀ x : List Nat, (toBits x).length = 4 * x.length
  | [] => rfl
  | t :: x => by
    show (tokBits t ++ toBits x).length = _
    rw [List.length_append, toBits_length x]
    simp [tokBits]; omega

theorem serNat_length : ∀ n : Nat, (serNat n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [serNat, serNat_length n]

theorem tokChar_le (t : Nat) : (tokChar t).toNat ≤ 124 := by
  unfold tokChar; split <;> decide

theorem emitL_length (bs : List Bool) : (emitL bs).length ≤ 504 := by
  have h := tokChar_le (tokOf bs)
  simp only [emitL, List.length_map, toBits_length, charTok, serChar, List.length_cons, serNat_length]
  omega

theorem lastSym_St (b : Bool) (u : List Bool) (out : List Nat) :
    lastSym (St (b :: u) out 3) = bitElem b + 4 := by
  rw [St_three]; simp [lastSym_append]

theorem lastSym_St_nil (out : List Nat) : lastSym (St [] out 3) = 3 := rfl

theorem rd_time1 (r : Nat) : 1 + (3 * r + 510) + 1 ≤ 3 * (r + 1) + 510 := by omega
theorem rd_time2 (r : Nat) : 1 + (3 * r + 510) + 1 + 1 ≤ 3 * (r + 1) + 510 := by omega

theorem rd_spec {B : Nat} : ∀ (r : Nat) (acc u : List Bool) (out : List Nat), out.length + 506 ≤ B →
    u.length + 2 ≤ B → Runs (LenOK B) (rd r acc) (St u out)
      (St (u.drop r) (out ++ if r ≤ u.length then emitL (acc ++ u.take r) else [])) (3 * r + 510)
  | 0, acc, u, out, h1, h2 => by
    have hE := emitL_length acc
    have := pushL_spec (B := B) 2 (emitL acc) (St u out) (lenOK_St (by omega) h2)
      (by rw [St_two]; simp; omega)
    rw [St_two, St_set2] at this
    simp only [List.drop_zero, Nat.zero_le, if_true, List.take_zero, List.append_nil]
    exact this.mono (by omega)
  | r + 1, acc, [], out, h1, h2 => by
    have hL : LenOK B (St [] out) := lenOK_St (by omega) h2
    have := Runs.iteF (c := (· == 5)) (p := .seq (.pop 3) (rd r (acc ++ [true]))) hL
      (by rw [lastSym_St_nil]; rfl)
      (Runs.iteF (c := (· == 4)) (p := .seq (.pop 3) (rd r (acc ++ [false]))) hL
        (by rw [lastSym_St_nil]; rfl) (runs_skip 3 hL))
    simp only [List.drop_nil, List.length_nil, show ¬ (r + 1 ≤ 0) by omega, if_false, List.append_nil]
    exact this.mono (by omega)
  | r + 1, acc, b :: u, out, h1, h2 => by
    have hL : LenOK B (St (b :: u) out) := lenOK_St (by omega) h2
    have hL' : LenOK B (St u out) := lenOK_St (by omega) (by simp at h2; omega)
    have hpop := runs_pop (Q := LenOK B) (i := 3) hL (by rw [St_pop]; exact hL')
    rw [St_pop] at hpop
    have e : (if r + 1 ≤ (b :: u).length then emitL (acc ++ (b :: u).take (r + 1)) else []) =
        (if r ≤ u.length then emitL (acc ++ [b] ++ u.take r) else []) := by
      simp [List.take_succ_cons, List.append_assoc]
    simp only [List.drop_succ_cons, e]
    cases b with
    | true =>
      have ht : 1 + (3 * r + 510) + 1 ≤ 3 * (r + 1) + 510 := rd_time1 r
      have hr := rd_spec r (acc ++ [true]) u out h1 (by simp at h2; omega)
      have hs := hpop.seq hr
      have hx := Runs.iteT (c := (· == 5)) (q := .ite 3 (· == 4) (.seq (.pop 3) (rd r (acc ++ [false]))) (skipP 3)) hL
        (by rw [lastSym_St]; rfl) hs
      exact Runs.mono hx ht
    | false =>
      have ht : 1 + (3 * r + 510) + 1 + 1 ≤ 3 * (r + 1) + 510 := rd_time2 r
      refine Runs.mono (T := 1 + (3 * r + 510) + 1 + 1) ?_ ht
      exact Runs.iteF (c := (· == 5)) (p := .seq (.pop 3) (rd r (acc ++ [true]))) hL
        (by rw [lastSym_St]; rfl)
        (Runs.iteT (c := (· == 4)) (q := skipP 3) hL (by rw [lastSym_St]; rfl)
          (hpop.seq (rd_spec r (acc ++ [false]) u out h1 (by simp at h2; omega))))

/-! ## The token loop -/

/-- The output bits of the characters of the tokens of `u`. -/
def gOut (u : List Bool) : List Nat := (toBits ((ofBits u).flatMap charTok)).map bitElem

theorem gOut_cons4 (b₃ b₂ b₁ b₀ : Bool) (u : List Bool) :
    gOut (b₃ :: b₂ :: b₁ :: b₀ :: u) = emitL [b₃, b₂, b₁, b₀] ++ gOut u := by
  simp only [gOut, emitL, ofBits, tokOf, List.flatMap_cons, toBits, List.flatMap_append, List.map_append]

theorem gOut_short : ∀ u : List Bool, u.length < 4 → gOut u = []
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => absurd h (by simp)

theorem charTok_length (t : Nat) : (charTok t).length ≤ 126 := by
  have := tokChar_le t
  simp only [charTok, serChar, List.length_cons, serNat_length]; omega

theorem flatMap_charTok_length : ∀ l : List Nat, (l.flatMap charTok).length ≤ 126 * l.length
  | [] => by simp
  | t :: l => by
    have h1 := flatMap_charTok_length l
    have h2 := charTok_length t
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

theorem gOut_length (u : List Bool) : (gOut u).length ≤ 504 * u.length := by
  have h1 := flatMap_charTok_length (ofBits u)
  have h2 := ofBits_length_le u
  simp only [gOut, List.length_map, toBits_length]
  omega

theorem loop_spec {B : Nat} (Tg : List Nat) (n : Nat) (hB : Tg.length + 506 ≤ B) (hn : n + 2 ≤ B) :
    ∀ (u : List Bool) (out : List Nat), out ++ gOut u = Tg → u.length ≤ n →
      Runs (LenOK B) (.loop 3 (· != 3) (rd 4 [])) (St u out) (St [] Tg) ((n + 1) * (522 + 1)) := by
  intro u out hT hu
  let I : Lists 4 → Prop := fun L => ∃ u out, L = St u out ∧ out ++ gOut u = Tg ∧ u.length ≤ n
  have hQ : ∀ L, I L → LenOK B L := by
    rintro L ⟨u, out, rfl, hT, hu⟩
    have : out.length ≤ Tg.length := by rw [← hT]; simp
    exact lenOK_St (by omega) (by omega)
  have hbody : ∀ L, I L → (· != 3) (lastSym (L 3)) = true →
      ∃ L', Runs (LenOK B) (rd 4 []) L L' 522 ∧ I L' ∧ (L' 3).length < (L 3).length := by
    rintro L ⟨u, out, rfl, hT, hu⟩ hc
    have hol : out.length ≤ Tg.length := by rw [← hT]; simp
    have hr := rd_spec (B := B) 4 [] u out (by omega) (by omega)
    refine ⟨_, hr, ?_⟩
    rcases u with _ | ⟨b₃, _ | ⟨b₂, _ | ⟨b₁, _ | ⟨b₀, u'⟩⟩⟩⟩
    · exact absurd hc (by rw [lastSym_St_nil]; decide)
    all_goals first
      | (refine ⟨⟨u', out ++ emitL [b₃, b₂, b₁, b₀], ?_, ?_, ?_⟩, ?_⟩
         · simp
         · rw [← hT, gOut_cons4]; simp
         · simp at hu; omega
         · simp [St_three])
      | (refine ⟨⟨[], out, ?_, ?_, ?_⟩, ?_⟩
         · simp
         · rw [← hT, gOut_short _ (by simp)]; simp [gOut_short]
         · simp
         · simp [St_three])
  obtain ⟨L', hR, ⟨u', out', rfl, hT', _⟩, hc⟩ := runs_loop (i := 3) (c := (· != 3)) (p := rd 4 [])
    (I := I) (μ := fun L => (L 3).length) (T := 522) hQ hbody (St u out) ⟨u, out, rfl, hT, hu⟩
  have hu' : u' = [] := by
    have : lastSym (St u' out' 3) = 3 := by simpa using hc
    have := lastSym_eq_three.1 this
    rw [St_three] at this
    simpa using this
  subst hu'
  have : out' = Tg := by rw [← hT']; simp [gOut_short]
  subst this
  refine hR.mono ?_
  simp only [St_three, List.length_reverse, List.length_map]
  exact Nat.mul_le_mul_right _ (by omega)

/-! ## The whole program -/

theorem lenOK_init4 (w : List Bool) {B : Nat} (hB : w.length + 2 ≤ B) : LenOK B (initLists 4 w) := by
  intro j
  simp only [initLists]
  split
  · simpa using hB
  · simp; omega

theorem init_moveAll (w : List Bool) : (initLists 4 w).moveAll 1 3 = St w [] := by
  have v3 : ((3 : Fin 4) : Nat) = 3 := rfl
  funext j
  unfold Lists.moveAll Lists.set St initLists
  match j with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => simp [Fin.ext_iff, v3]

theorem constOK_pushL (i : Fin 4) : ∀ es : List Nat, (∀ e ∈ es, e < 2) → (pushL i es).ConstOK 2
  | [], _ => by simp [pushL, skipP, LProg.ConstOK]
  | e :: es, h => ⟨h e List.mem_cons_self, constOK_pushL i es (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem bitElem_lt (bs : List Bool) : ∀ e ∈ bs.map bitElem, e < 2 := by
  intro e he
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 he
  cases b <;> decide

theorem constOK_rd : ∀ (r : Nat) (acc : List Bool), (rd r acc).ConstOK 2
  | 0, acc => constOK_pushL 2 _ (bitElem_lt _)
  | r + 1, acc => ⟨⟨trivial, constOK_rd r _⟩, ⟨trivial, constOK_rd r _⟩, by simp [skipP, LProg.ConstOK]⟩

theorem fixLP_constOK (g : HGrammar) (s : HExp) : (fixLP g s).ConstOK 2 :=
  ⟨constOK_moveAll _ _, constOK_pushL 2 _ (bitElem_lt _), constOK_rd 4 [], constOK_pushL 2 _ (bitElem_lt _)⟩

theorem fixedMap_eq (g : HGrammar) (s : HExp) (w : List Bool) :
    (fixedMap g s w).map bitElem = ((toBits (preT g s)).map bitElem ++ gOut w) ++ (toBits [0]).map bitElem := by
  simp only [fixedMap, serIn, serStr_eq, gOut, preT, toBits, List.flatMap_map, List.flatMap_append, List.map_append,
    List.append_assoc]
  rfl

section Bounds

variable (g : HGrammar) (s : HExp)

def fP : Nat := ((toBits (preT g s)).map bitElem).length
def fSpace (n : Nat) : Nat := fP g s + 504 * n + n + 520
def fTime (n : Nat) : Nat := (n + 1) * 3 + (fP g s + 1) + (n + 1) * (522 + 1) + 5

theorem fSpace_poly : IsPoly (fSpace g s) := by
  unfold fSpace
  exact isPoly_add (isPoly_add (isPoly_add (isPoly_const _) (isPoly_mul (isPoly_const 504) isPoly_id)) isPoly_id)
    (isPoly_const _)

theorem fTime_poly : IsPoly (fTime g s) := by
  unfold fTime
  have hn1 : IsPoly (fun n => n + 1) := isPoly_add isPoly_id (isPoly_const 1)
  exact isPoly_add (isPoly_add (isPoly_add (isPoly_mul hn1 (isPoly_const 3)) (isPoly_const _))
    (isPoly_mul hn1 (isPoly_const _))) (isPoly_const _)

end Bounds

theorem fix_runs (g : HGrammar) (s : HExp) (w : List Bool) :
    ∃ t L', t ≤ fTime g s w.length ∧ LExec (LenOK (fSpace g s w.length)) (fixLP g s) (initLists 4 w) t (.cont L') ∧
      L' ⟨0, by omega⟩ = [] ∧ L' 2 = (fixedMap g s w).map bitElem := by
  let n := w.length
  let B := fSpace g s n
  let P := (toBits (preT g s)).map bitElem
  let Tg := P ++ gOut w
  have hP : P.length = fP g s := rfl
  have hBv : B = fP g s + 504 * n + n + 520 := rfl
  have hn : w.length = n := rfl
  have hL1 : initLists 4 w 1 = w.map bitElem := rfl
  have hL3 : initLists 4 w 3 = [] := rfl
  have hG := gOut_length w
  have hTg : Tg.length + 506 ≤ B := by
    simp only [Tg, List.length_append]; omega
  have h0 : LenOK B (initLists 4 w) := lenOK_init4 w (by omega)
  have R1 := runs_moveAll' (i := 1) (j := 3) (by decide) h0
    (by rw [hL1, hL3]; simp; omega)
  rw [init_moveAll] at R1
  have R2 := pushL_spec (B := B) 2 P (St w []) (lenOK_St (by simp; omega) (by omega))
    (by rw [St_two]; simp only [List.nil_append]; omega)
  rw [St_two, St_set2, List.nil_append] at R2
  have R3 := loop_spec (B := B) Tg n hTg (by omega) w P rfl (Nat.le_refl _)
  have R4 := pushL_spec (B := B) 2 ((toBits [0]).map bitElem) (St [] Tg) (lenOK_St (by omega) (by simp; omega))
    (by rw [St_two]; simp [toBits, tokBits]; omega)
  rw [St_two, St_set2] at R4
  obtain ⟨t, ht, hx⟩ := R1.seq (R2.seq (R3.seq R4))
  refine ⟨t, _, ?_, hx, rfl, ?_⟩
  · have e1 : ((initLists 4 w 1).length + 1) * 3 = (n + 1) * 3 := by rw [hL1]; simp [n]
    have e2 : ((toBits [0]).map bitElem).length + 1 = 5 := rfl
    rw [e1, e2, hP] at ht
    show t ≤ (n + 1) * 3 + (fP g s + 1) + (n + 1) * (522 + 1) + 5
    omega
  · rw [St_two, fixedMap_eq]

theorem fixedMap_polytime (g : HGrammar) (s : HExp) : PolyTimeComputable (fixedMap g s) :=
  lm_polytime (k := 4) (by decide) 2 (by decide) (fixLP g s) 2 (by decide) (fixLP_constOK g s) (fixedMap g s)
    (fSpace g s) (fTime g s) (fSpace_poly g s) (fTime_poly g s) (fun w => fix_runs g s w)

end Shallot.MacroPeg.KExp
