import Lean
import Complexity.TqbfResolve
import Complexity.QbfCodec
import Complexity.TqbfEvalSpec

namespace Complexity

variable {k : Nat}

namespace RsResolveSpec

open Lean in
syntax "rs_ndis " ident " [" ident,* "]" : tactic
open Lean in
macro_rules
  | `(tactic| rs_ndis $hd [ $vs,* ]) => do
    let vs := vs.getElems
    let mut tacs : Array (TSyntax `tactic) := #[]
    for a in vs do
      for b in vs do
        if a.getId != b.getId then
          let nm := mkIdent (Name.mkSimple s!"n_{a.getId}_{b.getId}")
          tacs := tacs.push (← `(tactic| have $nm:ident : ($a = $b ↔ False) :=
            iff_false_intro (fun h => by subst h; simp at $hd:ident)))
    `(tactic| ($[$tacs]*))

open Lean in
set_option hygiene false in
syntax "rs_slk " "[" ident,* "]" "[" term,* "]" : tactic
open Lean in
set_option hygiene false in
macro_rules
  | `(tactic| rs_slk [ $vs,* ] [ $ts,* ]) => do
    let vs := vs.getElems
    let mut args : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    for a in vs do
      for b in vs do
        if a.getId != b.getId then
          let nm := mkIdent (Name.mkSimple s!"n_{a.getId}_{b.getId}")
          args := args.push (← `(Lean.Parser.Tactic.simpLemma| $nm:ident))
    for t in ts.getElems do
      args := args.push (← `(Lean.Parser.Tactic.simpLemma| $t:term))
    `(tactic| simp [Lists.set, $args,*])

open Lean in
set_option hygiene false in
syntax "rs_ext " "[" ident,* "]" : tactic
open Lean in
set_option hygiene false in
macro_rules
  | `(tactic| rs_ext [ $vs,* ]) => do
    let vs := vs.getElems
    let mut args : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    for a in vs do
      for b in vs do
        if a.getId != b.getId then
          let nm := mkIdent (Name.mkSimple s!"n_{a.getId}_{b.getId}")
          args := args.push (← `(Lean.Parser.Tactic.simpLemma| $nm:ident))
    let y := mkIdent `rs_y
    let toSeq : TSyntax `tactic → TSyntax ``Lean.Parser.Tactic.tacticSeq := fun t =>
      ⟨mkNode ``Lean.Parser.Tactic.tacticSeq1Indented #[mkNullNode #[t.raw]]⟩
    let mut tac : TSyntax `tactic ← `(tactic| simp [Lists.set, List.replicate_succ, Tok.one, Tok.sep, Tok.fin, $args,*, *])
    for v in vs.reverse do
      let hn := mkIdent (Name.mkSimple s!"hy_{v.getId}")
      let sq := toSeq tac
      tac ← `(tactic| (by_cases $hn:ident : $y = $v
                       · simp [Lists.set, List.replicate_succ, Tok.one, Tok.sep, Tok.fin, $args,*, $hn:ident, *]
                       · $sq))
    let sq := toSeq tac
    `(tactic| (funext $y:ident; ($sq)))

theorem set_set_same (L : Lists k) (i : Fin k) (a b : List Nat) : (L.set i a).set i b = L.set i b := by
  funext y; by_cases h : y = i <;> simp [Lists.set, h]

/-- Runs within some number of steps. -/
def RE (B : Nat) (p : LProg k) (L L' : Lists k) : Prop := ∃ T, Runs (LenOK B) p L L' T

theorem LExec.last {Q : Lists k → Prop} {p : LProg k} {L L' : Lists k} {t : Nat}
    (h : LExec Q p L t (.cont L')) : Q L' := by
  generalize ho : LOutcome.cont L' = o at h
  induction h with
  | push _ h2 => cases ho; exact h2
  | pop _ h2 => cases ho; exact h2
  | copy _ _ h2 => cases ho; exact h2
  | halt _ => cases ho
  | seqC _ _ _ ih2 => exact ih2 ho
  | seqS _ ih => cases ho
  | iteT _ _ _ ih => exact ih ho
  | iteF _ _ _ ih => exact ih ho
  | loopF h1 _ => cases ho; exact h1
  | loopC _ _ _ _ _ ih2 => exact ih2 ho
  | loopS _ _ _ ih => cases ho

theorem RE.last {B : Nat} {p : LProg k} {L L' : Lists k} (h : RE B p L L') : LenOK B L' :=
  let ⟨_, _, _, hx⟩ := h; LExec.last hx

theorem RE.seq {B : Nat} {p q : LProg k} {L L₁ L₂ : Lists k} (h₁ : RE B p L L₁) (h₂ : RE B q L₁ L₂) :
    RE B (.seq p q) L L₂ :=
  let ⟨_, h₁⟩ := h₁; let ⟨_, h₂⟩ := h₂; ⟨_, h₁.seq h₂⟩

theorem RE.iteT {B : Nat} {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L L' : Lists k} (hq : LenOK B L)
    (hc : c (lastSym (L i)) = true) (h : RE B p L L') : RE B (.ite i c p q) L L' :=
  let ⟨_, h⟩ := h; ⟨_, h.iteT hq hc⟩

theorem RE.iteF {B : Nat} {i : Fin k} {c : Nat → Bool} {p q : LProg k} {L L' : Lists k} (hq : LenOK B L)
    (hc : c (lastSym (L i)) = false) (h : RE B q L L') : RE B (.ite i c p q) L L' :=
  let ⟨_, h⟩ := h; ⟨_, h.iteF hq hc⟩

theorem RE.loopF {B : Nat} {i : Fin k} {c : Nat → Bool} {p : LProg k} {L : Lists k} (hq : LenOK B L)
    (hc : c (lastSym (L i)) = false) : RE B (.loop i c p) L L :=
  ⟨1, 1, Nat.le_refl _, .loopF hq hc⟩

theorem RE.loopC {B : Nat} {i : Fin k} {c : Nat → Bool} {p : LProg k} {L L₁ L₂ : Lists k} (hq : LenOK B L)
    (hc : c (lastSym (L i)) = true) (h₁ : RE B p L L₁) (h₂ : RE B (.loop i c p) L₁ L₂) :
    RE B (.loop i c p) L L₂ := by
  obtain ⟨_, t₁, ht₁, hx₁⟩ := h₁
  obtain ⟨_, t₂, ht₂, hx₂⟩ := h₂
  exact ⟨_, t₁ + 1 + t₂, Nat.le_refl _, .loopC hq hc hx₁ hx₂⟩

theorem RE.skip {B : Nat} (i : Fin k) {L : Lists k} (hL : LenOK B L) : RE B (skipP i) L L :=
  ⟨_, runs_skip i hL⟩

theorem RE.push {B : Nat} {i : Fin k} {e : Nat} {L : Lists k} (hL : LenOK B L) (hb : (L i).length + 3 ≤ B) :
    RE B (.push i e) L (L.set i (L i ++ [e])) := by
  refine ⟨_, runs_push hL ?_⟩
  intro x
  by_cases hx : x = i
  · subst hx; simp; omega
  · rw [Lists.set_ne _ _ hx]; exact hL x

theorem RE.pop {B : Nat} {i : Fin k} {l : List Nat} {e : Nat} {L : Lists k} (hL : LenOK B L)
    (hi : L i = l ++ [e]) : RE B (.pop i) L (L.set i l) := by
  have := runs_pop (Q := LenOK B) (i := i) (L := L) hL ?_
  · rw [hi] at this; simp at this; exact ⟨_, this⟩
  · intro x
    by_cases hx : x = i
    · subst hx; have := hL x; simp [hi] at this ⊢; omega
    · rw [Lists.set_ne _ _ hx]; exact hL x

theorem RE.move {B : Nat} {i j : Fin k} (hij : i ≠ j) {l : List Nat} {e : Nat} {L : Lists k} (hL : LenOK B L)
    (hi : L i = l ++ [e]) (hb : (L j).length + 3 ≤ B) :
    RE B (moveTop i j) L ((L.set j (L j ++ [e])).set i l) := by
  have h1 : LenOK B (L.set j (L j ++ (L i).getLast?.toList)) := by
    intro x
    by_cases hx : x = j
    · subst hx; simp [hi]; omega
    · rw [Lists.set_ne _ _ hx]; exact hL x
  have h2 : LenOK B (L.moveTop i j) := by
    intro x
    by_cases hx : x = i
    · subst hx; rw [moveTop_i]; have := hL x; simp [hi] at this ⊢; omega
    · by_cases hx2 : x = j
      · subst hx2; rw [moveTop_j hij]; simp [hi]; omega
      · rw [moveTop_other hx hx2]; exact hL x
  have := runs_moveTop (Q := LenOK B) hij hL h1 h2
  have e : L.moveTop i j = (L.set j (L j ++ [e])).set i l := by
    simp [Lists.moveTop, hi, Lists.set_ne _ _ hij]
  rw [e] at this
  exact ⟨_, this⟩

theorem RE.eq {B : Nat} {p : LProg k} {L L' L'' : Lists k} (h : RE B p L L') (e : L' = L'') : RE B p L L'' := e ▸ h


theorem rMoveWhile {B : Nat} {i j : Fin k} (hij : i ≠ j) (c : Nat → Bool) :
    ∀ (P : List Nat), (∀ t ∈ P, c (t + 4) = true) → ∀ (L : Lists k) (R : List Nat), LenOK B L →
      L i = R ++ P.reverse → c (lastSym R) = false → (L j).length + P.length + 2 ≤ B →
      RE B (.loop i c (moveTop i j)) L ((L.set j (L j ++ P)).set i R) := by
  intro P
  induction P with
  | nil =>
    intro _ L R hL hi hc _
    simp at hi
    have : (L.set j (L j ++ [])).set i R = L := by
      funext y; by_cases h : y = i
      · subst h; simp [Lists.set, hi]
      · simp [Lists.set, h]; intro h2; subst h2; rfl
    rw [this]
    exact RE.loopF hL (by rw [hi]; exact hc)
  | cons p P ih =>
    intro hP L R hL hi hc hb
    have hi' : L i = (R ++ P.reverse) ++ [p] := by simpa using hi
    have hcp : c (lastSym (L i)) = true := by
      rw [hi', lastSym_append]; exact hP p (by simp)
    have hm := RE.move hij hL hi' (by simp at hb; omega)
    have hL1 := hm.last
    have h1 := ih (fun t ht => hP t (by simp [ht])) _ R hL1
      (by simp [Lists.set]) hc (by simp [Lists.set, Ne.symm hij] at hb ⊢; omega)
    refine RE.loopC hL hcp hm (h1.eq ?_)
    funext y
    by_cases h1 : y = i
    · subst h1; simp [Lists.set]
    · by_cases h2 : y = j
      · subst h2; simp [Lists.set, hij, Ne.symm hij]
      · simp [Lists.set, h1, h2]

theorem rClear {B : Nat} (i : Fin k) : ∀ (n : Nat) (L : Lists k), (L i).length = n → LenOK B L →
    RE B (clearP i) L (L.set i []) := by
  intro n
  induction n with
  | zero =>
    intro L hn hL
    have h0 : L i = [] := List.length_eq_zero_iff.1 hn
    have : L.set i [] = L := by
      funext y; by_cases h : y = i
      · subst h; simp [Lists.set, h0]
      · simp [Lists.set, h]
    rw [this]
    exact RE.loopF hL (by rw [h0]; rfl)
  | succ n ih =>
    intro L hn hL
    obtain ⟨l, e, hle⟩ : ∃ l e, L i = l ++ [e] := by
      rcases List.eq_nil_or_concat (L i) with h | ⟨l, e, h⟩
      · simp [h] at hn
      · exact ⟨l, e, by simpa using h⟩
    have hp := RE.pop hL hle
    have h1 := ih (L.set i l) (by simp [hle] at hn ⊢; omega) hp.last
    refine RE.loopC hL (by rw [hle, lastSym_append]; rfl) hp (h1.eq ?_)
    exact set_set_same _ _ _ _


theorem encName_split (y : Name) : ∃ P, encName y = P ++ [3] ∧ ∀ t ∈ P, t = 1 ∨ t = 2 := by
  refine ⟨y.flatMap (fun n => List.replicate n Tok.one ++ [Tok.sep]), ?_, ?_⟩
  · simp [encName, Tok.fin]
  · intro t ht
    simp [List.mem_flatMap, List.mem_append, List.mem_replicate] at ht
    obtain ⟨n, _, h⟩ := ht
    rcases h with ⟨_, h⟩ | h
    · left; simpa [Tok.one] using h
    · right; simpa [Tok.sep] using h

theorem rReadName {B : Nat} {mt x : Fin k} (hmx : mt ≠ x) {L : Lists k} (hL : LenOK B L) (y : Name) (R : List Nat)
    (hmt : L mt = R ++ (encName y).reverse) (hb : (L x).length + (encName y).length + 2 ≤ B) :
    RE B (readNameP mt x) L ((L.set x (L x ++ encName y)).set mt R) := by
  obtain ⟨P, hP, hP12⟩ := encName_split y
  rw [hP] at hmt hb ⊢
  have hmt' : L mt = (R ++ [3]) ++ P.reverse := by simpa using hmt
  have h1 := rMoveWhile (B := B) hmx (fun s => s == Tok.one + 4 || s == Tok.sep + 4) P
    (by intro t ht; rcases hP12 t ht with h | h <;> simp [h, Tok.one, Tok.sep]) L (R ++ [3]) hL hmt'
    (by simp [lastSym_append, Tok.one, Tok.sep]) (by simp at hb; omega)
  have hL1 := h1.last
  have h2 := RE.move (i := mt) (j := x) hmx (l := R) (e := 3) hL1 (by simp [Lists.set]) (by
    simp [Lists.set, Ne.symm hmx]; simp at hb; omega)
  refine RE.seq h1 (h2.eq ?_)
  funext y'
  by_cases h1 : y' = mt
  · subst h1; simp [Lists.set]
  · by_cases h2 : y' = x
    · subst h2; simp [Lists.set, hmx, Ne.symm hmx]
    · simp [Lists.set, h1, h2]

theorem rSkipEntry {B : Nat} {qn qn2 : Fin k} (hq : qn ≠ qn2) {L : Lists k} (hL : LenOK B L) (R P : List Nat) (κ : Nat)
    (hκ : κ = 4 ∨ κ = 5) (hP : ∀ t ∈ P, t ≠ 4 ∧ t ≠ 5)
    (hqn : L qn = R ++ (P ++ [κ]).reverse) (hb : (L qn2).length + P.length + 1 + 2 ≤ B) :
    RE B (skipEntryP qn qn2) L ((L.set qn2 (L qn2 ++ (P ++ [κ]))).set qn R) := by
  have hqn' : L qn = (R ++ [κ]) ++ P.reverse := by simpa using hqn
  have h1 := rMoveWhile (B := B) hq (fun s => !(isKind s) && s != 3) P
    (by
      intro t ht
      obtain ⟨h4, h5⟩ := hP t ht
      simp [isKind, Tok.all, Tok.ex]; omega) L (R ++ [κ]) hL hqn'
    (by rcases hκ with rfl | rfl <;> simp [lastSym_append, isKind, Tok.all, Tok.ex]) (by omega)
  have hL1 := h1.last
  have h2 := RE.move (i := qn) (j := qn2) hq (l := R) (e := κ) hL1 (by simp [Lists.set]) (by
    simp [Lists.set, Ne.symm hq]; omega)
  refine RE.seq h1 (h2.eq ?_)
  funext y'
  by_cases h1 : y' = qn
  · subst h1; simp [Lists.set]
  · by_cases h2 : y' = qn2
    · subst h2; simp [Lists.set, hq, Ne.symm hq]
    · simp [Lists.set, h1, h2]


theorem rMis {B : Nat} {qn qn2 r cf : Fin k} (hd : [qn, qn2, r, cf].Nodup) {L : Lists k} (hL : LenOK B L)
    (Q0 u : List Nat) (κ : Nat) (hκ : κ = 4 ∨ κ = 5) (hu : ∀ t ∈ u, t = 1 ∨ t = 2 ∨ t = 3)
    (Cf : List Nat) (e : Nat)
    (hqn : L qn = Q0 ++ (u ++ [κ]).reverse) (hcf : L cf = Cf ++ [e])
    (hb2 : (L qn2).length + u.length + 1 + 2 ≤ B) (hbr : (L r).length + 3 ≤ B) :
    RE B (cmpStepP.mismatch qn qn2 r cf) L
      ((((L.set qn2 (L qn2 ++ (u ++ [κ]))).set qn Q0).set r (L r ++ [1])).set cf Cf) := by
  rs_ndis hd [qn, qn2, r, cf]
  unfold cmpStepP.mismatch
  have h1 := rSkipEntry (B := B) (qn := qn) (qn2 := qn2) (fun h => n_qn_qn2.mp h) hL Q0 u κ hκ
    (by intro t ht; rcases hu t ht with h | h | h <;> omega) hqn hb2
  have h2 := RE.push (i := r) (e := Tok.one) h1.last (by rs_slk [qn, qn2, r, cf] []; omega)
  have h3 := RE.pop (i := cf) (l := Cf) (e := e) h2.last (by rs_slk [qn, qn2, r, cf] [hcf])
  refine RE.seq h1 (RE.seq h2 (h3.eq ?_))
  rs_ext [qn, qn2, r, cf]

theorem symIs_false {e s : Nat} (h : s ≠ e + 4) : symIs e s = false := by simp [symIs, h]

theorem rStepMatch {B : Nat} {x x2 qn qn2 r fl cf : Fin k} (hd : [x, x2, qn, qn2, r, fl, cf].Nodup)
    {L : Lists k} (hL : LenOK B L) (t : Nat) (ht : t = 1 ∨ t = 2 ∨ t = 3) (Xa Qa : List Nat)
    (hx : L x = Xa ++ [t]) (hqn : L qn = Qa ++ [t]) (hb2 : (L qn2).length + 3 ≤ B) (hb : (L x2).length + 3 ≤ B) :
    RE B (cmpStepP x x2 qn qn2 r fl cf) L
      ((((L.set qn2 (L qn2 ++ [t])).set qn Qa).set x2 (L x2 ++ [t])).set x Xa) := by
  rs_ndis hd [x, x2, qn, qn2, r, fl, cf]
  have hm1 := RE.move (i := qn) (j := qn2) (fun h => n_qn_qn2.mp h) hL hqn hb2
  have hm2 := RE.move (i := x) (j := x2) (l := Xa) (e := t) (fun h => n_x_x2.mp h) hm1.last
    (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hx])
    (by rs_slk [x, x2, qn, qn2, r, fl, cf] []; omega)
  have hmv : RE B ((moveTop qn qn2).seq (moveTop x x2)) L
      ((((L.set qn2 (L qn2 ++ [t])).set qn Qa).set x2 (L x2 ++ [t])).set x Xa) := by
    refine RE.seq hm1 (hm2.eq ?_)
    rs_ext [x, x2, qn, qn2, r, fl, cf]
  unfold cmpStepP
  have hxl : lastSym (L x) = t + 4 := by rw [hx, lastSym_append]
  have hql : lastSym (L qn) = t + 4 := by rw [hqn, lastSym_append]
  rcases ht with rfl | rfl | rfl
  · exact RE.iteT hL (by rw [hxl]; decide) (RE.iteT hL (by rw [hxl]; decide) (RE.iteT hL (by rw [hql]; decide) hmv))
  · exact RE.iteT hL (by rw [hxl]; decide) (RE.iteF hL (by rw [hxl]; decide)
      (RE.iteT hL (by rw [hxl]; decide) (RE.iteT hL (by rw [hql]; decide) hmv)))
  · exact RE.iteT hL (by rw [hxl]; decide) (RE.iteF hL (by rw [hxl]; decide)
      (RE.iteF hL (by rw [hxl]; decide) (RE.iteT hL (by rw [hql]; decide) hmv)))

theorem rStepMis {B : Nat} {x x2 qn qn2 r fl cf : Fin k} (hd : [x, x2, qn, qn2, r, fl, cf].Nodup)
    {L : Lists k} (hL : LenOK B L) (t : Nat) (ht : t = 1 ∨ t = 2 ∨ t = 3) (Xa : List Nat)
    (hx : L x = Xa ++ [t])
    (Q0 u : List Nat) (κ : Nat) (hκ : κ = 4 ∨ κ = 5) (hu : ∀ t ∈ u, t = 1 ∨ t = 2 ∨ t = 3)
    (Cf : List Nat) (e : Nat)
    (hqn : L qn = Q0 ++ (u ++ [κ]).reverse) (hne : lastSym (L qn) ≠ t + 4) (hcf : L cf = Cf ++ [e])
    (hb2 : (L qn2).length + u.length + 1 + 2 ≤ B) (hbr : (L r).length + 3 ≤ B) :
    RE B (cmpStepP x x2 qn qn2 r fl cf) L
      ((((L.set qn2 (L qn2 ++ (u ++ [κ]))).set qn Q0).set r (L r ++ [1])).set cf Cf) := by
  rs_ndis hd [x, x2, qn, qn2, r, fl, cf]
  have hmis := rMis (B := B) (qn := qn) (qn2 := qn2) (r := r) (cf := cf)
    (by simp [List.nodup_cons, n_qn_qn2, n_qn_r, n_qn_cf, n_qn2_r, n_qn2_cf, n_r_cf])
    hL Q0 u κ hκ hu Cf e hqn hcf hb2 hbr
  unfold cmpStepP
  have hxl : lastSym (L x) = t + 4 := by rw [hx, lastSym_append]
  rcases ht with rfl | rfl | rfl
  · exact RE.iteT hL (by rw [hxl]; decide) (RE.iteT hL (by rw [hxl]; decide)
      (RE.iteF hL (symIs_false hne) hmis))
  · exact RE.iteT hL (by rw [hxl]; decide) (RE.iteF hL (by rw [hxl]; decide)
      (RE.iteT hL (by rw [hxl]; decide) (RE.iteF hL (symIs_false hne) hmis)))
  · exact RE.iteT hL (by rw [hxl]; decide) (RE.iteF hL (by rw [hxl]; decide)
      (RE.iteF hL (by rw [hxl]; decide) (RE.iteF hL (symIs_false hne) hmis)))

theorem rEndMatch {B : Nat} {x x2 qn qn2 r fl cf : Fin k} (hd : [x, x2, qn, qn2, r, fl, cf].Nodup)
    {L : Lists k} (hL : LenOK B L) (hx : L x = []) (κ : Nat) (hκ : κ = 4 ∨ κ = 5) (Q0 : List Nat)
    (hqn : L qn = Q0 ++ [κ]) (Cf F : List Nat) (e f : Nat) (hcf : L cf = Cf ++ [e]) (hfl : L fl = F ++ [f]) :
    RE B (cmpStepP x x2 qn qn2 r fl cf) L ((L.set cf Cf).set fl F) := by
  rs_ndis hd [x, x2, qn, qn2, r, fl, cf]
  have h1 := RE.pop (i := cf) hL hcf
  have h2 := RE.pop (i := fl) h1.last (l := F) (e := f) (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hfl])
  unfold cmpStepP
  refine RE.iteF hL (by rw [hx]; rfl) (RE.iteT hL ?_ (RE.seq h1 h2))
  rw [hqn, lastSym_append]
  rcases hκ with rfl | rfl <;> decide

theorem rEndMis {B : Nat} {x x2 qn qn2 r fl cf : Fin k} (hd : [x, x2, qn, qn2, r, fl, cf].Nodup)
    {L : Lists k} (hL : LenOK B L) (hx : L x = [])
    (Q0 u : List Nat) (κ : Nat) (hκ : κ = 4 ∨ κ = 5) (hu : ∀ t ∈ u, t = 1 ∨ t = 2 ∨ t = 3)
    (Cf : List Nat) (e : Nat)
    (hqn : L qn = Q0 ++ (u ++ [κ]).reverse) (hnk : isKind (lastSym (L qn)) = false) (hcf : L cf = Cf ++ [e])
    (hb2 : (L qn2).length + u.length + 1 + 2 ≤ B) (hbr : (L r).length + 3 ≤ B) :
    RE B (cmpStepP x x2 qn qn2 r fl cf) L
      ((((L.set qn2 (L qn2 ++ (u ++ [κ]))).set qn Q0).set r (L r ++ [1])).set cf Cf) := by
  rs_ndis hd [x, x2, qn, qn2, r, fl, cf]
  have hmis := rMis (B := B) (qn := qn) (qn2 := qn2) (r := r) (cf := cf)
    (by simp [List.nodup_cons, n_qn_qn2, n_qn_r, n_qn_cf, n_qn2_r, n_qn2_cf, n_r_cf])
    hL Q0 u κ hκ hu Cf e hqn hcf hb2 hbr
  unfold cmpStepP
  exact RE.iteF hL (by rw [hx]; rfl) (RE.iteF hL hnk hmis)

theorem rCmpLoop {B : Nat} {x x2 qn qn2 r fl cf : Fin k} (hd : [x, x2, qn, qn2, r, fl, cf].Nodup)
    (κ : Nat) (hκ : κ = 4 ∨ κ = 5) (Q0 F : List Nat) (f : Nat) :
    ∀ (a b : List Nat), (∀ t ∈ a, t = 1 ∨ t = 2 ∨ t = 3) → (∀ t ∈ b, t = 1 ∨ t = 2 ∨ t = 3) →
    ∀ (L : Lists k), LenOK B L → L x = a.reverse → L qn = Q0 ++ κ :: b.reverse → L cf = [0] → L fl = F ++ [f] →
      (L x2).length + a.length + 3 ≤ B → (L qn2).length + b.length + 4 ≤ B → (L r).length + 3 ≤ B →
      ∃ L', RE B (.loop cf nonEmpty (cmpStepP x x2 qn qn2 r fl cf)) L L' ∧
        (a = b → L' = (((((L.set x []).set x2 (L x2 ++ a)).set qn2 (L qn2 ++ a)).set qn (Q0 ++ [κ])).set cf []).set fl F) ∧
        (a ≠ b → ∃ c a' b', a = c ++ a' ∧ b = c ++ b' ∧
          L' = (((((L.set x a'.reverse).set x2 (L x2 ++ c)).set qn2 (L qn2 ++ (c ++ (b' ++ [κ])))).set qn Q0).set r
            (L r ++ [1])).set cf []) := by
  rs_ndis hd [x, x2, qn, qn2, r, fl, cf]
  intro a
  induction a with
  | nil =>
    intro b _ hb L hL hx hqn hcf hfl hbx hbq hbr
    have hx0 : L x = [] := by simpa using hx
    have hcc : nonEmpty (lastSym (L cf)) = true := by rw [hcf]; rfl
    cases b with
    | nil =>
      have hm := rEndMatch (B := B) hd hL hx0 κ hκ Q0 (by simpa using hqn) [] F 0 f (by rw [hcf]; rfl) hfl
      refine ⟨_, RE.loopC hL hcc hm (RE.loopF hm.last (by simp [Lists.set, n_cf_fl, lastSym, nonEmpty])), ?_, ?_⟩
      · intro _
        rs_ext [x, x2, qn, qn2, r, fl, cf]
      · intro h; exact absurd rfl h
    | cons t b0 =>
      have ht : t = 1 ∨ t = 2 ∨ t = 3 := hb t (by simp)
      have hqn' : L qn = Q0 ++ ((t :: b0) ++ [κ]).reverse := by simpa using hqn
      have hnk : isKind (lastSym (L qn)) = false := by
        have : L qn = (Q0 ++ κ :: b0.reverse) ++ [t] := by simpa using hqn
        rw [this, lastSym_append]
        rcases ht with rfl | rfl | rfl <;> simp [isKind, Tok.all, Tok.ex]
      have hm := rEndMis (B := B) hd hL hx0 Q0 (t :: b0) κ hκ hb [] 0 hqn' hnk (by rw [hcf]; rfl) (by simp at hbq ⊢; omega) hbr
      refine ⟨_, RE.loopC hL hcc hm (RE.loopF hm.last (by simp [Lists.set, lastSym, nonEmpty])), ?_, ?_⟩
      · intro h; cases h
      · intro _
        refine ⟨[], [], t :: b0, rfl, rfl, ?_⟩
        rs_ext [x, x2, qn, qn2, r, fl, cf]
  | cons t a0 ih =>
    intro b ha hb L hL hx hqn hcf hfl hbx hbq hbr
    have ht : t = 1 ∨ t = 2 ∨ t = 3 := ha t (by simp)
    have ha0 : ∀ s ∈ a0, s = 1 ∨ s = 2 ∨ s = 3 := fun s hs => ha s (by simp [hs])
    have hx' : L x = a0.reverse ++ [t] := by simpa using hx
    have hcc : nonEmpty (lastSym (L cf)) = true := by rw [hcf]; rfl
    have hcf' : L cf = [] ++ [0] := by rw [hcf]; rfl
    have hxl : lastSym (L x) = t + 4 := by rw [hx', lastSym_append]
    -- immediate mismatch
    have hmis : lastSym (L qn) ≠ t + 4 → ∃ L', RE B (.loop cf nonEmpty (cmpStepP x x2 qn qn2 r fl cf)) L L' ∧
        (t :: a0 = b → L' = (((((L.set x []).set x2 (L x2 ++ (t :: a0))).set qn2 (L qn2 ++ (t :: a0))).set qn (Q0 ++ [κ])).set cf []).set fl F) ∧
        (t :: a0 ≠ b → ∃ c a' b', t :: a0 = c ++ a' ∧ b = c ++ b' ∧
          L' = (((((L.set x a'.reverse).set x2 (L x2 ++ c)).set qn2 (L qn2 ++ (c ++ (b' ++ [κ])))).set qn Q0).set r
            (L r ++ [1])).set cf []) := by
      intro hne
      have hqn' : L qn = Q0 ++ (b ++ [κ]).reverse := by simpa using hqn
      have hm := rStepMis (B := B) hd hL t ht a0.reverse hx' Q0 b κ hκ hb [] 0 hqn' hne hcf' (by omega) hbr
      refine ⟨_, RE.loopC hL hcc hm (RE.loopF hm.last (by simp [Lists.set, lastSym, nonEmpty])), ?_, ?_⟩
      · intro h
        subst h
        exfalso
        have : L qn = (Q0 ++ κ :: a0.reverse) ++ [t] := by simpa using hqn
        exact hne (by rw [this, lastSym_append])
      · intro _
        refine ⟨[], t :: a0, b, rfl, rfl, ?_⟩
        rs_ext [x, x2, qn, qn2, r, fl, cf]
    cases b with
    | nil =>
      apply hmis
      have : L qn = Q0 ++ [κ] := by simpa using hqn
      rw [this, lastSym_append]
      rcases hκ with rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide
    | cons t' b0 =>
      by_cases htt : t' = t
      · have hqn2 : L qn = (Q0 ++ κ :: b0.reverse) ++ [t] := by simpa [htt] using hqn
        have hm := rStepMatch (B := B) hd hL t ht a0.reverse (Q0 ++ κ :: b0.reverse) hx' hqn2
          (by simp at hbq; omega) (by simp at hbx; omega)
        have hL1 := hm.last
        have hb0 : ∀ s ∈ b0, s = 1 ∨ s = 2 ∨ s = 3 := fun s hs => hb s (by simp [hs])
        have e2 : ((((L.set qn2 (L qn2 ++ [t])).set qn (Q0 ++ κ :: b0.reverse)).set x2 (L x2 ++ [t])).set x a0.reverse) x2 = L x2 ++ [t] := by
          rs_slk [x, x2, qn, qn2, r, fl, cf] []
        have e3 : ((((L.set qn2 (L qn2 ++ [t])).set qn (Q0 ++ κ :: b0.reverse)).set x2 (L x2 ++ [t])).set x a0.reverse) qn2 = L qn2 ++ [t] := by
          rs_slk [x, x2, qn, qn2, r, fl, cf] []
        obtain ⟨L', hrun, h1, h2⟩ := ih b0 ha0 hb0 _ hL1
          (by rs_slk [x, x2, qn, qn2, r, fl, cf] [])
          (by rs_slk [x, x2, qn, qn2, r, fl, cf] [])
          (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hcf])
          (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hfl])
          (by rw [e2]; simp at hbx ⊢; omega)
          (by rw [e3]; simp at hbq ⊢; omega)
          (by have : ((((L.set qn2 (L qn2 ++ [t])).set qn (Q0 ++ κ :: b0.reverse)).set x2 (L x2 ++ [t])).set x a0.reverse) r = L r := by
                rs_slk [x, x2, qn, qn2, r, fl, cf] []
              rw [this]; exact hbr)
        refine ⟨L', RE.loopC hL hcc hm hrun, ?_, ?_⟩
        · intro h
          have h' : a0 = b0 := by simpa [htt] using h
          have h1' := h1 h'
          subst h'
          rw [h1']
          clear ih hrun hm h1 h2 h1'
          rs_ext [x, x2, qn, qn2, r, fl, cf]
        · intro hne2
          have hne3 : a0 ≠ b0 := fun e => hne2 (by rw [e, htt])
          obtain ⟨c, a', b', hab1, hab2, hL'⟩ := h2 hne3
          refine ⟨t :: c, a', b', by simp [hab1], by simp [hab2, htt], ?_⟩
          rw [hL']
          clear ih hrun hm h1 h2 hL'
          rs_ext [x, x2, qn, qn2, r, fl, cf]
      · apply hmis
        have : L qn = (Q0 ++ κ :: b0.reverse) ++ [t'] := by simpa using hqn
        rw [this, lastSym_append]
        omega

theorem rMoveAllRE {B : Nat} {i j : Fin k} (hij : i ≠ j) {L : Lists k} (hL : LenOK B L)
    (hb : (L i).length + (L j).length + 2 ≤ B) : RE B (moveAll i j) L (L.moveAll i j) := by
  refine ⟨_, runs_moveAll hij ?_⟩
  intro n m hn hm y
  simp only [Lists.moving, Lists.set]
  by_cases hyi : y = i
  · subst hyi; simp; omega
  · by_cases hyj : y = j
    · subst hyj; simp [hyi]; omega
    · simp [hyi, hyj]; exact hL y

theorem rSearchStep {B : Nat} {x x2 qn qn2 r fl cf : Fin k} (hd : [x, x2, qn, qn2, r, fl, cf].Nodup)
    (κ : Nat) (hκ : κ = 4 ∨ κ = 5) (Q0 F : List Nat) (f : Nat) (a b : List Nat)
    (ha : ∀ t ∈ a, t = 1 ∨ t = 2 ∨ t = 3) (hb : ∀ t ∈ b, t = 1 ∨ t = 2 ∨ t = 3)
    {L : Lists k} (hL : LenOK B L) (hx : L x = a.reverse) (hx2 : L x2 = [])
    (hqn : L qn = Q0 ++ κ :: b.reverse) (hcf : L cf = []) (hfl : L fl = F ++ [f])
    (hbx : a.length + 3 ≤ B) (hbq : (L qn2).length + b.length + 4 ≤ B) (hbr : (L r).length + 3 ≤ B) :
    (a = b → RE B (searchStepP x x2 qn qn2 r fl cf) L (((L.set qn2 (L qn2 ++ a)).set qn (Q0 ++ [κ])).set fl F)) ∧
    (a ≠ b → RE B (searchStepP x x2 qn qn2 r fl cf) L
      (((L.set qn2 (L qn2 ++ (b ++ [κ]))).set qn Q0).set r (L r ++ [1]))) := by
  rs_ndis hd [x, x2, qn, qn2, r, fl, cf]
  have hp := RE.push (i := cf) (e := 0) hL (by simp [hcf]; omega)
  have hL0 := hp.last
  obtain ⟨L', hrun, h1, h2⟩ := rCmpLoop (B := B) hd κ hκ Q0 F f a b ha hb _ hL0
    (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hx]) (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hqn])
    (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hcf]) (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hfl])
    (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hx2]; omega)
    (by rs_slk [x, x2, qn, qn2, r, fl, cf] []; omega)
    (by rs_slk [x, x2, qn, qn2, r, fl, cf] []; omega)
  have hLL := hrun.last
  have nx : x2 ≠ x := fun h => n_x2_x.mp h
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · have e := h1 hab
    have hm := rMoveAllRE (B := B) nx hLL (by rw [e]; rs_slk [x, x2, qn, qn2, r, fl, cf] [hx2]; omega)
    refine RE.seq hp (RE.seq hrun (hm.eq ?_))
    rw [e]
    simp only [Lists.moveAll]
    rs_ext [x, x2, qn, qn2, r, fl, cf]
  · obtain ⟨c, a', b', hac, hbc, e⟩ := h2 hab
    have hm := rMoveAllRE (B := B) nx hLL (by
      rw [e]; rs_slk [x, x2, qn, qn2, r, fl, cf] [hx2]
      have : a.length = c.length + a'.length := by rw [hac]; simp
      omega)
    refine RE.seq hp (RE.seq hrun (hm.eq ?_))
    rw [e]
    simp only [Lists.moveAll]
    subst hbc
    rs_ext [x, x2, qn, qn2, r, fl, cf]

theorem encName_mem (y : Name) : ∀ t ∈ encName y, t = 1 ∨ t = 2 ∨ t = 3 := by
  obtain ⟨P, hP, h12⟩ := encName_split y
  intro t ht
  rw [hP] at ht
  simp at ht
  rcases ht with ht | ht
  · rcases h12 t ht with h | h <;> simp [h]
  · simp [ht]

theorem qnList_snoc (qs : List (Bool × Name)) (e : Bool × Name) :
    qnList (qs ++ [e]) = qnList qs ++ ((if e.1 then Tok.all else Tok.ex) :: encName e.2) := by
  simp [qnList]

theorem kind_mem (b : Bool) : (if b then Tok.all else Tok.ex) = 4 ∨ (if b then Tok.all else Tok.ex) = 5 := by
  cases b <;> simp [Tok.all, Tok.ex]

theorem qnList_len (E : List (Bool × Name)) (e : Bool × Name) :
    (qnList (e :: E).reverse).length = (qnList E.reverse).length + (encName e.2).length + 1 := by
  simp [qnList_snoc]; omega

@[simp] theorem qnList_nil : qnList [] = [] := rfl

theorem rSkipAll {B : Nat} {x x2 qn qn2 r fl cf : Fin k} (hd : [qn, qn2, fl].Nodup) :
    ∀ (E : List (Bool × Name)) (L : Lists k), LenOK B L → L fl = [] → L qn = qnList E.reverse →
      (L qn2).length + (qnList E.reverse).length + 3 ≤ B →
      RE B (.loop qn nonEmpty (.ite fl nonEmpty (searchStepP x x2 qn qn2 r fl cf) (skipEntryP qn qn2))) L
        ((L.set qn2 (L qn2 ++ (qnList E.reverse).reverse)).set qn []) := by
  rs_ndis hd [qn, qn2, fl]
  intro E
  induction E with
  | nil =>
    intro L hL hfl hqn _
    refine (RE.loopF hL (by rw [hqn]; rfl)).eq ?_
    rs_ext [qn, qn2, fl]
  | cons e E ih =>
    intro L hL hfl hqn hb
    have hE : qnList (e :: E).reverse = qnList E.reverse ++ ((if e.1 then Tok.all else Tok.ex) :: encName e.2) := by
      simp [qnList_snoc]
    have hlen := qnList_len E e
    have hqn' : L qn = qnList E.reverse ++ ((encName e.2).reverse ++ [if e.1 then Tok.all else Tok.ex]).reverse := by
      rw [hqn, hE]; simp
    have hs := rSkipEntry (B := B) (fun h => n_qn_qn2.mp h) hL (qnList E.reverse) (encName e.2).reverse _
      (kind_mem e.1)
      (by intro t ht; have := encName_mem e.2 t (by simpa using ht); omega) hqn' (by simp; omega)
    have hL1 := hs.last
    have hcond : nonEmpty (lastSym (L qn)) = true := by
      obtain ⟨P, hP, _⟩ := encName_split e.2
      have : L qn = (qnList E.reverse ++ (if e.1 then Tok.all else Tok.ex) :: P) ++ [3] := by
        rw [hqn, hE, hP]; simp
      rw [this, lastSym_append]; rfl
    refine RE.loopC hL hcond (RE.iteF hL (by rw [hfl]; rfl) hs) ((ih _ hL1 ?_ ?_ ?_).eq ?_)
    · rs_slk [qn, qn2, fl] [hfl]
    · rs_slk [qn, qn2, fl] []
    · rw [hlen] at hb; rs_slk [qn, qn2, fl] []; omega
    · rw [hE]
      rs_ext [qn, qn2, fl]

theorem encName_inj {y z : Name} (h : encName y = encName z) : y = z := by
  have h1 := parseName_encName y [] (y.length + z.length + 1) (by omega)
  have h2 := parseName_encName z [] (y.length + z.length + 1) (by omega)
  rw [h] at h1
  rw [h1] at h2
  simp at h2
  exact h2

theorem lastne (R : List Nat) (κ : Nat) (z : Name) : nonEmpty (lastSym (R ++ κ :: encName z)) = true := by
  obtain ⟨P, hP, _⟩ := encName_split z
  rw [hP]
  have : R ++ κ :: (P ++ [3]) = (R ++ κ :: P) ++ [3] := by simp
  rw [this, lastSym_append]; rfl

theorem findIdx_cons_aux (e : Bool × Name) (E : List (Bool × Name)) (y : Name) :
    ((e :: E).map Prod.snd).findIdx? (· == y) =
      if e.2 = y then some 0 else ((E.map Prod.snd).findIdx? (· == y)).map (· + 1) := by
  simp [List.findIdx?_cons]

theorem rLookLoop {B : Nat} {x x2 qn qn2 r fl cf : Fin k} (hd : [x, x2, qn, qn2, r, fl, cf].Nodup) (y : Name)
    (hbx : (encName y).length + 3 ≤ B) :
    ∀ (E : List (Bool × Name)) (L : Lists k), LenOK B L → L x = encName y → L x2 = [] → L cf = [] → L fl = [0] →
      L qn = qnList E.reverse → (L qn2).length + (qnList E.reverse).length + 4 ≤ B → (L r).length + E.length + 3 ≤ B →
      RE B (.loop qn nonEmpty (.ite fl nonEmpty (searchStepP x x2 qn qn2 r fl cf) (skipEntryP qn qn2))) L
        (match (E.map Prod.snd).findIdx? (· == y) with
         | some i => (((L.set qn2 (L qn2 ++ (qnList E.reverse).reverse)).set qn []).set r
             (L r ++ List.replicate i 1)).set fl []
         | none => ((L.set qn2 (L qn2 ++ (qnList E.reverse).reverse)).set qn []).set r
             (L r ++ List.replicate E.length 1)) := by
  rs_ndis hd [x, x2, qn, qn2, r, fl, cf]
  have hd3 : [qn, qn2, fl].Nodup := by simp [List.nodup_cons, n_qn_qn2, n_qn_fl, n_qn2_fl]
  intro E
  induction E with
  | nil =>
    intro L hL _ _ _ _ hqn _ _
    simp only [List.map_nil, List.findIdx?_nil]
    refine (RE.loopF hL (by rw [hqn]; rfl)).eq ?_
    simp
    rs_ext [x, x2, qn, qn2, r, fl, cf]
  | cons e E ih =>
    intro L hL hx hx2 hcf hfl hqn hbq hbr
    obtain ⟨κ, hκ, hEκ⟩ : ∃ κ, (κ = 4 ∨ κ = 5) ∧ qnList (e :: E).reverse = qnList E.reverse ++ κ :: encName e.2 :=
      ⟨_, kind_mem e.1, by simp [qnList_snoc]⟩
    have hlen : (qnList (e :: E).reverse).length = (qnList E.reverse).length + (encName e.2).length + 1 :=
      qnList_len E e
    have hqn' : L qn = qnList E.reverse ++ κ :: encName e.2 := by rw [hqn, hEκ]
    have hcond : nonEmpty (lastSym (L qn)) = true := by rw [hqn']; exact lastne _ _ _
    have hcondf : nonEmpty (lastSym (L fl)) = true := by rw [hfl]; rfl
    have ha : ∀ t ∈ (encName y).reverse, t = 1 ∨ t = 2 ∨ t = 3 := fun t ht => encName_mem y t (by simpa using ht)
    have hb : ∀ t ∈ (encName e.2).reverse, t = 1 ∨ t = 2 ∨ t = 3 := fun t ht => encName_mem e.2 t (by simpa using ht)
    have hx' : L x = (encName y).reverse.reverse := by simpa using hx
    have hqn'' : L qn = qnList E.reverse ++ κ :: (encName e.2).reverse.reverse := by simpa using hqn'
    have hfl' : L fl = [] ++ [0] := by rw [hfl]; rfl
    have hbq' : (L qn2).length + (encName e.2).reverse.length + 4 ≤ B := by simp; omega
    have hbx' : (encName y).reverse.length + 3 ≤ B := by simpa using hbx
    have hbr' : (L r).length + 3 ≤ B := by simp at hbr; omega
    by_cases hyz : y = e.2
    · have hab : (encName y).reverse = (encName e.2).reverse := by rw [hyz]
      have hlenyz : (encName y).length = (encName e.2).length := by rw [hyz]
      have hst := (rSearchStep (B := B) hd κ hκ (qnList E.reverse) [] 0 _ _ ha hb hL hx' hx2 hqn'' hcf hfl'
        hbx' hbq' hbr').1 hab
      have hL1 := hst.last
      have hq1 : (((L.set qn2 (L qn2 ++ (encName y).reverse)).set qn (qnList E.reverse ++ [κ])).set fl []) qn
          = qnList E.reverse ++ [κ] := by rs_slk [x, x2, qn, qn2, r, fl, cf] []
      have hs := rSkipEntry (B := B) (fun h => n_qn_qn2.mp h) hL1 (qnList E.reverse) [] κ hκ (by simp)
        (by rw [hq1]; simp) (by rs_slk [x, x2, qn, qn2, r, fl, cf] []; simp at hbq' ⊢; omega)
      have hL2 := hs.last
      have hsa := rSkipAll (B := B) (x := x) (x2 := x2) (r := r) (cf := cf) hd3 E _ hL2
        (by rs_slk [x, x2, qn, qn2, r, fl, cf] []) (by rs_slk [x, x2, qn, qn2, r, fl, cf] [])
        (by rs_slk [x, x2, qn, qn2, r, fl, cf] []; simp at hbq' ⊢; rw [hlen] at hbq; omega)
      have hcond1 : nonEmpty (lastSym ((((L.set qn2 (L qn2 ++ (encName y).reverse)).set qn
          (qnList E.reverse ++ [κ])).set fl []) qn)) = true := by
        rw [hq1, lastSym_append]; rcases hκ with h | h <;> simp [h, nonEmpty]
      have hcond2 : nonEmpty (lastSym ((((L.set qn2 (L qn2 ++ (encName y).reverse)).set qn
          (qnList E.reverse ++ [κ])).set fl []) fl)) = false := by
        simp [Lists.set, lastSym, nonEmpty]
      refine (RE.loopC hL hcond (RE.iteT hL hcondf hst)
        (RE.loopC hL1 hcond1 (RE.iteF hL1 hcond2 hs) hsa)).eq ?_
      have hfi : ((e :: E).map Prod.snd).findIdx? (· == y) = some 0 := by
        rw [findIdx_cons_aux]; simp [hyz]
      simp only [hfi]
      rw [hEκ]
      rs_ext [x, x2, qn, qn2, r, fl, cf]
    · have hab : (encName y).reverse ≠ (encName e.2).reverse := fun h =>
        hyz (encName_inj (by simpa using congrArg List.reverse h))
      have hst := (rSearchStep (B := B) hd κ hκ (qnList E.reverse) [] 0 _ _ ha hb hL hx' hx2 hqn'' hcf hfl'
        hbx' hbq' hbr').2 hab
      have hL1 := hst.last
      have ih' := ih _ hL1 (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hx]) (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hx2])
        (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hcf]) (by rs_slk [x, x2, qn, qn2, r, fl, cf] [hfl])
        (by rs_slk [x, x2, qn, qn2, r, fl, cf] [])
        (by rs_slk [x, x2, qn, qn2, r, fl, cf] []; simp at hbq' ⊢; omega)
        (by rs_slk [x, x2, qn, qn2, r, fl, cf] []; simp at hbr ⊢; omega)
      refine (RE.loopC hL hcond (RE.iteT hL hcondf hst) ih').eq ?_
      rw [findIdx_cons_aux, if_neg (Ne.symm hyz)]
      rcases h : (E.map Prod.snd).findIdx? (· == y) with _ | i
      · simp only [h, Option.map_none]
        rw [hEκ]
        rs_ext [x, x2, qn, qn2, r, fl, cf]
      · simp only [h, Option.map_some]
        rw [hEκ]
        rs_ext [x, x2, qn, qn2, r, fl, cf]

theorem findIdx_lt {N : List Name} {y : Name} {i : Nat} (h : N.findIdx? (· == y) = some i) : i < N.length := by
  have := List.findIdx?_eq_some_iff_findIdx_eq.mp h
  exact this.1

theorem rLookupP {B : Nat} {out x x2 qn qn2 r fl cf : Fin k} (hd : [out, x, x2, qn, qn2, r, fl, cf].Nodup)
    (y : Name) (E : List (Bool × Name)) {L : Lists k} (hL : LenOK B L)
    (hx : L x = encName y) (hx2 : L x2 = []) (hqn : L qn = qnList E.reverse) (hqn2 : L qn2 = [])
    (hr : L r = []) (hfl : L fl = []) (hcf : L cf = [])
    (hbx : (encName y).length + 3 ≤ B) (hbq : (qnList E.reverse).length + 4 ≤ B) (hbr : E.length + 3 ≤ B)
    (hbo : (L out).length + E.length + 5 ≤ B) :
    RE B (lookupP out x x2 qn qn2 r fl cf) L
      ((L.set x []).set out (L out ++ encV (resolveTok (E.map Prod.snd) (.var y)))) := by
  have hd7 : [x, x2, qn, qn2, r, fl, cf].Nodup := (List.nodup_cons.mp hd).2
  rs_ndis hd [out, x, x2, qn, qn2, r, fl, cf]
  have hv : Tok.var = 6 := rfl
  have hfin : Tok.fin = 3 := rfl
  have hff : Tok.ff = 8 := rfl
  have hp := RE.push (i := fl) (e := 0) hL (by simp [hfl]; omega)
  have hL0 := hp.last
  have hlook := rLookLoop (B := B) hd7 y hbx E _ hL0
    (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hx]) (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hx2])
    (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hcf]) (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hfl])
    (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hqn])
    (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hqn2]; omega)
    (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hr]; omega)
  rcases hfi : (E.map Prod.snd).findIdx? (· == y) with _ | i
  · simp only [hfi] at hlook
    have hLl := hlook.last
    have hm := rMoveAllRE (B := B) (i := qn2) (j := qn) (fun h => n_qn2_qn.mp h) hLl
      (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hqn2]; omega)
    have hLm := hm.last
    have hpop := RE.pop (i := fl) (l := []) (e := 0) hLm (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hfl])
    have hLa := hpop.last
    have hcl := rClear (B := B) r E.length _ (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hr]) hLa
    have hLb := hcl.last
    have hpu := RE.push (i := out) (e := Tok.ff) hLb (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] []; omega)
    have hLc := hpu.last
    have hcx := rClear (B := B) x (encName y).length _ (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hx]) hLc
    refine (RE.seq hp (RE.seq hlook (RE.seq hm (RE.seq (RE.iteT hLm (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hfl]; rfl)
      (RE.seq hpop (RE.seq hcl hpu))) hcx)))).eq ?_
    simp only [Lists.moveAll, resolveTok, hfi, encV]
    rs_ext [out, x, x2, qn, qn2, r, fl, cf]
  · have hi : i < E.length := by simpa using findIdx_lt (N := E.map Prod.snd) (y := y) hfi
    simp only [hfi] at hlook
    have hLl := hlook.last
    have hm := rMoveAllRE (B := B) (i := qn2) (j := qn) (fun h => n_qn2_qn.mp h) hLl
      (by rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hqn2]; omega)
    have hLm := hm.last
    have hpu1 := RE.push (i := out) (e := Tok.var) hLm (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] []; omega)
    have hL1 := hpu1.last
    have hm2 := rMoveAllRE (B := B) (i := r) (j := out) (fun h => n_r_out.mp h) hL1 (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hr]; omega)
    have hL2 := hm2.last
    have hpu2 := RE.push (i := out) (e := Tok.fin) hL2 (by
      simp only [Lists.moveAll, Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hr]; omega)
    have hL3 := hpu2.last
    have hcx := rClear (B := B) x (encName y).length _ (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hx]) hL3
    refine (RE.seq hp (RE.seq hlook (RE.seq hm (RE.seq (RE.iteF hLm (by
      simp only [Lists.moveAll]; rs_slk [out, x, x2, qn, qn2, r, fl, cf] [hfl]; rfl)
      (RE.seq hpu1 (RE.seq hm2 hpu2))) hcx)))).eq ?_
    simp only [Lists.moveAll, resolveTok, hfi, encV]
    rs_ext [out, x, x2, qn, qn2, r, fl, cf]

@[simp] theorem mtList_nil : mtList [] = [] := rfl

theorem qnList_len_ge (qs : List (Bool × Name)) : qs.length ≤ (qnList qs).length := by
  induction qs with
  | nil => simp
  | cons e qs ih => simp [qnList] at ih ⊢; omega

theorem mtList_cons (t : RTok) (m : List RTok) : mtList (t :: m) = RTok.enc t ++ mtList m := by
  simp [mtList]

theorem rResStep {B : Nat} {mt out x x2 qn qn2 r fl cf : Fin k}
    (hd : [mt, out, x, x2, qn, qn2, r, fl, cf].Nodup)
    (qs : List (Bool × Name)) (tok : RTok) (m' : List RTok) {L : Lists k} (hL : LenOK B L)
    (hmt : L mt = (mtList (tok :: m')).reverse) (hx : L x = []) (hx2 : L x2 = []) (hqn : L qn = qnList qs)
    (hqn2 : L qn2 = []) (hr : L r = []) (hfl : L fl = []) (hcf : L cf = [])
    (hbm : (mtList (tok :: m')).length + 3 ≤ B) (hbq : (qnList qs).length + 4 ≤ B)
    (hbo : (L out).length + qs.length + 5 ≤ B) :
    RE B (resStepP mt out x x2 qn qn2 r fl cf) L
      ((L.set mt (mtList m').reverse).set out (L out ++ encV (resolveTok (qs.map Prod.snd).reverse tok))) := by
  have hd8 : [out, x, x2, qn, qn2, r, fl, cf].Nodup := (List.nodup_cons.mp hd).2
  rs_ndis hd [mt, out, x, x2, qn, qn2, r, fl, cf]
  have hge := qnList_len_ge qs
  have hv : Tok.var = 6 := rfl
  have hfin : Tok.fin = 3 := rfl
  rw [mtList_cons] at hmt hbm
  cases tok with
  | var y =>
    have hmt' : L mt = ((mtList m').reverse ++ (encName y).reverse) ++ [6] := by
      rw [hmt]; simp [RTok.enc, Tok.var]
    have hcnd : symIs Tok.var (lastSym (L mt)) = true := by
      rw [hmt', lastSym_append]; simp [symIs, Tok.var]
    have hpop := RE.pop (i := mt) hL hmt'
    have hL1 := hpop.last
    simp only [RTok.enc, List.length_append, List.length_cons] at hbm
    have hrd := rReadName (B := B) (mt := mt) (x := x) (fun h => n_mt_x.mp h) hL1 y (mtList m').reverse
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] []) (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hx]; omega)
    have hL2 := hrd.last
    have hlk := rLookupP (B := B) hd8 y qs.reverse hL2
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hx]) (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hx2])
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hqn]) (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hqn2])
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hr]) (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hfl])
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hcf])
      (by omega) (by simpa using hbq) (by simp; omega)
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] []; omega)
    refine (RE.iteT hL hcnd (RE.seq hpop (RE.seq hrd hlk))).eq ?_
    have hmr : qs.reverse.map Prod.snd = (qs.map Prod.snd).reverse := List.map_reverse
    rs_ext [mt, out, x, x2, qn, qn2, r, fl, cf]
  | tt =>
    have hmt' : L mt = (mtList m').reverse ++ [7] := by rw [hmt]; simp [RTok.enc, Tok.tt]
    have hcnd : symIs Tok.var (lastSym (L mt)) = false := by
      rw [hmt', lastSym_append]; simp [symIs, Tok.var]
    have hm := RE.move (i := mt) (j := out) (fun h => n_mt_out.mp h) hL hmt' (by omega)
    refine (RE.iteF hL hcnd hm).eq ?_
    simp only [resolveTok, encV]
    rs_ext [mt, out, x, x2, qn, qn2, r, fl, cf]
  | ff =>
    have hmt' : L mt = (mtList m').reverse ++ [8] := by rw [hmt]; simp [RTok.enc, Tok.ff]
    have hcnd : symIs Tok.var (lastSym (L mt)) = false := by
      rw [hmt', lastSym_append]; simp [symIs, Tok.var]
    have hm := RE.move (i := mt) (j := out) (fun h => n_mt_out.mp h) hL hmt' (by omega)
    refine (RE.iteF hL hcnd hm).eq ?_
    simp only [resolveTok, encV]
    rs_ext [mt, out, x, x2, qn, qn2, r, fl, cf]
  | neg =>
    have hmt' : L mt = (mtList m').reverse ++ [9] := by rw [hmt]; simp [RTok.enc, Tok.neg]
    have hcnd : symIs Tok.var (lastSym (L mt)) = false := by
      rw [hmt', lastSym_append]; simp [symIs, Tok.var]
    have hm := RE.move (i := mt) (j := out) (fun h => n_mt_out.mp h) hL hmt' (by omega)
    refine (RE.iteF hL hcnd hm).eq ?_
    simp only [resolveTok, encV]
    rs_ext [mt, out, x, x2, qn, qn2, r, fl, cf]
  | conj =>
    have hmt' : L mt = (mtList m').reverse ++ [10] := by rw [hmt]; simp [RTok.enc, Tok.conj]
    have hcnd : symIs Tok.var (lastSym (L mt)) = false := by
      rw [hmt', lastSym_append]; simp [symIs, Tok.var]
    have hm := RE.move (i := mt) (j := out) (fun h => n_mt_out.mp h) hL hmt' (by omega)
    refine (RE.iteF hL hcnd hm).eq ?_
    simp only [resolveTok, encV]
    rs_ext [mt, out, x, x2, qn, qn2, r, fl, cf]
  | disj =>
    have hmt' : L mt = (mtList m').reverse ++ [11] := by rw [hmt]; simp [RTok.enc, Tok.disj]
    have hcnd : symIs Tok.var (lastSym (L mt)) = false := by
      rw [hmt', lastSym_append]; simp [symIs, Tok.var]
    have hm := RE.move (i := mt) (j := out) (fun h => n_mt_out.mp h) hL hmt' (by omega)
    refine (RE.iteF hL hcnd hm).eq ?_
    simp only [resolveTok, encV]
    rs_ext [mt, out, x, x2, qn, qn2, r, fl, cf]

theorem enc_ne (tok : RTok) : ∃ a rest, RTok.enc tok = a :: rest := by
  cases tok <;> simp [RTok.enc]

theorem rResLoop {B : Nat} {mt out x x2 qn qn2 r fl cf : Fin k}
    (hd : [mt, out, x, x2, qn, qn2, r, fl, cf].Nodup) (qs : List (Bool × Name))
    (hbq : (qnList qs).length + 4 ≤ B) :
    ∀ (m : List RTok) (L : Lists k), LenOK B L → L mt = (mtList m).reverse → L x = [] → L x2 = [] →
      L qn = qnList qs → L qn2 = [] → L r = [] → L fl = [] → L cf = [] →
      (mtList m).length + 3 ≤ B →
      (L out).length + (toksV (m.map (resolveTok (qs.map Prod.snd).reverse))).length + qs.length + 4 ≤ B →
      RE B (resolveP mt out x x2 qn qn2 r fl cf) L
        ((L.set mt []).set out (L out ++ toksV (m.map (resolveTok (qs.map Prod.snd).reverse)))) := by
  rs_ndis hd [mt, out, x, x2, qn, qn2, r, fl, cf]
  intro m
  induction m with
  | nil =>
    intro L hL hmt _ _ _ _ _ _ _ _ _
    refine (RE.loopF hL (by rw [hmt]; rfl)).eq ?_
    simp [toksV]
    rs_ext [mt, out, x, x2, qn, qn2, r, fl, cf]
  | cons tok m' ih =>
    intro L hL hmt hx hx2 hqn hqn2 hr hfl hcf hbm hbo
    have hcnd : nonEmpty (lastSym (L mt)) = true := by
      obtain ⟨a, rest, hr'⟩ := enc_ne tok
      have : L mt = (rest ++ mtList m').reverse ++ [a] := by
        rw [hmt, mtList_cons, hr']; simp
      rw [this, lastSym_append]
      simp [nonEmpty]
    have hmap : (List.map (resolveTok (qs.map Prod.snd).reverse) (tok :: m')) =
        resolveTok (qs.map Prod.snd).reverse tok :: m'.map (resolveTok (qs.map Prod.snd).reverse) := rfl
    have htk : toksV (List.map (resolveTok (qs.map Prod.snd).reverse) (tok :: m')) =
        encV (resolveTok (qs.map Prod.snd).reverse tok) ++ toksV (m'.map (resolveTok (qs.map Prod.snd).reverse)) := by
      rw [hmap]; simp [toksV]
    have hone : 1 ≤ (encV (resolveTok (qs.map Prod.snd).reverse tok)).length := by
      cases (resolveTok (qs.map Prod.snd).reverse tok) <;> simp [encV]
    have hst := rResStep (B := B) hd qs tok m' hL hmt hx hx2 hqn hqn2 hr hfl hcf hbm hbq
      (by rw [htk] at hbo; simp at hbo; omega)
    have hL1 := hst.last
    have hbm' : (mtList m').length + 3 ≤ B := by
      rw [mtList_cons] at hbm; simp at hbm; omega
    have hih := ih _ hL1 (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [])
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hx]) (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hx2])
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hqn]) (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hqn2])
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hr]) (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hfl])
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] [hcf]) hbm'
      (by rs_slk [mt, out, x, x2, qn, qn2, r, fl, cf] []; rw [htk] at hbo; simp at hbo ⊢; omega)
    refine (RE.loopC hL hcnd hst hih).eq ?_
    rw [htk]
    rs_ext [mt, out, x, x2, qn, qn2, r, fl, cf]

end RsResolveSpec

theorem resolveP_spec {mt out x x2 qn qn2 r fl cf : Fin k} (hd : [mt, out, x, x2, qn, qn2, r, fl, cf].Nodup)
    {B : Nat} (qs : List (Bool × Name)) (m : List RTok) {L : Lists k}
    (hmt : L mt = (mtList m).reverse) (hout : L out = []) (hx : L x = []) (hx2 : L x2 = []) (hqn : L qn = qnList qs)
    (hqn2 : L qn2 = []) (hr : L r = []) (hfl : L fl = []) (hcf : L cf = [])
    (hB : LenOK B L)
    (hBd : (mtList m).length + (toksV (m.map (resolveTok (qs.map Prod.snd).reverse))).length + (qnList qs).length + 4 ≤ B) :
    ∃ T, Runs (LenOK B) (resolveP mt out x x2 qn qn2 r fl cf) L
      ((L.set mt []).set out (toksV (m.map (resolveTok (qs.map Prod.snd).reverse)))) T := by
  have hge := RsResolveSpec.qnList_len_ge qs
  have h := RsResolveSpec.rResLoop (B := B) hd qs (by omega) m L hB hmt hx hx2 hqn hqn2 hr hfl hcf (by omega)
    (by rw [hout]; simp; omega)
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  rw [hout] at hT
  simpa using hT

namespace RsResolveSpec

def rsKf (t : Nat) : Option Nat := if t = 4 then some 1 else if t = 5 then some 0 else none

theorem rKindsLoop {B : Nat} {qn ks : Fin k} (hne : qn ≠ ks) :
    ∀ (R : List Nat) (L : Lists k), LenOK B L → L qn = R.reverse →
      (L ks).length + (R.filterMap rsKf).length + 2 ≤ B →
      RE B (kindsP qn ks) L ((L.set qn []).set ks (L ks ++ R.filterMap rsKf)) := by
  have hd : [qn, ks].Nodup := by simp [hne]
  rs_ndis hd [qn, ks]
  intro R
  induction R with
  | nil =>
    intro L hL hqn _
    refine (RE.loopF hL (by rw [hqn]; rfl)).eq ?_
    simp
    rs_ext [qn, ks]
  | cons t R ih =>
    intro L hL hqn hb
    have hqn' : L qn = R.reverse ++ [t] := by simpa using hqn
    have hcnd : nonEmpty (lastSym (L qn)) = true := by rw [hqn', lastSym_append]; simp [nonEmpty]
    by_cases h4 : t = 4
    · subst h4
      have hpop := RE.pop (i := qn) hL hqn'
      have hL1 := hpop.last
      have hpu := RE.push (i := ks) (e := 1) hL1 (by
        rs_slk [qn, ks] []; simp [rsKf] at hb; omega)
      have hL2 := hpu.last
      have hih := ih _ hL2 (by rs_slk [qn, ks] [])
        (by rs_slk [qn, ks] []; simp [rsKf] at hb ⊢; omega)
      refine (RE.loopC hL hcnd (RE.iteT hL (by rw [hqn']; simp [lastSym_append, symIs, Tok.all]) (RE.seq hpop hpu))
        hih).eq ?_
      simp only [List.filterMap_cons, rsKf]
      simp
      rs_ext [qn, ks]
    · by_cases h5 : t = 5
      · subst h5
        have hpop := RE.pop (i := qn) hL hqn'
        have hL1 := hpop.last
        have hpu := RE.push (i := ks) (e := 0) hL1 (by
          rs_slk [qn, ks] []; simp [rsKf] at hb; omega)
        have hL2 := hpu.last
        have hih := ih _ hL2 (by rs_slk [qn, ks] [])
          (by rs_slk [qn, ks] []; simp [rsKf] at hb ⊢; omega)
        refine (RE.loopC hL hcnd (RE.iteF hL (by rw [hqn']; simp [lastSym_append, symIs, Tok.all])
          (RE.iteT hL (by rw [hqn']; simp [lastSym_append, symIs, Tok.ex]) (RE.seq hpop hpu))) hih).eq ?_
        simp only [List.filterMap_cons, rsKf]
        simp
        rs_ext [qn, ks]
      · have hpop := RE.pop (i := qn) hL hqn'
        have hL1 := hpop.last
        have hih := ih _ hL1 (by rs_slk [qn, ks] [])
          (by rs_slk [qn, ks] []; simp [rsKf, h4, h5] at hb ⊢; omega)
        refine (RE.loopC hL hcnd (RE.iteF hL (by rw [hqn']; simp [lastSym_append, symIs, Tok.all]; omega)
          (RE.iteF hL (by rw [hqn']; simp [lastSym_append, symIs, Tok.ex]; omega) hpop)) hih).eq ?_
        simp only [List.filterMap_cons, rsKf, h4, h5]
        simp
        rs_ext [qn, ks]

theorem rKindsList : ∀ (qs : List (Bool × Name)),
    ((qnList qs).reverse).filterMap rsKf = ((qs.map Prod.fst).map kindElem).reverse
  | [] => by simp
  | e :: qs => by
    have h : qnList (e :: qs) = ((if e.1 then Tok.all else Tok.ex) :: encName e.2) ++ qnList qs := by
      simp [qnList]
    rw [h]
    simp only [List.reverse_append, List.filterMap_append, rKindsList qs]
    obtain ⟨P, hP, h12⟩ := encName_split e.2
    rw [hP]
    have : ∀ P' : List Nat, (∀ t ∈ P', t = 1 ∨ t = 2) → P'.filterMap rsKf = [] := by
      intro P' hP'
      rw [List.filterMap_eq_nil_iff]
      intro t ht
      rcases hP' t ht with h | h <;> simp [rsKf, h]
    simp [this P.reverse (by intro t ht; exact h12 t (by simpa using ht)), rsKf]
    cases e.1 <;> simp [kindElem, Tok.all, Tok.ex, rsKf]

end RsResolveSpec

theorem kindsP_spec {qn ks : Fin k} (hne : qn ≠ ks) {B : Nat} (qs : List (Bool × Name)) {L : Lists k}
    (hqn : L qn = qnList qs) (hks : L ks = []) (hB : LenOK B L) (hBq : (qnList qs).length + 2 ≤ B) :
    ∃ T, Runs (LenOK B) (kindsP qn ks) L ((L.set qn []).set ks (stackL kindElem (qs.map Prod.fst))) T := by
  have h := RsResolveSpec.rKindsLoop (B := B) hne (qnList qs).reverse L hB (by simpa using hqn)
    (by rw [hks]; have := List.length_filterMap_le RsResolveSpec.rsKf (qnList qs).reverse; simp at this ⊢; omega)
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  rw [RsResolveSpec.rKindsList, hks] at hT
  simpa [stackL] using hT

end Complexity
