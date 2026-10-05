import Complexity.TqbfDecode
import Complexity.QbfCodec

/-!
# Specification of the decoding programs

`tokenize_spec` (bits to tokens) and `decodeP_spec` (tokens to the quantifier list and the matrix list).
-/

namespace Complexity

variable {k : Nat}

/-! ## Generic helpers -/

section helpers

theorem lenOK_set {B : Nat} {L : Lists k} (h : LenOK B L) (i : Fin k) {l : List Nat} (hl : l.length + 2 ≤ B) :
    LenOK B (L.set i l) := by
  intro j
  by_cases hj : j = i
  · subst hj; rw [Lists.set_same]; exact hl
  · rw [Lists.set_ne _ _ hj]; exact h j

theorem LExec.q_end {Q : Lists k → Prop} {p : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k}
    (h : LExec Q p L t o) : ∀ L', o = .cont L' → Q L' := by
  induction h with
  | push _ h2 => intro L' h; cases h; exact h2
  | pop _ h2 => intro L' h; cases h; exact h2
  | copy _ _ h2 => intro L' h; cases h; exact h2
  | halt _ => intro L' h; cases h
  | seqC _ _ _ ih2 => exact ih2
  | seqS _ => intro L' h; cases h
  | iteT _ _ _ ih => exact ih
  | iteF _ _ _ ih => exact ih
  | loopF hq _ => intro L' h; cases h; exact hq
  | loopC _ _ _ _ _ ih2 => exact ih2
  | loopS _ _ _ => intro L' h; cases h

theorem Runs.q_end {Q : Lists k → Prop} {p : LProg k} {L L' : Lists k} {T : Nat} (h : Runs Q p L L' T) : Q L' :=
  let ⟨_, _, hx⟩ := h; hx.q_end _ rfl

theorem Runs.loopStep {Q : Lists k → Prop} {i : Fin k} {c : Nat → Bool} {p : LProg k} {L L₁ L₂ : Lists k}
    {T₁ T₂ : Nat} (hq : Q L) (hc : c (lastSym (L i)) = true) (h₁ : Runs Q p L L₁ T₁)
    (h₂ : Runs Q (.loop i c p) L₁ L₂ T₂) : Runs Q (.loop i c p) L L₂ (T₁ + 1 + T₂) :=
  let ⟨t₁, ht₁, hx₁⟩ := h₁; let ⟨t₂, ht₂, hx₂⟩ := h₂
  ⟨t₁ + 1 + t₂, by omega, .loopC hq hc hx₁ hx₂⟩

theorem Runs.loopEnd {Q : Lists k → Prop} {i : Fin k} {c : Nat → Bool} {p : LProg k} {L : Lists k}
    (hq : Q L) (hc : c (lastSym (L i)) = false) : Runs Q (.loop i c p) L L 1 :=
  ⟨1, Nat.le_refl _, .loopF hq hc⟩

theorem lastSym_rev_cons (t : Nat) (r : List Nat) : lastSym (t :: r).reverse = t + 4 := by
  simp [List.reverse_cons, lastSym_append]

theorem lastSym_rev_nil : lastSym ([] : List Nat).reverse = 3 := rfl

theorem lastSym_snoc_rev (t : Nat) (r : List Nat) : lastSym (r.reverse ++ [t]) = t + 4 := lastSym_append _ _

/-- Pointwise runs of the basic instructions. -/
theorem rPush {B : Nat} {i : Fin k} (e : Nat) {L : Lists k} (hL : LenOK B L) (hi : (L i).length + 3 ≤ B) :
    ∃ L', Runs (LenOK B) (.push i e) L L' 1 ∧ L' i = L i ++ [e] ∧ ∀ x, x ≠ i → L' x = L x := by
  have h2 : LenOK B (L.set i (L i ++ [e])) := lenOK_set hL i (by simp; omega)
  exact ⟨_, runs_push hL h2, by simp, fun x hx => Lists.set_ne _ _ hx⟩

theorem rPop {B : Nat} {i : Fin k} {L : Lists k} (hL : LenOK B L) :
    ∃ L', Runs (LenOK B) (.pop i) L L' 1 ∧ L' i = (L i).dropLast ∧ ∀ x, x ≠ i → L' x = L x := by
  have h2 : LenOK B (L.set i (L i).dropLast) :=
    lenOK_set hL i (by have := hL i; have := List.length_dropLast (xs := L i); omega)
  exact ⟨_, runs_pop hL h2, by simp, fun x hx => Lists.set_ne _ _ hx⟩

theorem rMoveTop {B : Nat} {i j : Fin k} (hij : i ≠ j) {L : Lists k} {l : List Nat} {e : Nat} (hL : LenOK B L)
    (hi : L i = l ++ [e]) (hj : (L j).length + 3 ≤ B) :
    ∃ L', Runs (LenOK B) (moveTop i j) L L' 2 ∧ L' i = l ∧ L' j = L j ++ [e] ∧
      ∀ x, x ≠ i → x ≠ j → L' x = L x := by
  have h1 : LenOK B (L.set j (L j ++ (L i).getLast?.toList)) :=
    lenOK_set hL j (by simp [hi]; omega)
  have h2 : LenOK B (L.moveTop i j) := by
    unfold Lists.moveTop
    exact lenOK_set h1 i (by
      have := hL i; have := List.length_dropLast (xs := L i)
      omega)
  refine ⟨_, runs_moveTop hij hL h1 h2, ?_, ?_, fun x hx hx' => moveTop_other hx hx'⟩
  · rw [moveTop_i, hi]; simp
  · rw [moveTop_j hij, hi]; simp

end helpers

/-! ## Tokenizing -/

def bn (w : List Bool) : List Nat := (w.map (fun b : Bool => if b then 1 else 0)).reverse

theorem bn_cons (b : Bool) (w : List Bool) : bn (b :: w) = bn w ++ [if b then 1 else 0] := by
  simp [bn]

theorem readBits_run {a tk : Fin k} (hat : a ≠ tk) {B : Nat} :
    ∀ (n : Nat) (bs w : List Bool) (L : Lists k), LenOK B L → L a = bn w → (L tk).length + 3 ≤ B →
    ∃ T L', Runs (LenOK B) (readBitsP a tk n bs) L L' T ∧
      (if n ≤ w.length then L' a = bn (w.drop n) ∧ L' tk = L tk ++ [bitsTokL (bs ++ w.take n)]
        else L' a = [] ∧ L' tk = L tk) ∧ ∀ x, x ≠ a → x ≠ tk → L' x = L x := by
  intro n
  induction n with
  | zero =>
    intro bs w L hL ha htk
    obtain ⟨L', hr, h1, h2⟩ := rPush (i := tk) (bitsTokL bs) hL htk
    refine ⟨_, L', hr, ?_, fun x hx hx' => h2 x hx'⟩
    simp only [Nat.zero_le, if_true, List.drop_zero, List.take_zero, List.append_nil]
    exact ⟨by rw [h2 a hat, ha], h1⟩
  | succ n ih =>
    intro bs w L hL ha htk
    cases w with
    | nil =>
      have hs : (L a) = [] := by rw [ha]; rfl
      have hc : nonEmpty (lastSym (L a)) = false := by rw [hs]; rfl
      refine ⟨_, L, Runs.iteF hL hc (runs_skip a hL), ?_, fun _ _ _ => rfl⟩
      simp [hs]
    | cons b w =>
      have hs : L a = bn w ++ [if b then 1 else 0] := by rw [ha, bn_cons]
      have hc : nonEmpty (lastSym (L a)) = true := by rw [hs, lastSym_append]; rfl
      have key : ∀ b' : Bool, b' = b → ∃ T L', Runs (LenOK B) (.seq (.pop a) (readBitsP a tk n (bs ++ [b']))) L L' T ∧
          (if n + 1 ≤ (b :: w).length then L' a = bn ((b :: w).drop (n + 1)) ∧
              L' tk = L tk ++ [bitsTokL (bs ++ (b :: w).take (n + 1))]
            else L' a = [] ∧ L' tk = L tk) ∧ ∀ x, x ≠ a → x ≠ tk → L' x = L x := by
        intro b' hb'
        subst hb'
        obtain ⟨L1, hr1, h1a, h1x⟩ := rPop (i := a) hL
        have hL1 := hr1.q_end
        have ha1 : L1 a = bn w := by rw [h1a, hs]; simp [bn]
        obtain ⟨T, L2, hr2, hp, hx⟩ := ih (bs ++ [b']) w L1 hL1 ha1 (by rw [h1x tk (Ne.symm hat)]; exact htk)
        refine ⟨1 + T, L2, hr1.seq hr2, ?_, fun x hx1 hx2 => by rw [hx x hx1 hx2, h1x x hx1]⟩
        rw [h1x tk (Ne.symm hat)] at hp
        by_cases hn : n ≤ w.length
        · simp only [hn, if_true, List.length_cons, Nat.add_le_add_iff_right, List.drop_succ_cons, List.take_succ_cons] at hp ⊢
          simpa [List.append_assoc] using hp
        · have hn' : ¬ (n + 1 ≤ (b' :: w).length) := by simp; omega
          rw [if_neg hn] at hp
          rw [if_neg hn']
          exact hp
      cases b with
      | true =>
        have hc2 : symIs 1 (lastSym (L a)) = true := by rw [hs, lastSym_append]; rfl
        obtain ⟨T, L', hr, hp, hx⟩ := key true rfl
        exact ⟨T + 1 + 1, L', Runs.iteT hL hc (Runs.iteT hL hc2 hr) |>.mono (by omega), hp, hx⟩
      | false =>
        have hc2 : symIs 1 (lastSym (L a)) = false := by rw [hs, lastSym_append]; rfl
        obtain ⟨T, L', hr, hp, hx⟩ := key false rfl
        exact ⟨T + 1 + 1, L', Runs.iteT hL hc (Runs.iteF hL hc2 hr) |>.mono (by omega), hp, hx⟩

theorem tokLoop_run {a tk : Fin k} (hat : a ≠ tk) {B : Nat} :
    ∀ (m : Nat) (w : List Bool) (L : Lists k) (acc : List Nat), w.length = m → LenOK B L → L a = bn w →
      L tk = acc → acc.length + w.length + 2 ≤ B →
      ∃ T L', Runs (LenOK B) (tokenizeP a tk) L L' T ∧ L' a = [] ∧ L' tk = acc ++ ofBits w ∧
        ∀ x, x ≠ a → x ≠ tk → L' x = L x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro w L acc hm hL ha htk hB
    cases w with
    | nil =>
      have hc : nonEmpty (lastSym (L a)) = false := by rw [ha]; rfl
      refine ⟨1, L, Runs.loopEnd hL hc, by rw [ha]; rfl, ?_, fun _ _ _ => rfl⟩
      simp [htk, ofBits]
    | cons b0 w0 =>
      have hs : L a = bn w0 ++ [if b0 then 1 else 0] := by rw [ha, bn_cons]
      have hc : nonEmpty (lastSym (L a)) = true := by rw [hs, lastSym_append]; rfl
      obtain ⟨T1, L1, hr1, hp, hx⟩ := readBits_run hat 4 [] (b0 :: w0) L hL ha (by rw [htk]; simp at hB ⊢; omega)
      by_cases h4 : 4 ≤ (b0 :: w0).length
      · rw [if_pos h4] at hp
        obtain ⟨hpa, hptk⟩ := hp
        rcases w0 with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, w3⟩⟩⟩
        · simp at h4
        · simp at h4
        · simp at h4
        · simp only [List.length_cons] at hm hB
          obtain ⟨T2, L2, hr2, h2a, h2tk, h2x⟩ :=
            ih w3.length (by omega) w3 L1 (acc ++ [bitsTokL [b0, b1, b2, b3]]) rfl hr1.q_end
              (by rw [hpa]; simp [bn]) (by rw [hptk, htk]; simp [bitsTokL]) (by simp; omega)
          refine ⟨T1 + 1 + T2, L2, Runs.loopStep hL hc hr1 hr2, h2a, ?_, fun x h1 h2 => by rw [h2x x h1 h2, hx x h1 h2]⟩
          rw [h2tk]
          simp [ofBits, bitsTokL, List.append_assoc]
      · rw [if_neg h4] at hp
        obtain ⟨hpa, hptk⟩ := hp
        have hc2 : nonEmpty (lastSym (L1 a)) = false := by rw [hpa]; rfl
        refine ⟨T1 + 1 + 1, L1, Runs.loopStep hL hc hr1 (Runs.loopEnd hr1.q_end hc2) |>.mono (by omega), hpa, ?_, hx⟩
        rw [hptk, htk]
        rcases w0 with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, w3⟩⟩⟩
        · simp [ofBits]
        · simp [ofBits]
        · simp [ofBits]
        · simp at h4

theorem tokenize_spec {a tk : Fin k} (hat : a ≠ tk) {B : Nat} (w : List Bool) {L : Lists k}
    (ha : L a = (w.map (fun b : Bool => if b then 1 else 0)).reverse) (htk : L tk = [])
    (hB : LenOK B L) (hBw : w.length + 2 ≤ B) :
    ∃ T, Runs (LenOK B) (tokenizeP a tk) L ((L.set a []).set tk (ofBits w)) T := by
  obtain ⟨T, L', hr, h1, h2, h3⟩ := tokLoop_run hat w.length w L [] rfl hB ha htk (by simpa using hBw)
  refine ⟨T, ?_⟩
  have : L' = (L.set a []).set tk (ofBits w) := by
    funext x
    by_cases hx : x = tk
    · subst hx; rw [Lists.set_same]; simpa using h2
    · by_cases hx' : x = a
      · subst hx'; rw [Lists.set_ne _ _ hx, Lists.set_same]; exact h1
      · rw [Lists.set_ne _ _ hx, Lists.set_ne _ _ hx']; exact h3 x hx' hx
  rw [← this]; exact hr

/-! ## Functional facts about decoding -/

theorem countOnes_len (ts : List Nat) : (countOnes ts).1 + (countOnes ts).2.length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t = Tok.one
    · simp [countOnes, h]; omega
    · simp [countOnes, h]

/-- `parseName` with the canonical fuel. -/
def pnm (ts : List Nat) : Name × List Nat := parseName ts.length ts

theorem parseName_fuel : ∀ (f₁ f₂ : Nat) (ts : List Nat), ts.length ≤ f₁ → ts.length ≤ f₂ →
    parseName f₁ ts = parseName f₂ ts := by
  intro f₁
  induction f₁ with
  | zero =>
    intro f₂ ts h1 h2
    have : ts = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    cases f₂ <;> simp [parseName, countOnes]
  | succ f ih =>
    intro f₂ ts h1 h2
    cases f₂ with
    | zero =>
      have : ts = [] := List.length_eq_zero_iff.1 (by omega)
      subst this
      simp [parseName, countOnes]
    | succ g =>
      have hc := countOnes_len ts
      simp only [parseName]
      generalize hcn : countOnes ts = c at hc
      obtain ⟨n, rest⟩ := c
      cases rest with
      | nil => simp
      | cons t r =>
        simp only [List.length_cons] at hc
        by_cases hs : t = Tok.sep
        · simp only [hs, if_true]
          rw [ih g r (by omega) (by omega)]
        · simp [hs]

theorem pnm_eq (ts : List Nat) : pnm ts = match countOnes ts with
    | (n, t :: r) => if t = Tok.sep then (n :: (pnm r).1, (pnm r).2) else if t = Tok.fin then ([], r) else ([], t :: r)
    | (_, []) => ([], []) := by
  cases ts with
  | nil => simp [pnm, parseName, countOnes]
  | cons t ts' =>
    have hc := countOnes_len (t :: ts')
    unfold pnm
    simp only [List.length_cons, parseName]
    simp only [List.length_cons] at hc
    generalize hcn : countOnes (t :: ts') = c at hc
    obtain ⟨n, rest⟩ := c
    cases rest with
    | nil => simp
    | cons t' r =>
      simp only [List.length_cons] at hc
      by_cases hs : t' = Tok.sep
      · simp only [hs, if_true]
        have := parseName_fuel ts'.length r.length r (by omega) (by omega)
        simp only [this]
      · simp [hs]

theorem pnm_facts : ∀ (m : Nat) (ts : List Nat), ts.length = m →
    (pnm ts).2.length ≤ ts.length ∧ (encName (pnm ts).1).length + (pnm ts).2.length ≤ ts.length + 1 := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro ts hm
    have hc := countOnes_len ts
    rw [pnm_eq]
    generalize hcn : countOnes ts = c at hc
    obtain ⟨n, rest⟩ := c
    cases rest with
    | nil => simp [encName]
    | cons t r =>
      simp only [List.length_cons] at hc
      by_cases hs : t = Tok.sep
      · simp only [hs, if_true]
        obtain ⟨h1, h2⟩ := ih r.length (by omega) r rfl
        rw [encName_cons]
        simp only [List.length_append, List.length_replicate, List.length_cons]
        omega
      · by_cases hf : t = Tok.fin
        · simp [hf, encName, Tok.fin, Tok.sep]; omega
        · simp [hs, hf, encName]; omega


attribute [local simp] Tok.one Tok.sep Tok.fin Tok.all Tok.ex Tok.var Tok.tt Tok.ff Tok.neg Tok.conj Tok.disj

def dec (ts : List Nat) : Qbf := decodeToks (ts.length + 1) ts

theorem decodeToks_fuel : ∀ (f₁ f₂ : Nat) (ts : List Nat), ts.length + 1 ≤ f₁ → ts.length + 1 ≤ f₂ →
    decodeToks f₁ ts = decodeToks f₂ ts := by
  intro f₁
  induction f₁ with
  | zero => intro f₂ ts h; omega
  | succ f ih =>
    intro f₂ ts h1 h2
    cases f₂ with
    | zero => omega
    | succ g =>
      cases ts with
      | nil => simp [decodeToks]
      | cons t ts' =>
        have hpn : (parseName ts'.length ts').2.length ≤ ts'.length := (pnm_facts _ ts' rfl).1
        simp only [List.length_cons] at h1 h2
        simp only [decodeToks]
        generalize parseName ts'.length ts' = q at hpn ⊢
        obtain ⟨x, r⟩ := q
        have hA : decodeToks f r = decodeToks g r := ih g r (by simp at hpn; omega) (by simp at hpn; omega)
        have hB : decodeToks f ts' = decodeToks g ts' := ih g ts' (by omega) (by omega)
        simp only [hA, hB]

/-- One pass of `decodeToks` on the token `t` followed by `ts`: remaining input, quantifier output, matrix output. -/
def decStep (t : Nat) (ts : List Nat) : List Nat × List Nat × List Nat :=
  if t = Tok.all ∨ t = Tok.ex then ((pnm ts).2, t :: encName (pnm ts).1, [])
  else if t = Tok.var then ((pnm ts).2, [], t :: encName (pnm ts).1)
  else if t = Tok.tt ∨ t = Tok.ff ∨ t = Tok.neg ∨ t = Tok.conj ∨ t = Tok.disj then (ts, [], [t])
  else (ts, [], [])

theorem decStep_facts (t : Nat) (ts : List Nat) :
    (decStep t ts).1.length ≤ ts.length ∧
    (decStep t ts).2.1.length + (decStep t ts).2.2.length + 2 * (decStep t ts).1.length ≤ 2 * (ts.length + 1) := by
  obtain ⟨h1, h2⟩ := pnm_facts _ ts rfl
  by_cases ha : t = 4 ∨ t = 5
  · simp [decStep, ha]; omega
  · by_cases hv : t = 6
    · simp [decStep, ha, hv]; omega
    · by_cases ho : t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11
      · simp [decStep, ha, hv, ho]; omega
      · simp [decStep, ha, hv, ho]; omega

theorem dec_cons (t : Nat) (ts : List Nat) :
    qnList (dec (t :: ts)).quants = (decStep t ts).2.1 ++ qnList (dec (decStep t ts).1).quants ∧
    mtList (dec (t :: ts)).matrix = (decStep t ts).2.2 ++ mtList (dec (decStep t ts).1).matrix := by
  have hpn : (pnm ts).2.length ≤ ts.length := (pnm_facts _ ts rfl).1
  have hdec : ∀ r : List Nat, r.length ≤ ts.length → decodeToks (ts.length + 1) r = decodeToks (r.length + 1) r :=
    fun r hr => decodeToks_fuel _ _ r (by omega) (by omega)
  unfold dec
  simp only [List.length_cons, decodeToks]
  have hP : parseName ts.length ts = pnm ts := rfl
  rw [hP]
  generalize hq : pnm ts = q at hpn
  obtain ⟨x, r⟩ := q
  simp only [] at hpn
  by_cases ha : t = 4 ∨ t = 5
  · rcases ha with rfl | rfl <;> simp [decStep, qnList, mtList, hq, hdec r hpn]
  · by_cases hv : t = 6
    · subst hv; simp [decStep, qnList, mtList, RTok.enc, hq, hdec r hpn]
    · by_cases ho : t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11
      · rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp [decStep, qnList, mtList, RTok.enc]
      · have ho' := ho
        simp only [not_or] at ho'
        obtain ⟨h7, h8, h9, h10, h11⟩ := ho'
        simp [decStep, ha, hv, ho, h7, h8, h9, h10, h11]

/-! ## Machine lemmas for the name reader -/

theorem exists_snoc {α : Type} {l : List α} (h : l ≠ []) : ∃ l' e, l = l' ++ [e] :=
  ⟨l.dropLast, l.getLast h, (List.dropLast_concat_getLast h).symm⟩

theorem moveAll_run {B : Nat} {i j : Fin k} (hij : i ≠ j) :
    ∀ (n : Nat) (L : Lists k), (L i).length = n → LenOK B L → (L i).length + (L j).length + 2 ≤ B →
    ∃ T L', Runs (LenOK B) (moveAll i j) L L' T ∧ L' i = [] ∧ L' j = L j ++ (L i).reverse ∧
      ∀ x, x ≠ i → x ≠ j → L' x = L x := by
  intro n
  induction n with
  | zero =>
    intro L hn hL _
    have h0 : L i = [] := List.length_eq_zero_iff.1 hn
    have hc : (fun s : Nat => s != 3) (lastSym (L i)) = false := by rw [h0]; rfl
    exact ⟨1, L, Runs.loopEnd hL hc, h0, by rw [h0]; simp, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro L hn hL hB
    obtain ⟨l, e, hl⟩ := exists_snoc (l := L i) (by intro h; rw [h] at hn; simp at hn)
    have hc : (fun s : Nat => s != 3) (lastSym (L i)) = true := by rw [hl, lastSym_append]; simp
    rw [hl] at hB
    simp only [List.length_append, List.length_singleton] at hB
    obtain ⟨L1, hr1, h1i, h1j, h1x⟩ := rMoveTop hij hL hl (by omega)
    obtain ⟨T, L2, hr2, h2i, h2j, h2x⟩ := ih L1 (by rw [h1i]; rw [hl] at hn; simpa using hn) hr1.q_end
      (by rw [h1i, h1j]; simp; omega)
    refine ⟨2 + 1 + T, L2, Runs.loopStep hL hc hr1 hr2, h2i, ?_, fun x hx hx' => by rw [h2x x hx hx', h1x x hx hx']⟩
    rw [h2j, h1j, h1i, hl]; simp

theorem clearAll_run {B : Nat} {i : Fin k} :
    ∀ (n : Nat) (L : Lists k), (L i).length = n → LenOK B L →
    ∃ T L', Runs (LenOK B) (nameStepP.clearAll i) L L' T ∧ L' i = [] ∧ ∀ x, x ≠ i → L' x = L x := by
  intro n
  induction n with
  | zero =>
    intro L hn hL
    have h0 : L i = [] := List.length_eq_zero_iff.1 hn
    have hc : nonEmpty (lastSym (L i)) = false := by rw [h0]; rfl
    exact ⟨1, L, Runs.loopEnd hL hc, h0, fun _ _ => rfl⟩
  | succ n ih =>
    intro L hn hL
    obtain ⟨l, e, hl⟩ := exists_snoc (l := L i) (by intro h; rw [h] at hn; simp at hn)
    have hc : nonEmpty (lastSym (L i)) = true := by rw [hl, lastSym_append]; rfl
    obtain ⟨L1, hr1, h1i, h1x⟩ := rPop (i := i) hL
    obtain ⟨T, L2, hr2, h2i, h2x⟩ := ih L1 (by rw [h1i, hl]; rw [hl] at hn; simpa using hn) hr1.q_end
    exact ⟨1 + 1 + T, L2, Runs.loopStep hL hc hr1 hr2, h2i, fun x hx => by rw [h2x x hx, h1x x hx]⟩

theorem ones_run {B : Nat} {tk buf : Fin k} (htb : tk ≠ buf) :
    ∀ (ts : List Nat) (L : Lists k), LenOK B L → L tk = ts.reverse → (L buf).length + ts.length + 2 ≤ B →
    ∃ T L', Runs (LenOK B) (.loop tk (symIs Tok.one) (moveTop tk buf)) L L' T ∧
      L' tk = (countOnes ts).2.reverse ∧ L' buf = L buf ++ List.replicate (countOnes ts).1 Tok.one ∧
      ∀ x, x ≠ tk → x ≠ buf → L' x = L x := by
  intro ts
  induction ts with
  | nil =>
    intro L hL htk _
    have hc : symIs Tok.one (lastSym (L tk)) = false := by rw [htk]; rfl
    exact ⟨1, L, Runs.loopEnd hL hc, by rw [htk]; simp [countOnes], by simp [countOnes], fun _ _ _ => rfl⟩
  | cons t ts ih =>
    intro L hL htk hB
    simp only [List.length_cons] at hB
    by_cases ht : t = 1
    · have hc : symIs Tok.one (lastSym (L tk)) = true := by rw [htk, lastSym_rev_cons]; simp [symIs, ht]
      obtain ⟨L1, hr1, h1i, h1j, h1x⟩ := rMoveTop htb hL (l := ts.reverse) (e := t) (by rw [htk]; simp) (by omega)
      obtain ⟨T, L2, hr2, h2t, h2b, h2x⟩ := ih L1 hr1.q_end h1i (by rw [h1j]; simp; omega)
      refine ⟨2 + 1 + T, L2, Runs.loopStep hL hc hr1 hr2, ?_, ?_, fun x hx hx' => by rw [h2x x hx hx', h1x x hx hx']⟩
      · rw [h2t]; simp [countOnes, ht]
      · rw [h2b, h1j]; simp [countOnes, ht, List.replicate_succ, List.append_assoc]
    · have hc : symIs Tok.one (lastSym (L tk)) = false := by
        rw [htk, lastSym_rev_cons]; simp [symIs, Tok.one] at ht ⊢; omega
      exact ⟨1, L, Runs.loopEnd hL hc, by rw [htk]; simp [countOnes, ht], by simp [countOnes, ht], fun _ _ _ => rfl⟩


theorem finTail_run {B : Nat} {d fl : Fin k} (hfd : fl ≠ d) {L : Lists k} (hL : LenOK B L)
    (hd : (L d).length + 3 ≤ B) (hfl : L fl = [0]) :
    ∃ T L', Runs (LenOK B) (.seq (.push d Tok.fin) (.pop fl)) L L' T ∧ L' d = L d ++ [Tok.fin] ∧ L' fl = [] ∧
      ∀ x, x ≠ d → x ≠ fl → L' x = L x := by
  obtain ⟨L1, hr1, h1d, h1x⟩ := rPush (i := d) Tok.fin hL hd
  obtain ⟨L2, hr2, h2f, h2x⟩ := rPop (i := fl) hr1.q_end
  refine ⟨1 + 1, L2, hr1.seq hr2, ?_, ?_, fun x hx hx' => by rw [h2x x hx', h1x x hx]⟩
  · rw [h2x d (Ne.symm hfd), h1d]
  · rw [h2f, h1x fl hfd, hfl]; rfl

theorem nameLoop_run {tk buf d fl : Fin k} (htb : tk ≠ buf) (htd : tk ≠ d) (hbd : buf ≠ d) (hft : fl ≠ tk)
    (hfb : fl ≠ buf) (hfd : fl ≠ d) {B : Nat} :
    ∀ (m : Nat) (ts : List Nat), ts.length = m → ∀ (L : Lists k) (da : List Nat), LenOK B L →
      L tk = ts.reverse → L buf = [] → L fl = [0] → L d = da → ts.length + 2 ≤ B →
      da.length + (encName (pnm ts).1).length + 2 ≤ B →
    ∃ T L', Runs (LenOK B) (.loop fl nonEmpty (nameStepP tk buf d fl)) L L' T ∧
      L' tk = (pnm ts).2.reverse ∧ L' buf = [] ∧ L' fl = [] ∧ L' d = da ++ encName (pnm ts).1 ∧
      ∀ x, x ≠ tk → x ≠ buf → x ≠ d → x ≠ fl → L' x = L x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro ts hm L da hL htk hbuf hfl hdd hts hda
    have hc : nonEmpty (lastSym (L fl)) = true := by rw [hfl]; rfl
    have hcl := countOnes_len ts
    obtain ⟨T1, L1, hr1, h1t, h1b, h1x⟩ := ones_run htb ts L hL htk (by rw [hbuf]; simpa using hts)
    have hL1 := hr1.q_end
    have hpn := pnm_eq ts
    have h1d : L1 d = da := by rw [h1x d (Ne.symm htd) (Ne.symm hbd), hdd]
    have h1f : L1 fl = [0] := by rw [h1x fl hft hfb, hfl]
    generalize hcn : countOnes ts = c at hcl hpn h1t h1b
    obtain ⟨n, rest⟩ := c
    dsimp only at hcl h1t h1b
    have h1b' : L1 buf = List.replicate n Tok.one := by rw [h1b, hbuf]; simp
    cases rest with
    | nil =>
      have hp : pnm ts = ([], []) := hpn
      have hed : encName (pnm ts).1 = [Tok.fin] := by rw [hp]; rfl
      rw [hed] at hda
      have hcs : symIs Tok.sep (lastSym (L1 tk)) = false := by simp [h1t, symIs, lastSym]
      have hcf : symIs Tok.fin (lastSym (L1 tk)) = false := by simp [h1t, symIs, lastSym]
      obtain ⟨T2, L2, hr2, h2b, h2x⟩ := clearAll_run (i := buf) (L1 buf).length L1 rfl hL1
      have hL2 := hr2.q_end
      have h2d : L2 d = da := by rw [h2x d (Ne.symm hbd), h1d]
      have h2f : L2 fl = [0] := by rw [h2x fl hfb, h1f]
      obtain ⟨T3, L3, hr3, h3d, h3f, h3x⟩ := finTail_run hfd hL2 (by rw [h2d]; simp at hda ⊢; omega) h2f
      have hL3 := hr3.q_end
      have hc3 : nonEmpty (lastSym (L3 fl)) = false := by rw [h3f]; rfl
      obtain ⟨Tx, hstep⟩ : ∃ T, Runs (LenOK B) (nameStepP tk buf d fl) L L3 T :=
        ⟨_, by unfold nameStepP; exact hr1.seq (Runs.iteF hL1 hcs (Runs.iteF hL1 hcf (hr2.seq hr3)))⟩
      refine ⟨_, L3, Runs.loopStep hL hc hstep (Runs.loopEnd hL3 hc3), ?_, ?_, h3f, ?_, ?_⟩
      · rw [hp, h3x tk htd (Ne.symm hft), h2x tk htb, h1t]
      · rw [h3x buf hbd hfb.symm, h2b]
      · rw [h3d, h2d, hed]
      · intro x hx1 hx2 hx3 hx4
        rw [h3x x hx3 hx4, h2x x hx2, h1x x hx1 hx2]
    | cons t r =>
      simp only [List.length_cons] at hcl
      have h1t' : L1 tk = r.reverse ++ [t] := by rw [h1t]; simp
      have hcnt : lastSym (L1 tk) = t + 4 := by rw [h1t', lastSym_append]
      by_cases hs : t = Tok.sep
      · subst hs
        have hp : pnm ts = (n :: (pnm r).1, (pnm r).2) := by rw [hpn]; simp
        have hlen : (encName (pnm ts).1).length = n + 1 + (encName (pnm r).1).length := by
          rw [hp, encName_cons]; simp <;> omega
        rw [hlen] at hda
        have hcs : symIs Tok.sep (lastSym (L1 tk)) = true := by rw [hcnt]; simp [symIs]
        obtain ⟨T2, L2, hr2, h2b, h2d', h2x⟩ := moveAll_run (B := B) hbd (L1 buf).length L1 rfl hL1
          (by rw [h1b', h1d]; simp; omega)
        have hL2 := hr2.q_end
        obtain ⟨L3, hr3, h3t, h3x⟩ := rPop (i := tk) hL2
        have hL3 := hr3.q_end
        have h2t : L2 tk = r.reverse ++ [Tok.sep] := by rw [h2x tk htb htd, h1t']
        have h2d : L2 d = da ++ List.replicate n Tok.one := by rw [h2d', h1d, h1b']; simp
        have h3d : L3 d = da ++ List.replicate n Tok.one := by rw [h3x d (Ne.symm htd), h2d]
        obtain ⟨L4, hr4, h4d, h4x⟩ := rPush (i := d) Tok.sep hL3 (by rw [h3d]; simp; omega)
        have hL4 := hr4.q_end
        have h4t : L4 tk = r.reverse := by
          rw [h4x tk htd, h3t, h2t]; simp
        have h4b : L4 buf = [] := by rw [h4x buf hbd, h3x buf (Ne.symm htb), h2b]
        have h4f : L4 fl = [0] := by
          rw [h4x fl hfd, h3x fl hft, h2x fl hfb hfd, h1f]
        obtain ⟨T5, L5, hr5, h5t, h5b, h5f, h5d, h5x⟩ := ih r.length (by omega) r rfl L4
          (da ++ List.replicate n Tok.one ++ [Tok.sep]) hL4 h4t h4b h4f (by rw [h4d, h3d])
          (by omega) (by simp; omega)
        obtain ⟨Tx, hstep⟩ : ∃ T, Runs (LenOK B) (nameStepP tk buf d fl) L L4 T :=
          ⟨_, by
            unfold nameStepP
            exact hr1.seq (Runs.iteT hL1 hcs (hr2.seq (hr3.seq hr4)))⟩
        refine ⟨_, L5, Runs.loopStep hL hc hstep hr5, ?_, h5b, h5f, ?_, ?_⟩
        · rw [hp]; exact h5t
        · rw [h5d, hp, encName_cons]; simp [List.append_assoc]
        · intro x hx1 hx2 hx3 hx4
          rw [h5x x hx1 hx2 hx3 hx4, h4x x hx3, h3x x hx1, h2x x hx2 hx3, h1x x hx1 hx2]
      · by_cases hf : t = Tok.fin
        · subst hf
          have hp : pnm ts = ([], r) := by rw [hpn]; simp
          have hed : encName (pnm ts).1 = [Tok.fin] := by rw [hp]; rfl
          rw [hed] at hda
          have hcs : symIs Tok.sep (lastSym (L1 tk)) = false := by rw [hcnt]; simp [symIs]
          have hcf : symIs Tok.fin (lastSym (L1 tk)) = true := by rw [hcnt]; simp [symIs]
          obtain ⟨T2, L2, hr2, h2b, h2x⟩ := clearAll_run (i := buf) (L1 buf).length L1 rfl hL1
          have hL2 := hr2.q_end
          obtain ⟨L3, hr3, h3t, h3x⟩ := rPop (i := tk) hL2
          have hL3 := hr3.q_end
          have h2d : L2 d = da := by rw [h2x d (Ne.symm hbd), h1d]
          have h3d : L3 d = da := by rw [h3x d (Ne.symm htd), h2d]
          have h3f : L3 fl = [0] := by rw [h3x fl hft, h2x fl hfb, h1f]
          obtain ⟨T4, L4, hr4, h4d, h4f, h4x⟩ := finTail_run hfd hL3 (by rw [h3d]; simp at hda ⊢; omega) h3f
          have hL4 := hr4.q_end
          have hc4 : nonEmpty (lastSym (L4 fl)) = false := by rw [h4f]; rfl
          obtain ⟨Tx, hstep⟩ : ∃ T, Runs (LenOK B) (nameStepP tk buf d fl) L L4 T :=
            ⟨_, by
              unfold nameStepP
              exact hr1.seq (Runs.iteF hL1 hcs (Runs.iteT hL1 hcf (hr2.seq (hr3.seq hr4))))⟩
          refine ⟨_, L4, Runs.loopStep hL hc hstep (Runs.loopEnd hL4 hc4), ?_, ?_, h4f, ?_, ?_⟩
          · rw [hp, h4x tk htd (Ne.symm hft), h3t, h2x tk htb, h1t']; simp
          · rw [h4x buf hbd hfb.symm, h3x buf (Ne.symm htb), h2b]
          · rw [h4d, h3d, hed]
          · intro x hx1 hx2 hx3 hx4
            rw [h4x x hx3 hx4, h3x x hx1, h2x x hx2, h1x x hx1 hx2]
        · have hs' : t ≠ 2 := hs
          have hf' : t ≠ 3 := hf
          have hp : pnm ts = ([], t :: r) := by rw [hpn]; simp [hs', hf']
          have hed : encName (pnm ts).1 = [Tok.fin] := by rw [hp]; rfl
          rw [hed] at hda
          have hcs : symIs Tok.sep (lastSym (L1 tk)) = false := by
            rw [hcnt]; simp [symIs, Tok.sep] at hs ⊢; omega
          have hcf : symIs Tok.fin (lastSym (L1 tk)) = false := by
            rw [hcnt]; simp [symIs, Tok.fin] at hf ⊢; omega
          obtain ⟨T2, L2, hr2, h2b, h2x⟩ := clearAll_run (i := buf) (L1 buf).length L1 rfl hL1
          have hL2 := hr2.q_end
          have h2d : L2 d = da := by rw [h2x d (Ne.symm hbd), h1d]
          have h2f : L2 fl = [0] := by rw [h2x fl hfb, h1f]
          obtain ⟨T3, L3, hr3, h3d, h3f, h3x⟩ := finTail_run hfd hL2 (by rw [h2d]; simp at hda ⊢; omega) h2f
          have hL3 := hr3.q_end
          have hc3 : nonEmpty (lastSym (L3 fl)) = false := by rw [h3f]; rfl
          obtain ⟨Tx, hstep⟩ : ∃ T, Runs (LenOK B) (nameStepP tk buf d fl) L L3 T :=
            ⟨_, by
              unfold nameStepP
              exact hr1.seq (Runs.iteF hL1 hcs (Runs.iteF hL1 hcf (hr2.seq hr3)))⟩
          refine ⟨_, L3, Runs.loopStep hL hc hstep (Runs.loopEnd hL3 hc3), ?_, ?_, h3f, ?_, ?_⟩
          · rw [hp, h3x tk htd (Ne.symm hft), h2x tk htb, h1t']; simp
          · rw [h3x buf hbd hfb.symm, h2b]
          · rw [h3d, h2d, hed]
          · intro x hx1 hx2 hx3 hx4
            rw [h3x x hx3 hx4, h2x x hx2, h1x x hx1 hx2]


theorem decName_run {tk d buf fl : Fin k} (htd : tk ≠ d) (htb : tk ≠ buf) (hbd : buf ≠ d) (hft : fl ≠ tk)
    (hfb : fl ≠ buf) (hfd : fl ≠ d) {B : Nat} (t : Nat) (ts : List Nat) {L : Lists k} (hL : LenOK B L)
    (htk : L tk = ts.reverse ++ [t]) (hbuf : L buf = []) (hfl : L fl = [])
    (hB : (L d).length + ts.length + 4 ≤ B) :
    ∃ T L', Runs (LenOK B) (.seq (moveTop tk d) (parseNameP tk buf d fl)) L L' T ∧
      L' tk = (pnm ts).2.reverse ∧ L' d = L d ++ t :: encName (pnm ts).1 ∧ L' buf = [] ∧ L' fl = [] ∧
      ∀ x, x ≠ tk → x ≠ buf → x ≠ d → x ≠ fl → L' x = L x := by
  obtain ⟨L1, hr1, h1t, h1d, h1x⟩ := rMoveTop htd hL htk (by omega)
  have hL1 := hr1.q_end
  have h1b : L1 buf = [] := by rw [h1x buf htb.symm hbd, hbuf]
  have h1f : L1 fl = [] := by rw [h1x fl hft hfd, hfl]
  obtain ⟨L2, hr2, h2f, h2x⟩ := rPush (i := fl) 0 hL1 (by rw [h1f]; simp; omega)
  have hL2 := hr2.q_end
  have hpf := pnm_facts _ ts rfl
  have h2f' : L2 fl = [0] := by rw [h2f, h1f]; rfl
  obtain ⟨T3, L3, hr3, h3t, h3b, h3f, h3d, h3x⟩ := nameLoop_run htb htd hbd hft hfb hfd (B := B) ts.length ts rfl L2
    (L d ++ [t]) hL2 (by rw [h2x tk hft.symm, h1t]) (by rw [h2x buf hfb.symm, h1b]) h2f'
    (by rw [h2x d hfd.symm, h1d]) (by have := hL2 tk; rw [h2x tk hft.symm, h1t] at this; omega)
    (by simp; omega)
  refine ⟨_, L3, hr1.seq (by unfold parseNameP; exact hr2.seq hr3), h3t, ?_, h3b, h3f, ?_⟩
  · rw [h3d]; simp
  · intro x hx1 hx2 hx3 hx4
    rw [h3x x hx1 hx2 hx3 hx4, h2x x hx4, h1x x hx1 hx3]


theorem nodup5 {a b c d e : Fin k} (h : [a, b, c, d, e].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  simp [List.nodup_cons] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem decStep_run {tk qn mt buf fl : Fin k} (hd : [tk, qn, mt, buf, fl].Nodup) {B : Nat} (t : Nat)
    (ts : List Nat) {L : Lists k} (hL : LenOK B L) (htk : L tk = ts.reverse ++ [t]) (hbuf : L buf = [])
    (hfl : L fl = []) (hB : (L qn).length + (L mt).length + 2 * (ts.length + 1) + 3 ≤ B) :
    ∃ T L', Runs (LenOK B) (decStepP tk qn mt buf fl) L L' T ∧ L' tk = (decStep t ts).1.reverse ∧
      L' qn = L qn ++ (decStep t ts).2.1 ∧ L' mt = L mt ++ (decStep t ts).2.2 ∧ L' buf = [] ∧ L' fl = [] ∧
      ∀ x, x ≠ tk → x ≠ qn → x ≠ mt → x ≠ buf → x ≠ fl → L' x = L x := by
  obtain ⟨h_tq, h_tm, h_tb, h_tf, h_qm, h_qb, h_qf, h_mb, h_mf, h_bf⟩ := nodup5 hd
  have hlast : lastSym (L tk) = t + 4 := by rw [htk, lastSym_append]
  have hpf := pnm_facts _ ts rfl
  by_cases ha : t = 4 ∨ t = 5
  · have hds : decStep t ts = ((pnm ts).2, t :: encName (pnm ts).1, []) := by
      rcases ha with rfl | rfl <;> simp [decStep]
    obtain ⟨T, L', hr, h1, h2, h3, h4, h5⟩ := decName_run (d := qn) h_tq h_tb h_qb.symm h_tf.symm h_bf.symm
      h_qf.symm t ts hL htk hbuf hfl (by omega)
    obtain ⟨T', hrun⟩ : ∃ T', Runs (LenOK B) (decStepP tk qn mt buf fl) L L' T' := by
      unfold decStepP
      rcases ha with rfl | rfl
      · exact ⟨_, Runs.iteT hL (by rw [hlast]; simp [symIs]) hr⟩
      · exact ⟨_, Runs.iteF hL (by rw [hlast]; simp [symIs]) (Runs.iteT hL (by rw [hlast]; simp [symIs]) hr)⟩
    refine ⟨_, L', hrun, by rw [hds]; exact h1, by rw [hds]; exact h2, ?_, h3, h4,
      fun x hx1 hx2 hx3 hx4 hx5 => h5 x hx1 hx4 hx2 hx5⟩
    rw [hds, h5 mt h_tm.symm h_mb h_qm.symm h_mf]; simp
  have n4 : symIs Tok.all (lastSym (L tk)) = false := by rw [hlast]; simp [symIs]; omega
  have n5 : symIs Tok.ex (lastSym (L tk)) = false := by rw [hlast]; simp [symIs]; omega
  by_cases hv : t = 6
  · subst hv
    have hds : decStep 6 ts = ((pnm ts).2, [], 6 :: encName (pnm ts).1) := by simp [decStep]
    obtain ⟨T, L', hr, h1, h2, h3, h4, h5⟩ := decName_run (d := mt) h_tm h_tb h_mb.symm h_tf.symm h_bf.symm
      h_mf.symm 6 ts hL htk hbuf hfl (by omega)
    obtain ⟨T', hrun⟩ : ∃ T', Runs (LenOK B) (decStepP tk qn mt buf fl) L L' T' := by
      unfold decStepP
      exact ⟨_, Runs.iteF hL n4 (Runs.iteF hL n5 (Runs.iteT hL (by rw [hlast]; simp [symIs]) hr))⟩
    refine ⟨_, L', hrun, by rw [hds]; exact h1, ?_, by rw [hds]; exact h2, h3, h4,
      fun x hx1 hx2 hx3 hx4 hx5 => h5 x hx1 hx4 hx3 hx5⟩
    rw [hds, h5 qn h_tq.symm h_qb h_qm h_qf]; simp
  have n6 : symIs Tok.var (lastSym (L tk)) = false := by rw [hlast]; simp [symIs]; omega
  by_cases ho : t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11
  · have hds : decStep t ts = (ts, [], [t]) := by
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp [decStep]
    obtain ⟨L1, hr1, h1t, h1m, h1x⟩ := rMoveTop h_tm hL htk (by omega)
    have hpred : (fun s : Nat => s == Tok.tt + 4 || s == Tok.ff + 4 || s == Tok.neg + 4 || s == Tok.conj + 4 ||
        s == Tok.disj + 4) (lastSym (L tk)) = true := by
      rw [hlast]; rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨T', hrun⟩ : ∃ T', Runs (LenOK B) (decStepP tk qn mt buf fl) L L1 T' := by
      unfold decStepP
      exact ⟨_, Runs.iteF hL n4 (Runs.iteF hL n5 (Runs.iteF hL n6 (Runs.iteT hL hpred hr1)))⟩
    refine ⟨_, L1, hrun, by rw [hds]; exact h1t, ?_, by rw [hds]; exact h1m, ?_, ?_,
      fun x hx1 hx2 hx3 hx4 hx5 => h1x x hx1 hx3⟩
    · rw [hds, h1x qn h_tq.symm h_qm]; simp
    · rw [h1x buf h_tb.symm h_mb.symm, hbuf]
    · rw [h1x fl h_tf.symm h_mf.symm, hfl]
  · have ho' := ho
    simp only [not_or] at ho'
    obtain ⟨h7, h8, h9, h10, h11⟩ := ho'
    have hds : decStep t ts = (ts, [], []) := by simp [decStep, ha, hv, ho, h7, h8, h9, h10, h11]
    obtain ⟨L1, hr1, h1t, h1x⟩ := rPop (i := tk) hL
    have hpred : (fun s : Nat => s == Tok.tt + 4 || s == Tok.ff + 4 || s == Tok.neg + 4 || s == Tok.conj + 4 ||
        s == Tok.disj + 4) (lastSym (L tk)) = false := by
      rw [hlast]; simp [Tok.tt, Tok.ff, Tok.neg, Tok.conj, Tok.disj]; omega
    obtain ⟨T', hrun⟩ : ∃ T', Runs (LenOK B) (decStepP tk qn mt buf fl) L L1 T' := by
      unfold decStepP
      exact ⟨_, Runs.iteF hL n4 (Runs.iteF hL n5 (Runs.iteF hL n6 (Runs.iteF hL hpred hr1)))⟩
    refine ⟨_, L1, hrun, ?_, ?_, ?_, ?_, ?_, fun x hx1 hx2 hx3 hx4 hx5 => h1x x hx1⟩
    · rw [hds, h1t, htk]; simp
    · rw [hds, h1x qn h_tq.symm]; simp
    · rw [hds, h1x mt h_tm.symm]; simp
    · rw [h1x buf h_tb.symm, hbuf]
    · rw [h1x fl h_tf.symm, hfl]


theorem decode_run {tk qn mt buf fl : Fin k} (hd : [tk, qn, mt, buf, fl].Nodup) {B : Nat} :
    ∀ (m : Nat) (ts : List Nat), ts.length = m → ∀ (L : Lists k), LenOK B L → L tk = ts.reverse →
      L buf = [] → L fl = [] → (L qn).length + (L mt).length + 2 * ts.length + 3 ≤ B →
      ∃ T L', Runs (LenOK B) (decodeP tk qn mt buf fl) L L' T ∧ L' tk = [] ∧
        L' qn = L qn ++ qnList (dec ts).quants ∧ L' mt = L mt ++ mtList (dec ts).matrix ∧
        L' buf = [] ∧ L' fl = [] ∧
        ∀ x, x ≠ tk → x ≠ qn → x ≠ mt → x ≠ buf → x ≠ fl → L' x = L x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro ts hm L hL htk hbuf hfl hB
    cases ts with
    | nil =>
      have hc : nonEmpty (lastSym (L tk)) = false := by rw [htk]; rfl
      refine ⟨1, L, Runs.loopEnd hL hc, by rw [htk]; rfl, ?_, ?_, hbuf, hfl, fun _ _ _ _ _ _ => rfl⟩
      · simp [dec, decodeToks, qnList]
      · simp [dec, decodeToks, mtList]
    | cons t ts' =>
      have hc : nonEmpty (lastSym (L tk)) = true := by
        rw [htk]; simp [lastSym_snoc_rev, nonEmpty]
      have htk' : L tk = ts'.reverse ++ [t] := by rw [htk]; simp
      simp only [List.length_cons] at hm hB
      obtain ⟨T1, L1, hr1, h1t, h1q, h1m, h1b, h1f, h1x⟩ :=
        decStep_run hd t ts' hL htk' hbuf hfl (by omega)
      have hL1 := hr1.q_end
      obtain ⟨hf1, hf2⟩ := decStep_facts t ts'
      obtain ⟨T2, L2, hr2, h2t, h2q, h2m, h2b, h2f, h2x⟩ :=
        ih (decStep t ts').1.length (by omega) (decStep t ts').1 rfl L1 hL1 h1t h1b h1f
          (by rw [h1q, h1m]; simp only [List.length_append]; omega)
      obtain ⟨hq, hm'⟩ := dec_cons t ts'
      refine ⟨_, L2, Runs.loopStep hL hc hr1 hr2, h2t, ?_, ?_, h2b, h2f,
        fun x hx1 hx2 hx3 hx4 hx5 => by rw [h2x x hx1 hx2 hx3 hx4 hx5, h1x x hx1 hx2 hx3 hx4 hx5]⟩
      · rw [h2q, h1q, hq, List.append_assoc]
      · rw [h2m, h1m, hm', List.append_assoc]

theorem decodeP_spec {tk qn mt buf fl : Fin k} (hd : [tk, qn, mt, buf, fl].Nodup) {B : Nat} (ts : List Nat)
    {L : Lists k} (htk : L tk = ts.reverse) (hqn : L qn = []) (hmt : L mt = []) (hbuf : L buf = [])
    (hfl : L fl = []) (hB : LenOK B L) (hBt : 2 * ts.length + 3 ≤ B) :
    ∃ T, Runs (LenOK B) (decodeP tk qn mt buf fl) L
      (((L.set tk []).set qn (qnList (decodeToks (ts.length + 1) ts).quants)).set mt
        (mtList (decodeToks (ts.length + 1) ts).matrix)) T := by
  obtain ⟨h_tq, h_tm, h_tb, h_tf, h_qm, h_qb, h_qf, h_mb, h_mf, h_bf⟩ := nodup5 hd
  obtain ⟨T, L', hr, h1, h2, h3, h4, h5, h6⟩ :=
    decode_run hd ts.length ts rfl L hB htk hbuf hfl (by rw [hqn, hmt]; simpa using hBt)
  refine ⟨T, ?_⟩
  have : L' = ((L.set tk []).set qn (qnList (decodeToks (ts.length + 1) ts).quants)).set mt
        (mtList (decodeToks (ts.length + 1) ts).matrix) := by
    funext x
    by_cases hx : x = mt
    · subst hx; rw [Lists.set_same]; rw [h3, hmt]; simp [dec]
    · by_cases hx' : x = qn
      · subst hx'; rw [Lists.set_ne _ _ hx, Lists.set_same]; rw [h2, hqn]; simp [dec]
      · by_cases hx'' : x = tk
        · subst hx''; rw [Lists.set_ne _ _ hx, Lists.set_ne _ _ hx', Lists.set_same]; exact h1
        · rw [Lists.set_ne _ _ hx, Lists.set_ne _ _ hx', Lists.set_ne _ _ hx'']
          by_cases hb : x = buf
          · subst hb; rw [h4, hbuf]
          · by_cases hf : x = fl
            · subst hf; rw [h5, hfl]
            · exact h6 x hx'' hx' hx hb hf
  rw [← this]; exact hr

end Complexity
