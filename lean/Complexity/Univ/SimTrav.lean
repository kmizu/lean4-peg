import Complexity.Univ.SimKit

/-!
# Walking over the tapes

`travP bd` takes the tapes off `TP` and the heads off `POS` one at a time (tape `0` first), runs the body `bd`
with the tape on `sTT`, its head on `sP` and its length on `sLN`, and puts back what the body leaves on `sTT` and
`sP` (`nruns_travP`). The body may change any stack but the ones the walk uses.
-/

namespace Complexity.Univ

open Complexity

def unpackP : NProg UK :=
  .seq (nmv sW sLEN (by decide)) (.seq (.prim (.dup sLEN sLN (by decide)))
    (.seq (moveN sLEN sW sTT (by decide)) (nmv sPW sP (by decide))))

def packP : NProg UK :=
  .seq (.prim (.pushZ TP)) (.seq (cnt sTT sTT2 TP (by decide))
    (.seq (nmvAll sTT2 TP (by decide)) (nmv sP POS (by decide))))

def travP (bd : NProg UK) : NProg UK :=
  .seq (nmvAll TP sW (by decide)) (.seq (nmvAll POS sPW (by decide))
    (.loop sPW .nonempty (.seq unpackP (.seq bd packP))))

/-- The stacks after `i` tapes. -/
def trF (O : Nat → Lists UK) (ts ts' : List (List Nat)) (ps ps' : List Nat) (i : Nat) : Lists UK :=
  ((((((((((O i).set sTT []).set sP []).set sLN []).set sLEN []).set sTT2 []).set TP (encTapes (ts'.take i))).set
    POS (ps'.take i)).set sW (encTapes (ts.drop i)).reverse).set sPW (ps.drop i).reverse)

/-- The stacks the body starts from. -/
def trIn (O : Nat → Lists UK) (ts : List (List Nat)) (ps : List Nat) (i : Nat) : Lists UK :=
  (((O i).set sTT (ts.getD i [])).set sP [ps.getD i 0]).set sLN [(ts.getD i []).length]

/-- The stacks the body ends with. -/
def trOut (O : Nat → Lists UK) (ts' : List (List Nat)) (ps' : List Nat) (i : Nat) : Lists UK :=
  (((O (i + 1)).set sTT (ts'.getD i [])).set sP [ps'.getD i 0]).set sLN []

/-- The stacks the walk keeps for itself. -/
def TravFree (bd : NProg UK) : Prop :=
  bd.touches TP = false ∧ bd.touches POS = false ∧ bd.touches sW = false ∧ bd.touches sPW = false ∧
    bd.touches sLEN = false ∧ bd.touches sTT2 = false

theorem encTapes_cons (t : List Nat) (ts : List (List Nat)) :
    encTapes (t :: ts) = t.length :: t ++ encTapes ts := by simp [encTapes]

theorem encTapes_snoc (ts : List (List Nat)) (t : List Nat) :
    encTapes (ts ++ [t]) = encTapes ts ++ (t.length :: t) := by simp [encTapes]

/-- One round of the walk. -/
theorem trav_round (bd : NProg UK) (hf : TravFree bd) (O : Nat → Lists UK) (ts ts' : List (List Nat))
    (ps ps' : List Nat) (n CB : Nat) (hts : ts.length = n) (hps : ps.length = n) (hts' : ts'.length = n)
    (hps' : ps'.length = n) (i : Nat) (hi : i < n)
    (hb : NRuns bd (trIn O ts ps i) (trOut O ts' ps' i) CB) :
    NRuns (.seq unpackP (.seq bd packP)) (trF O ts ts' ps ps' i) (trF O ts ts' ps ps' (i + 1))
      (CB + 4 * (ts.getD i []).length + 7 * (ts'.getD i []).length + 12) := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := hf
  -- the names of the round
  generalize ht : ts.getD i [] = t at hb
  generalize hp : ps.getD i 0 = p at hb
  generalize ht' : ts'.getD i [] = t' at hb
  generalize hp' : ps'.getD i 0 = p' at hb
  have hdt : ts.drop i = t :: ts.drop (i + 1) := by rw [← ht]; exact drop_getD _ (by omega)
  have hdp : ps.drop i = p :: ps.drop (i + 1) := by rw [← hp]; exact drop_getD _ (by omega)
  have htt : ts'.take (i + 1) = ts'.take i ++ [t'] := by rw [← ht']; exact take_getD _ (by omega)
  have htp : ps'.take (i + 1) = ps'.take i ++ [p'] := by rw [← hp']; exact take_getD _ (by omega)
  generalize hE : encTapes (ts'.take i) = E
  generalize hR : (encTapes (ts.drop (i + 1))).reverse = R
  generalize hQ : ps'.take i = Q
  generalize hPR : (ps.drop (i + 1)).reverse = PR
  have hFW : trF O ts ts' ps ps' i sW = (R ++ t.reverse) ++ [t.length] := by
    simp only [trF]; rw [Lists.set_ne _ _ (by decide), Lists.set_same, hdt, encTapes_cons, ← hR]; simp
  -- unpack
  obtain ⟨U₁, hU₁, u₁⟩ := NRuns.named (nruns_mv sW sLEN (by decide) (trF O ts ts' ps ps' i) hFW)
  obtain ⟨U₂, hU₂, u₂⟩ := NRuns.named (nruns_dup sLEN sLN (by decide) U₁ (l := []) (v := t.length)
    (by rw [hU₁]; simp only [trF]; lat))
  obtain ⟨U₃, hU₃, u₃⟩ := NRuns.named (nruns_moveN sLEN sW sTT (by decide) (by decide) (by decide) U₂
    (lc := []) (n := t.length) (by rw [hU₂, hU₁]; simp only [trF]; lat) (l := R) (seg := t.reverse)
    (by rw [hU₂, hU₁]; lat) (by simp))
  obtain ⟨U₄, hU₄, u₄⟩ := NRuns.named (nruns_mv sPW sP (by decide) U₃ (l := PR) (v := p)
    (by rw [hU₃, hU₂, hU₁]; simp only [trF]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
      Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
      Lists.set_ne _ _ (by decide), Lists.set_same, hdp, ← hPR]; simp))
  -- the body, with the stacks of the walk around it
  have b₁ := ((((((hb.frame hf1 E).frame hf2 Q).frame hf3 R).frame hf4 PR).frame hf5 []).frame hf6 [])
  have e₁ : U₄ = ((((((trIn O ts ps i).set TP E).set POS Q).set sW R).set sPW PR).set sLEN []).set sTT2 [] := by
    rw [hU₄, hU₃, hU₂, hU₁]; simp only [trF, trIn, ht, hp, List.reverse_reverse, ← hE, ← hQ]; leq
  rw [← e₁] at b₁
  -- pack
  obtain ⟨B, hB, b₂⟩ := NRuns.named b₁
  obtain ⟨K₁, hK₁, k₁⟩ := NRuns.named (nruns_pushZ TP B)
  obtain ⟨K₂, hK₂, k₂⟩ := NRuns.named (nruns_cnt sTT sTT2 TP (by decide) (by decide) (by decide) K₁ (lo := E)
    (b := 0) (by rw [hK₁, hB]; simp only [trOut]; lat))
  have hBt : K₁ sTT = t' := by rw [hK₁, hB]; simp only [trOut, ht']; lat
  have hBt2 : K₁ sTT2 = [] := by rw [hK₁, hB]; lat
  rw [hBt, hBt2, List.nil_append, Nat.zero_add] at hK₂
  obtain ⟨K₃, hK₃, k₃⟩ := NRuns.named (nruns_mvAll sTT2 TP (by decide) K₂)
  obtain ⟨K₄, hK₄, k₄⟩ := NRuns.named (nruns_mv sP POS (by decide) K₃ (l := []) (v := p')
    (by rw [hK₃, hK₂, hK₁, hB]; simp only [trOut, hp']; lat))
  have e₂ : K₄ = trF O ts ts' ps ps' (i + 1) := by
    have hE' : encTapes (ts'.take (i + 1)) = E ++ (t'.length :: t') := by rw [htt, encTapes_snoc, hE]
    have hR' : (encTapes (ts.drop (i + 1))).reverse = R := hR
    rw [hK₄, hK₃, hK₂, hK₁, hB]
    simp only [trF, trOut, hE', hR', htp, hQ, hPR, List.reverse_reverse, List.append_assoc, List.cons_append,
      List.nil_append]
    leq
  rw [e₂] at k₄
  refine (u₁.seq (u₂.seq (u₃.seq u₄))).seq (b₂.seq (k₁.seq (k₂.seq (k₃.seq k₄)))) |>.mono ?_
  have h₂ : K₂ sTT2 = t'.reverse := by rw [hK₂]; lat
  rw [hBt, h₂, List.length_reverse]
  omega

/-- **The walk over the tapes.** -/
theorem nruns_travP (bd : NProg UK) (hf : TravFree bd) (O : Nat → Lists UK) (ts ts' : List (List Nat))
    (ps ps' : List Nat) (n CB M : Nat) (hts : ts.length = n) (hps : ps.length = n) (hts' : ts'.length = n)
    (hps' : ps'.length = n) (hb : ∀ i, i < n → NRuns bd (trIn O ts ps i) (trOut O ts' ps' i) CB)
    (hM : ∀ i, i < n → (ts.getD i []).length ≤ M ∧ (ts'.getD i []).length ≤ M) (S : Lists UK) (hO : O 0 = S)
    (hTP : S TP = encTapes ts) (hPOS : S POS = ps) (h₁ : S sW = []) (h₂ : S sPW = []) (h₃ : S sTT = [])
    (h₄ : S sP = []) (h₅ : S sLN = []) (h₆ : S sLEN = []) (h₇ : S sTT2 = []) :
    NRuns (travP bd) S (trF O ts ts' ps ps' n) (3 * (encTapes ts).length + 3 * n + 3 + n * (CB + 11 * M + 13)) := by
  have x₁ := nruns_mvAll TP sW (by decide) S
  have x₂ := nruns_mvAll POS sPW (by decide) ((S.set sW (S sW ++ (S TP).reverse)).set TP [])
  have e : ((((S.set sW (S sW ++ (S TP).reverse)).set TP [])).set sPW
      (((S.set sW (S sW ++ (S TP).reverse)).set TP []) sPW ++
        (((S.set sW (S sW ++ (S TP).reverse)).set TP []) POS).reverse)).set POS [] = trF O ts ts' ps ps' 0 := by
    simp only [trF, hO, List.take_zero, List.drop_zero, hTP, h₁, List.nil_append]
    have : encTapes [] = [] := rfl
    rw [this]
    leq
  rw [e] at x₂
  have hl := nruns_family_const (i := sPW) (c := .nonempty) (p := .seq unpackP (.seq bd packP))
    (trF O ts ts' ps ps') n (CB + 11 * M + 12)
    (fun m hm => by
      simp only [trF, Lists.set_same]
      exact eval_nonempty_ne (by simp; omega))
    (by simp only [trF, Lists.set_same]; rw [List.drop_eq_nil_of_le (by omega)]; rfl)
    (fun m hm => by
      have := trav_round bd hf O ts ts' ps ps' n CB hts hps hts' hps' m hm (hb m hm)
      have hm' := hM m hm
      exact this.mono (by omega))
  have hp : ((S.set sW (S sW ++ (S TP).reverse)).set TP []) POS = ps := by lat
  refine (x₁.seq (x₂.seq hl)).mono ?_
  rw [hp, hTP, hps, show CB + 11 * M + 12 + 1 = CB + 11 * M + 13 by omega]
  omega

end Complexity.Univ
