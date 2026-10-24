import MacroPeg.CBV.RegularCaptureProduct

/-! Stable-table semantics of the generated capture filter. The table is an
actual physical evaluation table, rather than an assumed parsing oracle. -/
namespace Shallot.MacroPeg.CBV.RegularCaptureProduct
open ClockFreezing (Table)

/-- Every defined finite approximation agrees with a physical fixed point,
even if the approximation is taken after the chosen stabilization round. -/
theorem defined_at_fixed {g : MGrammar} {x : List Char} {s : Strategy} {m : Nat}
    (hf : AgreeV g x (tblV g x s m) (tblV g x s (m+1)))
    {i : Nat} {e : MExp} (hi : ruleAtM g.rules i=some ⟨0,e⟩)
    {k p : Nat} (hp : p≤x.length) {v : Option Nat}
    (hv : valAt (tblV g x s k i []) p=some v) :
    valAt (tblV g x s m i []) p=some v := by
  by_cases hk : k≤m
  · have hh := tblV_le g x s hk i [] p
    rcases hh with hh | hh
    · rw [hv] at hh; contradiction
    · rw [←hh,hv]
  · have hh := agreeV_from hf (k-m) i ⟨0,e⟩ [] hi (by simp [words]) p hp
    have he : m+(k-m)=k := by omega
    rw [he,hv] at hh
    exact hh

/-- At a physical fixed point, installed zero-arity rows obey their actual
PEG body equations, including undefined results. -/
theorem row_at_fixed {g : MGrammar} {x : List Char} {s : Strategy} {m : Nat}
    (hf : AgreeV g x (tblV g x s m) (tblV g x s (m+1)))
    {i : Nat} {e : MExp} (hi : ruleAtM g.rules i=some ⟨0,e⟩)
    {p : Nat} (hp : p≤x.length) :
    valAt (tblV g x s m i []) p=evV g x s (tblV g x s m) [] e p := by
  rw [hf i ⟨0,e⟩ [] hi (by simp [words]) p hp]
  exact valAt_tblV_succ hi [] hp

/-- The original query guard gives exact failure/undefined preservation
at stabilization, without a recursive correctness assumption. -/
theorem filter_at_fixed (nodes : List Node) (D : Machine) (hD : 0<D.width)
    (x : List Char) (s : Strategy) (m : Nat)
    (hf : AgreeV (grammar nodes D) x (tblV (grammar nodes D) x s m)
      (tblV (grammar nodes D) x s (m+1)))
    (i q r p : Nat) (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width)
    (hp : p≤x.length) :
    valAt (tblV (grammar nodes D) x s m (key nodes D i q r) []) p =
      match valAt (tblV (grammar nodes D) x s m i []) p with
      | some (some _) => evV (grammar nodes D) x s (tblV (grammar nodes D) x s m) []
          (core nodes D i nodes[i] q r) p
      | other => other := by
  rw [row_at_fixed hf (filter_rule nodes D hD i q r hi hq hr) hp]
  exact filter_body_eval nodes D x s _ i nodes[i] (List.getElem?_eq_getElem hi) q r p []

/-- Soundness of the physical Seq table supplies the consumed prefix, with
no restriction on recursive cycles or successful capture length. -/
theorem physical_success_prefix (nodes : List Node) (D : Machine) (x : List Char)
    (k : Nat) (e : MExp) (he : e.FirstOrder) (p j : Nat) (hp : p≤x.length)
    (hv : evV (grammar nodes D) x .callByValueSeq
      (tblV (grammar nodes D) x .callByValueSeq k) [] e p=some (some j)) :
    j≤x.length ∧ sfx x p=pre x p j++sfx x j := by
  obtain ⟨o,hd,ho⟩ := evV_sound (by decide)
    (tblV_sound (grammar_firstOrder nodes D) (by decide) k) e he p hp _ hv
  obtain ⟨t,rest,rfl,hj⟩ := obsR_ok ho
  have hs := mderives_suffix hd _ _ rfl
  have hr := rest_eq_sfx' hd
  rw [hj] at hr
  have hlen : j≤x.length := by
    obtain ⟨w,hw⟩ := hs
    have hl := congrArg List.length hw
    rw [List.length_append,length_sfx x hp,hj] at hl
    omega
  refine ⟨hlen,?_⟩
  rw [hr]
  simpa [hj] using pre_split hp hs

/-- Literal product rows satisfy the complete result specification at any
physical fixed point, for every input and evaluation strategy. -/
theorem literal_at_fixed (nodes : List Node) (D : Machine) (hD : 0<D.width)
    (x : List Char) (s : Strategy) (m : Nat)
    (hf : AgreeV (grammar nodes D) x (tblV (grammar nodes D) x s m)
      (tblV (grammar nodes D) x s (m+1)))
    (i q r p : Nat) (w : List Char) (hi : nodes[i]?=some (.lit w))
    (hq : q<D.width) (hr : r<D.width) (hp : p≤x.length) :
    valAt (tblV (grammar nodes D) x s m (key nodes D i q r) []) p =
      filtered D x q r p (valAt (tblV (grammar nodes D) x s m i []) p) := by
  have hi' : i<nodes.length := (List.getElem?_eq_some_iff.mp hi).1
  have hrow := row_at_fixed hf (original_rule nodes D i (.lit w) hi) hp
  have hprod := filter_rule nodes D hD i q r hi' hq hr
  rw [(List.getElem?_eq_some_iff.mp hi).2] at hprod
  rw [row_at_fixed hf hprod hp,hrow]
  exact literal_correct nodes D x s _ i q r p w hi hp hrow

/-- A successful pair of parses selects exactly its true intermediate state.
The second parse cannot cause an alternative first capture to be chosen. -/
theorem select_success (nodes : List Node) (D : Machine) (hD : D.Valid)
    (x : List Char) (s : Strategy) (T : Table) (a b q r p j k : Nat)
    (hq : q<D.width) (hp : p≤x.length) (hk : k≤x.length)
    (ha : sfx x p=pre x p j++sfx x j) (hb : sfx x j=pre x j k++sfx x k)
    (hA : ∀ t, t<D.width → evV (grammar nodes D) x s T [] (call nodes D a q t) p =
      filtered D x q t p (some (some j)))
    (hB : evV (grammar nodes D) x s T []
      (call nodes D b (run D q (pre x p j)) r) j =
        filtered D x (run D q (pre x p j)) r j (some (some k))) :
    evV (grammar nodes D) x s T [] (select nodes D a b q r) p =
      filtered D x q r p (some (some k)) := by
  have ht := run_bound hD q hq (pre x p j)
  have hc := SequenceArguments.pre_concat hp hk ha hb
  unfold select
  rw [choice_eval_unique (chosen := run D q (pre x p j))
    (v := filtered D x q r p (some (some k)))]
  · simp only [List.mem_range,ht,ite_true]
  · intro t hmem
    have hat := hA t (List.mem_range.mp hmem)
    by_cases he : t=run D q (pre x p j)
    · subst t
      simp only [filtered,ite_true] at hat
      rw [evV_seq_ok hat,hB,if_pos rfl]
      simp only [filtered,hc,run_append]
    · have he' : run D q (pre x p j)≠t := Ne.symm he
      simp only [filtered,if_neg he'] at hat
      rw [evV_seq_fail hat,if_neg he]

theorem row_success_prefix (nodes : List Node) (D : Machine) (x : List Char)
    (k i p j : Nat) (hi : i<nodes.length) (hp : p≤x.length)
    (hv : valAt (tblV (grammar nodes D) x .callByValueSeq k i []) p=some (some j)) :
    j≤x.length ∧ sfx x p=pre x p j++sfx x j := by
  apply physical_success_prefix nodes D x k (.call i []) True.intro p j hp
  rw [original_call_eval nodes D x .callByValueSeq _ [] i nodes[i]
    (List.getElem?_eq_getElem hi) p]
  exact hv

/-- Finite successful source computations determine the product at a real
fixed point. Induction on source rounds handles recursion; decreasing input
positions handle greedy repetition within a single source round. -/
theorem finite_success (nodes : List Node) (hNodes : Valid nodes)
    (D : Machine) (hD : D.Valid) (x : List Char) (m : Nat)
    (hf : AgreeV (grammar nodes D) x (tblV (grammar nodes D) x .callByValueSeq m)
      (tblV (grammar nodes D) x .callByValueSeq (m+1))) :
    ∀ k i p j, (hi : i<nodes.length) → p≤x.length →
      valAt (tblV (grammar nodes D) x .callByValueSeq k i []) p=some (some j) →
      ∀ q r, q<D.width → r<D.width →
        valAt (tblV (grammar nodes D) x .callByValueSeq m (key nodes D i q r) []) p =
          filtered D x q r p (some (some j)) := by
  intro k
  induction k with
  | zero => intro i p j hi hp hv; simp [tblV,valAt] at hv
  | succ k ih =>
    intro i p
    induction p using Nat.strongRecOn generalizing i with
    | ind p ihp =>
      intro j hi hp hv q r hq hr
      have hn : nodes[i]?=some nodes[i] := List.getElem?_eq_getElem hi
      have hfixed := defined_at_fixed hf (original_rule nodes D i nodes[i] hn) hp hv
      have hsrc := hv
      rw [valAt_tblV_succ (original_rule nodes D i nodes[i] hn) [] hp] at hsrc
      have hvalid := hNodes nodes[i] (List.getElem_mem hi)
      cases he : nodes[i] with
      | lit w =>
        rw [literal_at_fixed nodes D hD.1 x .callByValueSeq m hf i q r p w
          (by simpa [he] using hn) hq hr hp,hfixed]
      | seq a b =>
        rw [filter_at_fixed nodes D hD.1 x .callByValueSeq m hf i q r p hi hq hr hp,hfixed]
        simp only [he,core]
        simp only [he,body] at hsrc
        change (match evV (grammar nodes D) x .callByValueSeq
          (tblV (grammar nodes D) x .callByValueSeq k) [] (.call a []) p with
          | some (some z) => evV (grammar nodes D) x .callByValueSeq
              (tblV (grammar nodes D) x .callByValueSeq k) [] (.call b []) z
          | other => other)=some (some j) at hsrc
        simp only [he] at hvalid
        rw [original_call_eval nodes D x .callByValueSeq _ [] a nodes[a]
          (List.getElem?_eq_getElem hvalid.1) p] at hsrc
        cases ha : valAt (tblV (grammar nodes D) x .callByValueSeq k a []) p with
        | none => simp [ha] at hsrc
        | some result => cases result with
          | none => simp [ha] at hsrc
          | some z =>
            rw [ha] at hsrc
            dsimp only [] at hsrc
            have hz := row_success_prefix nodes D x k a p z hvalid.1 hp ha
            rw [original_call_eval nodes D x .callByValueSeq _ [] b nodes[b]
              (List.getElem?_eq_getElem hvalid.2) z] at hsrc
            have hj := row_success_prefix nodes D x k b z j hvalid.2 hz.1 hsrc
            apply select_success nodes D hD x .callByValueSeq _ a b q r p z j hq hp hj.1 hz.2 hj.2
            · intro t ht
              rw [product_call_eval nodes D hD.1 x .callByValueSeq _ [] a q t hvalid.1 hq ht p]
              exact ih a p z hvalid.1 hp ha q t hq ht
            · rw [product_call_eval nodes D hD.1 x .callByValueSeq _ [] b
                (run D q (pre x p z)) r hvalid.2 (run_bound hD q hq _) hr z]
              exact ih b z j hvalid.2 hz.1 hsrc _ r (run_bound hD q hq _) hr
      | alt a b =>
        simp only [he] at hvalid
        simp only [he,body] at hsrc
        change (match evV (grammar nodes D) x .callByValueSeq
          (tblV (grammar nodes D) x .callByValueSeq k) [] (.call a []) p with
          | some none => evV (grammar nodes D) x .callByValueSeq
              (tblV (grammar nodes D) x .callByValueSeq k) [] (.call b []) p
          | other => other)=some (some j) at hsrc
        rw [original_call_eval nodes D x .callByValueSeq _ [] a nodes[a]
          (List.getElem?_eq_getElem hvalid.1) p] at hsrc
        rw [filter_at_fixed nodes D hD.1 x .callByValueSeq m hf i q r p hi hq hr hp,hfixed]
        simp only [he,core]
        rw [ChoiceArguments.branch_eval,original_call_eval nodes D x .callByValueSeq _ [] a nodes[a]
          (List.getElem?_eq_getElem hvalid.1) p]
        cases ha : valAt (tblV (grammar nodes D) x .callByValueSeq k a []) p with
        | none => simp [ha] at hsrc
        | some result => cases result with
          | none =>
            have hfa := defined_at_fixed hf (original_rule nodes D a nodes[a]
              (List.getElem?_eq_getElem hvalid.1)) hp ha
            rw [hfa]
            dsimp only []
            rw [ha] at hsrc
            dsimp only [] at hsrc
            rw [original_call_eval nodes D x .callByValueSeq _ [] b nodes[b]
              (List.getElem?_eq_getElem hvalid.2) p] at hsrc
            rw [product_call_eval nodes D hD.1 x .callByValueSeq _ [] b q r hvalid.2 hq hr p]
            exact ih b p j hvalid.2 hp hsrc q r hq hr
          | some z =>
            have hfa := defined_at_fixed hf (original_rule nodes D a nodes[a]
              (List.getElem?_eq_getElem hvalid.1)) hp ha
            rw [hfa]
            dsimp only []
            have hz : z=j := by simpa [ha] using hsrc
            subst z
            rw [product_call_eval nodes D hD.1 x .callByValueSeq _ [] a q r hvalid.1 hq hr p]
            exact ih a p j hvalid.1 hp ha q r hq hr
      | star a =>
        simp only [he] at hvalid
        let f : Nat → Res := fun z => valAt (tblV (grammar nodes D) x .callByValueSeq k a []) z
        have hbody (z : Nat) : evV (grammar nodes D) x .callByValueSeq
            (tblV (grammar nodes D) x .callByValueSeq k) [] (.star (.call a [])) z=evStar f z := by
          change evStar _ z=evStar _ z
          congr 1
          funext u
          exact original_call_eval nodes D x .callByValueSeq _ [] a nodes[a]
            (List.getElem?_eq_getElem hvalid) u
        simp only [he,body] at hsrc
        rw [hbody] at hsrc
        rw [filter_at_fixed nodes D hD.1 x .callByValueSeq m hf i q r p hi hq hr hp,hfixed]
        simp only [he,core]
        rw [ChoiceArguments.branch_eval,original_call_eval nodes D x .callByValueSeq _ [] a nodes[a]
          (List.getElem?_eq_getElem hvalid) p]
        cases ha : f p with
        | none => rw [evStar_none ha] at hsrc; contradiction
        | some result => cases result with
          | none =>
            have hfa := defined_at_fixed hf (original_rule nodes D a nodes[a]
              (List.getElem?_eq_getElem hvalid)) hp ha
            rw [hfa]
            dsimp only []
            rw [evStar_fail ha] at hsrc
            have hj : p=j := Option.some.inj (Option.some.inj hsrc)
            subst j
            simp only [filtered,pre,Nat.sub_self,List.take_zero,run,List.foldl_nil]
            split <;> rfl
          | some z =>
            by_cases hz : z<p
            · rw [evStar_ok ha hz] at hsrc
              have hzpre := row_success_prefix nodes D x k a p z hvalid hp ha
              have hvz : valAt (tblV (grammar nodes D) x .callByValueSeq (k+1) i []) z=
                  some (some j) := by
                rw [valAt_tblV_succ (original_rule nodes D i nodes[i] hn) [] hzpre.1]
                simpa only [he,body,hbody] using hsrc
              have hjpre := row_success_prefix nodes D x (k+1) i z j hi hzpre.1 hvz
              have hfa := defined_at_fixed hf (original_rule nodes D a nodes[a]
                (List.getElem?_eq_getElem hvalid)) hp ha
              rw [hfa]
              dsimp only []
              apply select_success nodes D hD x .callByValueSeq _ a i q r p z j
                hq hp hjpre.1 hzpre.2 hjpre.2
              · intro t ht
                rw [product_call_eval nodes D hD.1 x .callByValueSeq _ [] a q t hvalid hq ht p]
                exact ih a p z hvalid hp ha q t hq ht
              · rw [product_call_eval nodes D hD.1 x .callByValueSeq _ [] i
                  (run D q (pre x p z)) r hi (run_bound hD q hq _) hr z]
                exact ihp z hz i j hi hzpre.1 hvz _ r (run_bound hD q hq _) hr
            · rw [evStar_stuck ha hz] at hsrc
              contradiction
      | notP a =>
        simp only [he] at hvalid
        simp only [he,body] at hsrc
        change (match evV (grammar nodes D) x .callByValueSeq
          (tblV (grammar nodes D) x .callByValueSeq k) [] (.call a []) p with
          | some (some _) => some none | some none => some (some p) | none => none)=
            some (some j) at hsrc
        rw [original_call_eval nodes D x .callByValueSeq _ [] a nodes[a]
          (List.getElem?_eq_getElem hvalid) p] at hsrc
        cases ha : valAt (tblV (grammar nodes D) x .callByValueSeq k a []) p with
        | none => simp [ha] at hsrc
        | some result => cases result with
          | some z => simp [ha] at hsrc
          | none =>
            have hj : p=j := by simpa [ha] using hsrc
            subst j
            rw [filter_at_fixed nodes D hD.1 x .callByValueSeq m hf i q r p hi hq hr hp,hfixed]
            simp only [he,core,filtered,pre,Nat.sub_self,List.take_zero,run,List.foldl_nil]
            split <;> rfl

/-- Full result equality for every valid recursive graph and every input.
Undefined source computations remain undefined; successful captures with the
wrong automaton state are finite failures. -/
theorem product_at_fixed (nodes : List Node) (hNodes : Valid nodes)
    (D : Machine) (hD : D.Valid) (x : List Char) (m : Nat)
    (hf : AgreeV (grammar nodes D) x (tblV (grammar nodes D) x .callByValueSeq m)
      (tblV (grammar nodes D) x .callByValueSeq (m+1)))
    (i q r p : Nat) (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width)
    (hp : p≤x.length) :
    valAt (tblV (grammar nodes D) x .callByValueSeq m (key nodes D i q r) []) p =
      filtered D x q r p (valAt (tblV (grammar nodes D) x .callByValueSeq m i []) p) := by
  cases hv : valAt (tblV (grammar nodes D) x .callByValueSeq m i []) p with
  | none => rw [filter_at_fixed nodes D hD.1 x .callByValueSeq m hf i q r p hi hq hr hp,hv]; rfl
  | some result => cases result with
    | none => rw [filter_at_fixed nodes D hD.1 x .callByValueSeq m hf i q r p hi hq hr hp,hv]; rfl
    | some j => exact finite_success nodes hNodes D hD x m hf m i p j hi hp hv q r hq hr

/-- The standard finite evaluation bound is itself a physical fixed point. -/
theorem bound_fixed (g : MGrammar) (x : List Char) (s : Strategy) :
    AgreeV g x (tblV g x s (iterBoundV g x)) (tblV g x s (iterBoundV g x+1)) := by
  obtain ⟨m,hm,hf⟩ := tblV_fix_exists g x s
  have h0 := agreeV_from hf (iterBoundV g x-m)
  have h1 := agreeV_from hf (iterBoundV g x+1-m)
  have he0 : m+(iterBoundV g x-m)=iterBoundV g x := by omega
  have he1 : m+(iterBoundV g x+1-m)=iterBoundV g x+1 := by omega
  rw [he0] at h0
  rw [he1] at h1
  exact h0.symm.trans h1

/-- Unconditional correctness at the evaluator's canonical round, on the
same original input strings. No semantic advice or fixed-point premise is
supplied by the user of the generated grammar. -/
theorem product_correct (nodes : List Node) (hNodes : Valid nodes)
    (D : Machine) (hD : D.Valid) (x : List Char) (i q r p : Nat)
    (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) (hp : p≤x.length) :
    let g := grammar nodes D
    let T := tblV g x .callByValueSeq (iterBoundV g x)
    evV g x .callByValueSeq T [] (call nodes D i q r) p =
      filtered D x q r p (evV g x .callByValueSeq T [] (.call i []) p) := by
  dsimp only []
  rw [product_call_eval nodes D hD.1 x .callByValueSeq _ [] i q r hi hq hr p,
    original_call_eval nodes D x .callByValueSeq _ [] i nodes[i] (List.getElem?_eq_getElem hi) p]
  exact product_at_fixed nodes hNodes D hD x _ (bound_fixed _ _ _) i q r p hi hq hr hp

/-- Adding the filter rules does not change the canonical original parser.
Independent original components also agree between Par and Seq. -/
theorem canonical_helpers_eq {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g h : MGrammar} (hg : RecursiveParserStability.Installed bodies g)
    (hh : RecursiveParserStability.Installed bodies h) (x : List Char) (s t : Strategy)
    (i p : Nat) (hi : i<bodies.length) (hp : p≤x.length) :
    valAt (tblV g x s (iterBoundV g x) i []) p =
      valAt (tblV h x t (iterBoundV h x) i []) p := by
  have hn := List.getElem?_eq_getElem hi
  have hleft := agreeV_from (bound_fixed g x s) (iterBoundV h x)
    i ⟨0,bodies[i]⟩ [] (hg i bodies[i] hn) (by simp [words]) p hp
  have hright := agreeV_from (bound_fixed h x t) (iterBoundV g x)
    i ⟨0,bodies[i]⟩ [] (hh i bodies[i] hn) (by simp [words]) p hp
  rw [hleft,hright]
  have he := RecursiveParserStability.helper_rows_eq hb hg hh x s t
    (iterBoundV g x+iterBoundV h x) i hi [] []
  simpa only [Nat.add_comm] using congrArg (fun row => valAt row p) he

/-- The generated Seq filter recognizes exactly the automaton-selected
captures of the original standalone recursive Par grammar, on unchanged
input strings and with the same successful endpoint. -/
theorem product_source_correct (nodes : List Node) (hNodes : Valid nodes)
    (D : Machine) (hD : D.Valid) (x : List Char) (i q r p : Nat)
    (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) (hp : p≤x.length) :
    let g := grammar nodes D
    let h := RecursiveParserStability.grammar (nodes.map body)
    evV g x .callByValueSeq (tblV g x .callByValueSeq (iterBoundV g x)) []
        (call nodes D i q r) p =
      filtered D x q r p
        (evV h x .callByValuePar (tblV h x .callByValuePar (iterBoundV h x)) [] (.call i []) p) := by
  dsimp only []
  rw [product_correct nodes hNodes D hD x i q r p hi hq hr hp]
  rw [original_call_eval nodes D x .callByValueSeq _ [] i nodes[i] (List.getElem?_eq_getElem hi) p]
  have hn : (nodes.map body)[i]?=some (body nodes[i]) := by
    simp only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]
  have hh := RecursiveParserStability.installed (nodes.map body) i (body nodes[i]) hn
  have hcall : evV (RecursiveParserStability.grammar (nodes.map body)) x .callByValuePar
      (tblV (RecursiveParserStability.grammar (nodes.map body)) x .callByValuePar
        (iterBoundV (RecursiveParserStability.grammar (nodes.map body)) x)) [] (.call i []) p =
      valAt (tblV (RecursiveParserStability.grammar (nodes.map body)) x .callByValuePar
        (iterBoundV (RecursiveParserStability.grammar (nodes.map body)) x) i []) p := by
    simp [evV,hh,evParArgs]
  rw [hcall]
  congr 1
  exact canonical_helpers_eq (helper_valid hNodes) (original_installed nodes D)
    (RecursiveParserStability.installed _) x .callByValueSeq .callByValuePar i p
    (by simpa using hi) hp

/-- Successful finite observations of the real generated grammar, with no
bound on the input or recursion depth. The endpoint is preserved exactly. -/
theorem product_observations (nodes : List Node) (hNodes : Valid nodes)
    (D : Machine) (hD : D.Valid) (x rest : List Char) (i q r : Nat)
    (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) :
    let g := grammar nodes D
    let h := RecursiveParserStability.grammar (nodes.map body)
    SObs g .callByValueSeq (call nodes D i q r) x (some rest) ↔
      ∃ j, evV h x .callByValuePar (tblV h x .callByValuePar (iterBoundV h x)) []
          (.call i []) x.length=some (some j) ∧
        run D q (pre x x.length j)=r ∧ sfx x j=rest := by
  dsimp only []
  rw [←decideObsV_iff (e := call nodes D i q r) (grammar_firstOrder nodes D) (by decide) True.intro]
  unfold decideObsV
  rw [product_source_correct nodes hNodes D hD x i q r x.length hi hq hr (by omega)]
  cases hv : evV (RecursiveParserStability.grammar (nodes.map body)) x .callByValuePar
      (tblV _ x .callByValuePar (iterBoundV _ x)) [] (.call i []) x.length with
  | none => simp [filtered]
  | some result => cases result with
    | none => simp [filtered]
    | some j =>
      simp only [filtered]
      by_cases hc : run D q (pre x x.length j)=r <;> simp [hc]

end Shallot.MacroPeg.CBV.RegularCaptureProduct
