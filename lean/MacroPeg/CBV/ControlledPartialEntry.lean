import MacroPeg.CBV.ControlledPartialPreflight
import MacroPeg.CBV.LeadingReplayStar

/-! Full call-entry correspondence for controlled partial captures. Test
and continuation correspondences are parameters for recursive induction. -/
namespace Shallot.MacroPeg.CBV.ControlledPartialEntry
open ControlledPartialCapture (step argument restArgument)
open ControlledPartialPreflight (preflight)
open PartialCodewordCapture (runA look)
open RuntimeShiftFilter (scanner block)
open PartialCodewordExecution (firstPiece)
open ClockFreezing (Table)

def branches (binary unary : Nat) (test : MExp) : MExp :=
  .alt (.seq (look (step test)) (.call binary [runA,restArgument test]))
    (.seq (.notP (step test)) (.call unary [runA]))
def entry (binary unary : Nat) (test : MExp) : MExp :=
  .seq (look (preflight test)) (branches binary unary test)

theorem entry_firstOrder (binary unary : Nat) (test : MExp) (ht : test.FirstOrder) :
    (entry binary unary test).FirstOrder := by
  have hB := ControlledPartialCapture.argument_firstOrder test ht
  have hS : (step test).FirstOrder := hB.1
  have hR : runA.FirstOrder := hB.2
  exact ⟨ControlledPartialPreflight.preflight_firstOrder test ht,
    ⟨hS,hR,⟨True.intro,hB⟩,True.intro⟩,hS,hR,True.intro⟩

private theorem scanner_pure : ParserPrefixFusion.Pure scanner := by
  simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
    MExp.failAlways,ParserPrefixFusion.Pure]

private theorem run_pure : ParserPrefixFusion.Pure runA := scanner_pure.1

/-- Only the actual stopping tests need a cross-context relation. All
scanner steps, greedy stops, and capture endpoints then follow from it. -/
theorem argument_congr (g g' : MGrammar) (x : List Char) (s s' : Strategy)
    (T U : Table) (hT : OkTV x.length T) (E E' : List (List Char))
    (test test' : MExp)
    (ht : ∀ q, q≤x.length → evV g x s T E test q=evV g' x s' U E' test' q)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (argument test) p=evV g' x s' U E' (argument test') p := by
  have hA := ParserPrefixFusion.pure_eval g g' x s s' T U E E' scanner scanner_pure
  have hR := ParserPrefixFusion.pure_eval g g' x s s' T U E E' runA run_pure
  have hseq : ∀ q, q≤x.length → evV g x s T E (.seq scanner test) q=
      evV g' x s' U E' (.seq scanner test') q := by
    intro q hq
    change (match evV g x s T E scanner q with
      | some (some j) => evV g x s T E test j | other => other)=
      (match evV g' x s' U E' scanner q with
      | some (some j) => evV g' x s' U E' test' j | other => other)
    rw [←hA q]
    cases ha : evV g x s T E scanner q with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some j => exact ht j (evV_ok hT _ q hq j ha)
  have hstep : ∀ q, q≤x.length → evV g x s T E (step test) q=
      evV g' x s' U E' (step test') q := by
    intro q hq
    change (match evV g x s T E scanner q with
      | some (some j) => evV g x s T E (look (.seq scanner test)) j | other => other)=
      (match evV g' x s' U E' scanner q with
      | some (some j) => evV g' x s' U E' (look (.seq scanner test')) j | other => other)
    rw [←hA q]
    cases ha : evV g x s T E scanner q with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some j =>
        change evV g x s T E (.andP (.seq scanner test)) j=
          evV g' x s' U E' (.andP (.seq scanner test')) j
        rw [CallLookahead.evV_peek,CallLookahead.evV_peek,
          hseq j (evV_ok hT _ q hq j ha)]
  have hstar := evStar_congr p (fun q hq => hstep q (by omega))
  change (match evStar (fun q => evV g x s T E (step test) q) p with
    | some (some q) => evV g x s T E runA q | other => other)=
    (match evStar (fun q => evV g' x s' U E' (step test') q) p with
    | some (some q) => evV g' x s' U E' runA q | other => other)
  rw [hstar]
  cases evStar (fun q => evV g' x s' U E' (step test') q) p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q => exact hR q

/-- Even partial stopping tests cannot make B_G finitely fail: a star
stops with a position and the final a-run always succeeds. -/
theorem argument_ne_fail (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (argument test) p≠some none := by
  change (match evStar (fun q => evV g x s T E (step test) q) p with
    | some (some q) => evV g x s T E runA q | other => other)≠_
  cases hs : evStar (fun q => evV g x s T E (step test) q) p with
  | none => simp
  | some r => cases r with
    | none => exact False.elim (evStar_ne_fail p hs)
    | some q =>
      have hq := evStar_le p q hs
      change evV g x s T E runA q≠some none
      rw [runA,NestedScannerArguments.scan_eval g x s T E ['a'] q (by omega)]
      simp

private theorem seq_success (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (a b : MExp) (p q : Nat)
    (h : evV g x s T E (.seq a b) p=some (some q)) :
    ∃ j, evV g x s T E a p=some (some j) ∧ evV g x s T E b j=some (some q) := by
  cases ha : evV g x s T E a p with
  | none => rw [evV_seq_none ha] at h; cases h
  | some r => cases r with
    | none => rw [evV_seq_fail ha] at h; cases h
    | some j => rw [evV_seq_ok ha] at h; exact ⟨j,rfl,h⟩

private theorem look_ok (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (a : MExp) (p q : Nat)
    (h : evV g x s T E a p=some (some q)) :
    evV g x s T E (look a) p=some (some p) := by
  change evV g x s T E (.andP a) p=_
  rw [CallLookahead.evV_peek,h]; rfl

private theorem look_position (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (a : MExp) (p q : Nat)
    (h : evV g x s T E (look a) p=some (some q)) : q=p := by
  change evV g x s T E (.andP a) p=_ at h
  rw [CallLookahead.evV_peek] at h
  cases ha : evV g x s T E a p with
  | none => simp [ha,CallLookahead.peek] at h
  | some r => cases r with
    | none => simp [ha,CallLookahead.peek] at h
    | some j => simpa [ha,CallLookahead.peek] using h.symm

/-- A successful first step supplies both actual Seq captures and the
real rotated replay suffix, without a shape or word-count oracle. -/
theorem positive_state (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p j q z : Nat) (E : List (List Char)) (test : MExp) (ht : test.FirstOrder)
    (hp : p≤x.length)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument test) p=some (some j))
    (hh : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p j] (.seq scanner (.param 0)) p=some (some q))
    (hstep : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (step test) p=some (some z)) :
    ∃ u v, evSeqArgs g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
        [runA,restArgument test] p=some (some ([u,v],j)) ∧
      u++v=pre x p j ∧ sfx x j='#'::(u++sfx x q) := by
  let T := tblV g x .callByValueSeq (m+1)
  obtain ⟨a,hA,hguard⟩ := seq_success g x .callByValueSeq T E _ _ p z hstep
  have hz := look_position g x .callByValueSeq T E _ a z hguard
  subst a
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  have hz := evV_ok hOk _ p hp z hA
  obtain ⟨k,hinput⟩ := PartialCodewordClassification.scanner_shape g x .callByValueSeq T E p z hp hA
  have hguard' : evV g x .callByValueSeq T E (look (.seq scanner test))
      (sfx x z).length=some (some (sfx x z).length) := by
    simpa only [length_sfx x hz] using hguard
  obtain ⟨hargs,hjoin⟩ := ControlledPartialCapture.split_arguments g x .callByValueSeq T E
    test p k j (sfx x z) hp hinput hguard' ha
  obtain ⟨l,n,hcap,hshape,hend⟩ := ControlledPartialCapture.source_prefix_shape g x
    .callByValueSeq (by decide) T (tblV_sound hg (by decide) (m+1)) E test ht p j q hp ha hh
  have hkl : k=l := (RuntimeShiftFilter.block_prefix k l _).mp
    ⟨sfx x z,by simpa [CodewordReplay.power,List.replicate_succ,List.append_assoc]
      using hinput.symm.trans hshape⟩
  subst l
  exact ⟨firstPiece k,pre x ('#'::sfx x z).length j,hargs,hjoin,hend⟩

private theorem split_body (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u v : List Char) (j q : Nat) (hq : q≤x.length)
    (hs : sfx x j='#'::(u++sfx x q)) (b : MExp) (hb : b.FirstOrder) :
    evV g x s T [u,v] (.seq (.lit ['#'])
      (.seq (.param 0) (CodewordControlFilter.wholeView b))) j=
      evV g x s T [u++v] b q := by
  have hhash := LastCodewordCandidate.literal_at g x s T [u,v] ['#'] (u++sfx x q) j hs
  have hrest : sfx x (u++sfx x q).length=u++sfx x q :=
    sfx_suffix (suffix_trans (sfx_is_suffix x j) ⟨['#'],hs⟩).choose_spec
  have hparam : evV g x s T [u,v] (.param 0) (u++sfx x q).length=some (some q) := by
    have hh := LastCodewordCandidate.literal_at g x s T [] u (sfx x q) _ hrest
    simpa only [evV,List.getElem?_cons_zero,length_sfx x hq] using hh
  rw [evV_seq_ok hhash,evV_seq_ok hparam,
    CodewordControlFilter.wholeView_eval g x s T u v b hb]

theorem positive_branch (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m binary unary p j q z : Nat) (E : List (List Char)) (test b : MExp)
    (ht : test.FirstOrder) (hb : b.FirstOrder) (hp : p≤x.length)
    (rule : ruleAtM g.rules binary=some ⟨2,.seq (.lit ['#'])
      (.seq (.param 0) (CodewordControlFilter.wholeView b))⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument test) p=some (some j))
    (hh : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p j] (.seq scanner (.param 0)) p=some (some q))
    (hstep : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (step test) p=some (some z)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (branches binary unary test) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) [pre x p j] b q := by
  let T := tblV g x .callByValueSeq (m+1)
  obtain ⟨u,v,hargs,hjoin,hend⟩ := positive_state g hg x m p j q z E test ht hp ha hh hstep
  have hj := evV_ok (tblV_ok g x .callByValueSeq (m+1)) _ p hp j ha
  have hq := evV_ok (tblV_ok g x .callByValueSeq (m+1)) _ p hp q hh
  have hcall : evV g x .callByValueSeq T E (.call binary [runA,restArgument test]) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) [pre x p j] b q := by
    rw [evV_call_seq rule rfl,hargs]
    dsimp only [T]
    rw [valAt_tblV_succ rule _ hj,split_body g x .callByValueSeq _ u v j q hq hend b hb,hjoin]
  have hlook := look_ok g x .callByValueSeq T E _ p z hstep
  have hno : evV g x .callByValueSeq T E
      (.seq (.notP (step test)) (.call unary [runA])) p=some none :=
    evV_seq_fail (evV_not_ok hstep)
  change (match evV g x .callByValueSeq T E
      (.seq (look (step test)) (.call binary [runA,restArgument test])) p with
    | some none => evV g x .callByValueSeq T E
        (.seq (.notP (step test)) (.call unary [runA])) p | other => other)=_
  rw [evV_seq_ok hlook,hno,←hcall]
  cases evV g x .callByValueSeq T E (.call binary [runA,restArgument test]) p with
  | none => rfl
  | some r => cases r <;> rfl

private theorem unary_body (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u : List Char) (j q : Nat) (hq : q≤x.length)
    (hs : sfx x j='#'::(u++sfx x q)) (b : MExp) :
    evV g x s T [u] (.seq (.lit ['#']) (.seq (.param 0) b)) j=
      evV g x s T [u] b q := by
  have hhash := LastCodewordCandidate.literal_at g x s T [u] ['#'] (u++sfx x q) j hs
  have hrest : sfx x (u++sfx x q).length=u++sfx x q :=
    sfx_suffix (suffix_trans (sfx_is_suffix x j) ⟨['#'],hs⟩).choose_spec
  have hparam : evV g x s T [u] (.param 0) (u++sfx x q).length=some (some q) := by
    have hh := LastCodewordCandidate.literal_at g x s T [] u (sfx x q) _ hrest
    simpa only [evV,List.getElem?_cons_zero,length_sfx x hq] using hh
  rw [evV_seq_ok hhash,evV_seq_ok hparam]

/-- A failed first iteration takes the unary branch, retaining the whole
actual final run, including an empty capture. Later failure does not
retry a different capture. -/
theorem zero_branch (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m binary unary p j q : Nat) (E : List (List Char)) (test b : MExp)
    (ht : test.FirstOrder) (hp : p≤x.length)
    (rule : ruleAtM g.rules unary=some ⟨1,.seq (.lit ['#']) (.seq (.param 0) b)⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument test) p=some (some j))
    (hh : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p j] (.seq scanner (.param 0)) p=some (some q))
    (hstep : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (step test) p=some none) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (branches binary unary test) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) [pre x p j] b q := by
  let T := tblV g x .callByValueSeq (m+1)
  have hrun : evV g x .callByValueSeq T E runA p=some (some j) :=
    (ControlledPartialCapture.zero g x .callByValueSeq T E test p hstep).symm.trans ha
  obtain ⟨k,hfirst,_⟩ := PartialCodewordClassification.run_shape g x .callByValueSeq T E p j hp hrun
  obtain ⟨l,n,hcap,_,hend⟩ := ControlledPartialCapture.source_prefix_shape g x
    .callByValueSeq (by decide) T (tblV_sound hg (by decide) (m+1)) E test ht p j q hp ha hh
  obtain ⟨hkl,_⟩ := ControlledPartialPreflight.partial_decode l n [] k
    (by simp) (by simpa using hcap.symm.trans hfirst)
  subst l
  have hj := evV_ok (tblV_ok g x .callByValueSeq (m+1)) _ p hp j ha
  have hq := evV_ok (tblV_ok g x .callByValueSeq (m+1)) _ p hp q hh
  have hcall : evV g x .callByValueSeq T E (.call unary [runA]) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) [pre x p j] b q := by
    rw [evV_call_seq rule rfl]
    simp only [evSeqArgs,hrun]
    dsimp only [T]
    rw [valAt_tblV_succ rule _ hj]
    exact unary_body g x .callByValueSeq _ (pre x p j) j q hq (by rw [hfirst]; exact hend) b
  have hlook : evV g x .callByValueSeq T E (look (step test)) p=some none := by
    change evV g x .callByValueSeq T E (.andP (step test)) p=_
    rw [CallLookahead.evV_peek,hstep]; rfl
  rw [branches,evV_alt_fail (evV_seq_fail hlook),evV_seq_ok (evV_not_fail hstep)]
  exact hcall

/-- Full partial call transfer across different grammars, strategies,
clocks, and caller environments. The stopping-test relation is at the
current caller clock; the callee continuation uses the preceding clock. -/
theorem transfer (g g' : MGrammar) (hg' : g'.FirstOrder) (x : List Char)
    (m m' i binary unary p : Nat) (E E' : List (List Char))
    (test test' b b' : MExp) (ht' : test'.FirstOrder) (hb' : b'.FirstOrder)
    (hp : p≤x.length)
    (sourceRule : ruleAtM g.rules i=some ⟨1,.seq scanner (.seq (.param 0) b)⟩)
    (r0 : ruleAtM g'.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g'.rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩)
    (binaryRule : ruleAtM g'.rules binary=some ⟨2,.seq (.lit ['#'])
      (.seq (.param 0) (CodewordControlFilter.wholeView b'))⟩)
    (unaryRule : ruleAtM g'.rules unary=some ⟨1,.seq (.lit ['#']) (.seq (.param 0) b')⟩)
    (htest : ∀ q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar (m+1)) E test q=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E' test' q)
    (hcont : ∀ w q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar m) [w] b q=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq m') [w] b' q) :
    evV g x .callByValuePar (tblV g x .callByValuePar (m+1)) E
        (.call i [argument test]) p=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
        (entry binary unary test') p := by
  let T := tblV g x .callByValuePar (m+1)
  let U := tblV g' x .callByValueSeq (m'+1)
  have harg := argument_congr g g' x .callByValuePar .callByValueSeq T U
    (tblV_ok g x .callByValuePar (m+1)) E E' test test' htest p hp
  cases ha : evV g x .callByValuePar T E (argument test) p with
  | none =>
    have ha' := harg.symm.trans ha
    have hf := ControlledPartialPreflight.undefined g' x .callByValueSeq U E' test' p ha'
    have hlo : evV g' x .callByValueSeq U E' (look (preflight test')) p=none := by
      change evV g' x .callByValueSeq U E' (.andP (preflight test')) p=_
      rw [CallLookahead.evV_peek,hf]; rfl
    rw [evV_call_par sourceRule rfl (by decide)]
    simp only [evParArgs,show evV g x .callByValuePar
      (tblV g x .callByValuePar (m+1)) E (argument test) p=none from ha]
    rw [entry,evV_seq_none hlo]
  | some r => cases r with
    | none => exact False.elim (argument_ne_fail g x .callByValuePar T E test p hp ha)
    | some j =>
      have ha' := harg.symm.trans ha
      have hsource : evV g x .callByValuePar T E (.call i [argument test]) p=
          evV g x .callByValuePar (tblV g x .callByValuePar m) [pre x p j]
            (.seq scanner (.seq (.param 0) b)) p := by
        rw [evV_call_par sourceRule rfl (by decide)]
        simp only [evParArgs,ha]
        dsimp only [T]
        rw [valAt_tblV_succ sourceRule _ hp]
      rw [hsource,←LeadingReplayStar.sequence_assoc g x .callByValuePar _ _ scanner (.param 0) b p]
      have hprefixeq := LastCodewordGrammar.syntax_eval g g' x .callByValuePar .callByValueSeq
        (tblV g x .callByValuePar m) U (tblV_ok g x .callByValuePar m) [pre x p j]
        (.seq scanner (.param 0)) ⟨LastCodewordGrammar.pure_syntax scanner scanner_pure,True.intro⟩ p hp
      have hfilter := ControlledPartialPreflight.physical_result g' hg' x m' p j E' test' ht' hp r0 r1 ha'
      obtain ⟨r,hr⟩ := PartialCodewordTotality.prefix_total g x .callByValuePar _
        (tblV_ok g x .callByValuePar m) (pre x p j) p hp
      have hr' := hprefixeq.symm.trans hr
      rw [hr'] at hfilter
      cases r with
      | none =>
        have hlo : evV g' x .callByValueSeq U E' (look (preflight test')) p=some none := by
          change evV g' x .callByValueSeq U E' (.andP (preflight test')) p=_
          rw [CallLookahead.evV_peek,hfilter]; rfl
        rw [evV_seq_fail hr,entry,evV_seq_fail hlo]
      | some q =>
        have hq := evV_ok (tblV_ok g x .callByValuePar m) _ p hp q hr
        have hlo := look_ok g' x .callByValueSeq U E' (preflight test') p j hfilter
        rw [evV_seq_ok hr,hcont _ q hq,entry,evV_seq_ok hlo]
        symm
        cases hstep : evV g' x .callByValueSeq U E' (step test') p with
        | none =>
          have hn := ControlledPartialCapture.undefined g' x .callByValueSeq U E' test' p hstep
          rw [ha'] at hn; cases hn
        | some r => cases r with
          | none => exact zero_branch g' hg' x m' binary unary p j q E' test' b' ht' hp unaryRule ha' hr' hstep
          | some z => exact positive_branch g' hg' x m' binary unary p j q z E' test' b' ht' hb' hp binaryRule ha' hr' hstep

/-- Actual helper rows at clock zero supply no comparison result. This
seed holds for arbitrary stopping tests, including recursive ones. -/
theorem preflight_zero (g : MGrammar) (x : List Char) (E : List (List Char))
    (test : MExp) (p : Nat) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq 0) E (preflight test) p=none := by
  let T := tblV g x .callByValueSeq 0
  cases ha : evV g x .callByValueSeq T E (argument test) p with
  | none => exact ControlledPartialPreflight.undefined g x .callByValueSeq T E test p ha
  | some r => cases r with
    | none => exact False.elim (argument_ne_fail g x .callByValueSeq T E test p hp ha)
    | some j =>
      obtain ⟨z,hstar,_⟩ := seq_success g x .callByValueSeq T E _ _ p j ha
      have hlo := look_ok g x .callByValueSeq T E _ p j ha
      rw [preflight,evV_seq_ok hlo]
      let d : CodewordControlFilter.Expr := .seq .token (.test (.seq scanner test))
      let f := AdjacentCodewordControl.filter scanner (.call 0 [scanner]) d
      have hfstar : evV g x .callByValueSeq T E
          (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
            (ControlledPartialPreflight.control test)) p=
          evV g x .callByValueSeq T E (.seq (.star f) (.notP (step test))) p := by
        change evV g x .callByValueSeq T E
          (.seq (look (.star (step test))) (.seq (.star f) (.notP (step test)))) p=_
        rw [evV_seq_ok (look_ok g x .callByValueSeq T E _ p z hstar)]
      cases hstep : evV g x .callByValueSeq T E (step test) p with
      | none =>
        have hn := ControlledPartialCapture.undefined g x .callByValueSeq T E test p hstep
        rw [ha] at hn; cases hn
      | some r => cases r with
        | none =>
          have hf : evV g x .callByValueSeq T E f p=some none :=
            AdjacentCodewordControl.filter_fail g x .callByValueSeq T E scanner (.call 0 [scanner]) d p hstep
          have hfst : evV g x .callByValueSeq T E (.star f) p=some (some p) := evStar_fail hf
          have hfilter : evV g x .callByValueSeq T E
              (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
                (ControlledPartialPreflight.control test)) p=some (some p) := by
            rw [hfstar,evV_seq_ok hfst]; exact evV_not_fail hstep
          rw [evV_seq_ok hfilter]
          obtain ⟨q,hrun⟩ := PartialCodewordTotality.run_total g x .callByValueSeq T E p hp
          have hc : evV g x .callByValueSeq T E (.call 1 [runA]) p=none := by
            rw [evV_call_seq r1 rfl]
            simp only [evSeqArgs,hrun]
            simp only [T,tblV,valAt_nil]
          apply evV_seq_none
          change evV g x .callByValueSeq T E (.andP (.call 1 [runA])) p=none
          rw [CallLookahead.evV_peek,hc]; rfl
        | some q =>
          obtain ⟨a,hA,hguard⟩ := seq_success g x .callByValueSeq T E _ _ p q hstep
          have hc : evV g x .callByValueSeq T E (.call 0 [scanner]) p=none := by
            rw [evV_call_seq r0 rfl]
            simp only [evSeqArgs,hA]
            simp only [T,tblV,valAt_nil]
          have htoken : evV g x .callByValueSeq T E
              (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) .token) p=none := by
            change evV g x .callByValueSeq T E
              (.seq (look scanner) (.seq (look (.call 0 [scanner])) scanner)) p=none
            rw [evV_seq_ok (look_ok g x .callByValueSeq T E _ p a hA)]
            apply evV_seq_none
            change evV g x .callByValueSeq T E (.andP (.call 0 [scanner])) p=none
            rw [CallLookahead.evV_peek,hc]; rfl
          have hf : evV g x .callByValueSeq T E f p=none := by
            change evV g x .callByValueSeq T E
              (.seq (look (step test))
                (.seq (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) .token)
                  (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) (.test (.seq scanner test))))) p=none
            rw [evV_seq_ok (look_ok g x .callByValueSeq T E _ p q hstep),evV_seq_none htoken]
          have hfst : evV g x .callByValueSeq T E (.star f) p=none := evStar_none hf
          have hfilter : evV g x .callByValueSeq T E
              (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
                (ControlledPartialPreflight.control test)) p=none := by
            rw [hfstar,evV_seq_none hfst]
          exact evV_seq_none hfilter

theorem zero (g g' : MGrammar) (x : List Char) (i binary unary p : Nat)
    (E E' : List (List Char)) (test test' b : MExp) (hp : p≤x.length)
    (sourceRule : ruleAtM g.rules i=some ⟨1,.seq scanner (.seq (.param 0) b)⟩)
    (r0 : ruleAtM g'.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g'.rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩) :
    evV g x .callByValuePar (tblV g x .callByValuePar 0) E (.call i [argument test]) p=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq 0) E' (entry binary unary test') p := by
  have hs : evV g x .callByValuePar (tblV g x .callByValuePar 0) E
      (.call i [argument test]) p=none := by
    rw [evV_call_par sourceRule rfl (by decide)]
    cases ha : evV g x .callByValuePar (tblV g x .callByValuePar 0) E (argument test) p with
    | none => simp only [evParArgs,ha]
    | some r => cases r with
      | none => exact False.elim (argument_ne_fail g x .callByValuePar _ E test p hp ha)
      | some j =>
        simp only [evParArgs,ha]
        simp only [tblV,valAt_nil]
  rw [hs,entry]
  symm
  apply evV_seq_none
  change evV g' x .callByValueSeq (tblV g' x .callByValueSeq 0) E'
    (.andP (preflight test')) p=none
  rw [CallLookahead.evV_peek,preflight_zero g' x E' test' p hp r0 r1]; rfl

end Shallot.MacroPeg.CBV.ControlledPartialEntry
