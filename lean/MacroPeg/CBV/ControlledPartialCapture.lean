import MacroPeg.CBV.PartialCodewordTotality

/-! Actual split captures with caller-dependent stopping conditions. These
entry lemmas do not yet supply a complete recursive Par-to-Seq compiler. -/
namespace Shallot.MacroPeg.CBV.ControlledPartialCapture
open ClockFreezing (Table)
open RuntimeShiftFilter (scanner block)
open PartialCodewordCapture (runA look captured)
open PartialCodewordExecution (firstPiece)
open CodewordReplay (power)

def step (test : MExp) : MExp := .seq scanner (look (.seq scanner test))
def argument (test : MExp) : MExp := .seq (.star (step test)) runA
def restArgument (test : MExp) : MExp := .seq (.lit ['#']) (argument test)

theorem argument_firstOrder (test : MExp) (ht : test.FirstOrder) :
    (argument test).FirstOrder := by
  simpa [argument,step,look,scanner,runA,NestedScannerArguments.scan,
    NestedScannerArguments.choice,MExp.FirstOrder,MExp.failAlways] using ht

private theorem seq_success (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (a b : MExp) (p q : Nat)
    (h : evV g x s T E (.seq a b) p=some (some q)) :
    ∃ j, evV g x s T E a p=some (some j) ∧ evV g x s T E b j=some (some q) := by
  cases ha : evV g x s T E a p with
  | none => rw [evV_seq_none ha] at h; cases h
  | some r => cases r with
    | none => rw [evV_seq_fail ha] at h; cases h
    | some j => rw [evV_seq_ok ha] at h; exact ⟨j,rfl,h⟩

/-- Peel the actual first iteration, preserving every possible later
result, including divergence in a caller-dependent or recursive test. -/
theorem peel (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p j : Nat)
    (h : evV g x s T E (step test) p=some (some j)) (hj : j<p) :
    evV g x s T E (argument test) p=evV g x s T E (argument test) j := by
  change (match evStar (fun z => evV g x s T E (step test) z) p with
    | some (some q) => evV g x s T E runA q | other => other)=_
  rw [evStar_ok h hj]
  rfl

/-- If the original iteration stops immediately, the sole capture is
exactly the final run; no alternative stopping point is chosen. -/
theorem zero (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p : Nat)
    (h : evV g x s T E (step test) p=some none) :
    evV g x s T E (argument test) p=evV g x s T E runA p := by
  change (match evStar (fun z => evV g x s T E (step test) z) p with
    | some (some q) => evV g x s T E runA q | other => other)=_
  rw [evStar_fail h]

theorem undefined (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p : Nat)
    (h : evV g x s T E (step test) p=none) :
    evV g x s T E (argument test) p=none := by
  change (match evStar (fun z => evV g x s T E (step test) z) p with
    | some (some q) => evV g x s T E runA q | other => other)=_
  rw [evStar_none h]

/-- A genuinely undefined stopping test is not converted into a shorter
successful capture, at any table or caller environment. -/
theorem test_none (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p j k : Nat)
    (hfirst : evV g x s T E scanner p=some (some j))
    (hnext : evV g x s T E scanner j=some (some k))
    (htest : evV g x s T E test k=none) :
    evV g x s T E (argument test) p=none := by
  apply undefined
  rw [step,evV_seq_ok hfirst]
  change evV g x s T E (.andP (.seq scanner test)) j=none
  rw [CallLookahead.evV_peek,evV_seq_ok hnext,htest]; rfl

theorem argument_le (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E (argument test) p=some (some q)) : q≤p := by
  obtain ⟨j,hstar,hrun⟩ := seq_success g x s T E _ _ p q h
  have hj : j≤p := evStar_le p j hstar
  rw [runA,NestedScannerArguments.scan_eval g x s T E ['a'] j (by omega)] at hrun
  have he := Option.some.inj (Option.some.inj hrun)
  have hl := congrArg List.length (List.takeWhile_append_dropWhile
    (p := NestedScannerArguments.accepts ['a']) (l := sfx x j))
  rw [List.length_append,length_sfx x (by omega : j≤x.length)] at hl
  omega

/-- Only the final greedy a-run determines this boundary. Earlier
iterations may stop for a parent-dependent reason while full words remain. -/
theorem argument_stop (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E (argument test) p=some (some q)) :
    (sfx x q).head?≠some 'a' := by
  obtain ⟨j,hstar,hrun⟩ := seq_success g x s T E _ _ p q h
  have hj : j≤p := evStar_le p j hstar
  rw [runA,NestedScannerArguments.scan_eval g x s T E ['a'] j (by omega)] at hrun
  have hq := Option.some.inj (Option.some.inj hrun)
  have hs : sfx x q=(sfx x j).dropWhile (NestedScannerArguments.accepts ['a']) := by
    rw [←hq]
    exact sfx_suffix (suffix_trans (sfx_is_suffix x j)
      ⟨(sfx x j).takeWhile (NestedScannerArguments.accepts ['a']),
        List.takeWhile_append_dropWhile.symm⟩).choose_spec
  rw [hs]
  have stop : ∀ l : List Char,
      (l.dropWhile (NestedScannerArguments.accepts ['a'])).head?≠some 'a' := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
      cases hc : NestedScannerArguments.accepts ['a'] c with
      | true => simpa [List.dropWhile_cons,hc] using ih
      | false =>
        simp only [List.dropWhile_cons,hc,Bool.false_eq_true,↓reduceIte,List.head?_cons]
        intro he
        have he' : c='a' := Option.some.inj he
        subst c
        cases hc
  exact stop _

/-- Real capture and replay still force a uniform partial codeword when
the test changes the captured length. No maximal-run or terminal-scanner
failure premise is imposed. Tests can read E and call users recursively. -/
theorem source_prefix_shape (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (test : MExp) (ht : test.FirstOrder)
    (p j q : Nat) (hp : p≤x.length)
    (ha : evV g x s T E (argument test) p=some (some j))
    (hh : evV g x s T [pre x p j] (.seq scanner (.param 0)) p=some (some q)) :
    ∃ k n, pre x p j=captured k n ∧
      sfx x p=power (block k) (n+1)++firstPiece k++sfx x q ∧
      sfx x j='#'::(firstPiece k++sfx x q) := by
  let w := pre x p j
  have hprefix := (WordStarFilter.success_prefix hs hT E (argument test)
    (argument_firstOrder test ht) p j hp ha).2
  have hstop := argument_stop g x s T E test p j hp ha
  obtain ⟨v,hscan,hw⟩ := seq_success g x s T [w] _ _ p q hh
  obtain ⟨k,hk⟩ := PartialCodewordClassification.scanner_shape g x s T [w] p v hp hscan
  have hw' : sfx x v=w++sfx x q := by
    cases hr : Shallot.stripPrefix? w (sfx x v) with
    | none => simp [evV,hr] at hw
    | some rest =>
      have he : rest.length=q := by simpa only [evV,List.getElem?_cons_zero,hr,
        Option.some.injEq] using hw
      have hx := (CBVtoCBN.stripPrefix_exact _ _ _).mp hr
      have hend : sfx x rest.length=rest :=
        sfx_suffix (suffix_trans (sfx_is_suffix x v) ⟨w,hx⟩).choose_spec
      rw [←he,hend]; exact hx
  have hsource : sfx x p=(block k++w)++sfx x q := by
    rw [hk,hw',List.append_assoc]
  obtain ⟨n,hn⟩ := PartialCodewordPreflight.stopped_overlap_tail k w (sfx x q)
    (sfx x j) (hsource.symm.trans hprefix) hstop
  have hshape : sfx x p=power (block k) (n+1)++firstPiece k++sfx x q := by
    simpa [hn,captured,firstPiece,power,List.replicate_succ,List.append_assoc] using hsource
  refine ⟨k,n,hn,hshape,?_⟩
  have hs' : sfx x p=captured k n++('#'::(firstPiece k++sfx x q)) := by
    rw [hshape,PartialCodewordPreflight.word_boundary]
  have he : w++sfx x j=w++('#'::(firstPiece k++sfx x q)) := by
    rw [←hprefix,hn]; exact hs'
  exact (List.append_right_inj w).mp he

/-- Two real Seq arguments, both evaluated in the unchanged caller E,
reach the source argument's actual endpoint. The stop test is neither
moved to a different word nor supplied with the new first capture. -/
theorem split_arguments (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p k q : Nat) (rest : List Char)
    (hp : p≤x.length) (hs : sfx x p=block k++rest)
    (hguard : evV g x s T E (look (.seq scanner test)) rest.length=
      some (some rest.length))
    (harg : evV g x s T E (argument test) p=some (some q)) :
    evSeqArgs g x s T E [runA,restArgument test] p=
      some (some ([firstPiece k,pre x ('#'::rest).length q],q)) ∧
    firstPiece k++pre x ('#'::rest).length q=pre x p q := by
  have hs' : sfx x p=firstPiece k++'#'::rest := by
    simpa [block,firstPiece] using hs
  have hlen := congrArg List.length hs'
  rw [length_sfx x hp] at hlen
  have hj : rest.length<p := by simp only [List.length_append,List.length_replicate,
    List.length_cons,firstPiece] at hlen; omega
  have hc : ('#'::rest).length≤x.length := by
    simp only [List.length_append,List.length_cons] at hlen ⊢; omega
  have hsf : sfx x ('#'::rest).length='#'::rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨firstPiece k,hs'⟩).choose_spec
  have hfirst := PartialCodewordCapture.run_at g x s T E k p '#' rest (by decide) hp hs'
  have hhead := PrefixCodeCapture.scanner_at g x s T E p k rest hp hs
  have hstep : evV g x s T E (step test) p=some (some rest.length) := by
    rw [step,evV_seq_ok hhead]; exact hguard
  have hrest := (peel g x s T E test p rest.length hstep hj).symm.trans harg
  have hhash := LastCodewordCandidate.literal_at g x s T E ['#'] rest _ hsf
  have hsecond : evV g x s T E (restArgument test) ('#'::rest).length=
      some (some q) := by
    rw [restArgument,evV_seq_ok hhash]; exact hrest
  have hcap : pre x p ('#'::rest).length=firstPiece k := by
    have hh := pre_eq (sfx_is_suffix x p) hs'
    simpa only [length_sfx x hp] using hh
  constructor
  · rw [evSeq_cons_ok hfirst,evSeq_cons_ok hsecond]
    simp only [evSeqArgs,hcap]
  · have hq := argument_le g x s T E test rest.length q (by omega) hrest
    rw [ScannerFrontier.pre_concat x p ('#'::rest).length q hp
      (by simp only [List.length_append,List.length_cons] at hlen ⊢; omega)
      (by simp; omega),hcap]

/-- After actual successful capture and initial replay, the split Seq
entry carries the same whole value into every first-order continuation.
The successful first guard is kept at its real original position. -/
theorem entry (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : Table) (hT : SoundTV g x s T) (E : List (List Char))
    (test : MExp) (ht : test.FirstOrder) (p k j q : Nat) (rest : List Char)
    (hp : p≤x.length) (hinput : sfx x p=block k++rest)
    (hguard : evV g x s T E (look (.seq scanner test)) rest.length=
      some (some rest.length))
    (harg : evV g x s T E (argument test) p=some (some j))
    (hprefix : evV g x s T [pre x p j] (.seq scanner (.param 0)) p=some (some q))
    (b : MExp) (hb : b.FirstOrder) :
    let v := pre x ('#'::rest).length j
    evSeqArgs g x s T E [runA,restArgument test] p=
      some (some ([firstPiece k,v],j)) ∧
    evV g x s T [pre x p j] (.seq (.seq scanner (.param 0)) b) p=
      evV g x s T [firstPiece k,v]
        (.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView b))) j := by
  dsimp only []
  obtain ⟨hargs,hjoin⟩ := split_arguments g x s T E test p k j rest hp hinput hguard harg
  refine ⟨hargs,?_⟩
  obtain ⟨l,n,hcap,hshape,hend⟩ := source_prefix_shape g x s hs T hT E test ht
    p j q hp harg hprefix
  have hkl : k=l := by
    have hh : (block k).IsPrefix (block l++
        (power (block l) n++firstPiece l++sfx x q)) := by
      refine ⟨rest,?_⟩
      simpa [power,List.replicate_succ,List.append_assoc] using hinput.symm.trans hshape
    exact (RuntimeShiftFilter.block_prefix k l _).mp hh
  subst l
  have hq : q≤x.length :=
    (WordStarFilter.success_prefix hs hT [pre x p j] _
      (by simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
        MExp.FirstOrder,MExp.failAlways]) p q hp hprefix).1
  have hhash := LastCodewordCandidate.literal_at g x s T
    [firstPiece k,pre x ('#'::rest).length j] ['#'] (firstPiece k++sfx x q) j hend
  have hrun : sfx x (firstPiece k++sfx x q).length=firstPiece k++sfx x q :=
    sfx_suffix (suffix_trans (sfx_is_suffix x j) ⟨['#'],hend⟩).choose_spec
  have hparam : evV g x s T [firstPiece k,pre x ('#'::rest).length j]
      (.param 0) (firstPiece k++sfx x q).length=some (some q) := by
    have hh := LastCodewordCandidate.literal_at g x s T [] (firstPiece k) (sfx x q) _ hrun
    simpa only [evV,List.getElem?_cons_zero,length_sfx x hq] using hh
  rw [evV_seq_ok hprefix,evV_seq_ok hhash,evV_seq_ok hparam,
    CodewordControlFilter.wholeView_eval g x s T (firstPiece k)
      (pre x ('#'::rest).length j) b hb,hjoin]

end Shallot.MacroPeg.CBV.ControlledPartialCapture
