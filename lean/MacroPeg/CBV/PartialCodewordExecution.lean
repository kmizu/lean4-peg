import MacroPeg.CBV.PartialCodewordCapture
import MacroPeg.CBV.CodewordControlFilter

/-! Unbounded operational calculations for the partial-codeword candidate.
These calculations do not establish all-input equivalence. -/
namespace Shallot.MacroPeg.CBV.PartialCodewordExecution
open PartialCodewordCapture
open RuntimeShiftFilter (block scanner)
open CodewordReplay (power)
open ClockFreezing (Table)
open LastCodewordCandidate (literal_at)

def firstPiece (k : Nat) : List Char := List.replicate k 'a'
def secondPiece (k n : Nat) : List Char := '#'::captured k n

theorem pieces_join (k n : Nat) :
    firstPiece k++secondPiece k n=captured k (n+1) := by
  simp [firstPiece,secondPiece,captured,block,power,List.replicate_succ,List.append_assoc]

theorem word_boundary (k n : Nat) (rest : List Char) :
    power (block k) (n+1)++firstPiece k++'!'::rest=
      captured k n++('#'::(firstPiece k++'!'::rest)) := by
  rw [LastCodewordCandidate.power_succ_right]
  simp [captured,block,firstPiece,List.append_assoc]

/-- Both sequential arguments are evaluated in the same original caller
E. Their actual captures are the two pieces of the original Par value;
the second parser is not given the first argument's newly captured value. -/
theorem split_arguments (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (k n p : Nat) (rest : List Char)
    (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+2)++firstPiece k++'!'::rest) :
    evSeqArgs g x s T E [runA,restArgument] p=
      some (some ([firstPiece k,secondPiece k n],
        ('#'::(firstPiece k++'!'::rest)).length)) := by
  let r := power (block k) (n+1)++firstPiece k++'!'::rest
  have hs' : sfx x p=firstPiece k++'#'::r := by
    simpa [r,firstPiece,block,power,List.replicate_succ,List.append_assoc] using hs
  have hfirst := run_at g x s T E k p '#' r (by decide) hp hs'
  have hlen := congrArg List.length hs'
  rw [length_sfx x hp,List.length_append] at hlen
  have hj : ('#'::r).length≤x.length := by omega
  have hsfirst : sfx x ('#'::r).length='#'::r :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨firstPiece k,hs'⟩).choose_spec
  have hsafter : sfx x r.length=r :=
    sfx_suffix (suffix_trans (sfx_is_suffix x ('#'::r).length) ⟨['#'],hsfirst⟩).choose_spec
  have hr : r.length≤x.length := by simp only [List.length_cons] at hj; omega
  have hhash := literal_at g x s T E ['#'] r ('#'::r).length hsfirst
  have harg := argument_at g x s T E k n r.length rest hr hsafter
  have hsecond : evV g x s T E restArgument ('#'::r).length=
      some (some ('#'::(firstPiece k++'!'::rest)).length) := by
    rw [restArgument,evV_seq_ok hhash]
    exact harg
  have hcfirst : pre x p ('#'::r).length=firstPiece k := by
    have hh := pre_eq (sfx_is_suffix x p) hs'
    simpa only [length_sfx x hp] using hh
  have hssecond : sfx x ('#'::r).length=
      secondPiece k n++('#'::(firstPiece k++'!'::rest)) := by
    rw [hsfirst]
    simp only [r]
    rw [word_boundary]
    rfl
  have hcsecond : pre x ('#'::r).length ('#'::(firstPiece k++'!'::rest)).length=
      secondPiece k n := by
    have hh := pre_eq (sfx_is_suffix x ('#'::r).length) hssecond
    simpa only [length_sfx x hj] using hh
  rw [evSeq_cons_ok hfirst,evSeq_cons_ok hsecond]
  simp only [evSeqArgs,hcfirst,hcsecond]

/-- At the concrete input origin, the two real captures reconstruct the
same complete original value, for every length and positive word count. -/
theorem actual_split (g : MGrammar) (s : Strategy) (T : Table)
    (E : List (List Char)) (k n : Nat) :
    let x := input k (n+1)
    evSeqArgs g x s T E [runA,restArgument] x.length=
      some (some ([firstPiece k,secondPiece k n],
        ('#'::(firstPiece k++'!'::captured k (n+1))).length)) ∧
    firstPiece k++secondPiece k n=captured k (n+1) := by
  dsimp only []
  refine ⟨?_,pieces_join k n⟩
  apply split_arguments g (input k (n+1)) s T E k n _ (captured k (n+1)) (Nat.le_refl _)
  rw [sfx_self]
  simp [input,captured,power,List.replicate_succ,firstPiece,List.append_assoc]

/-- Once the original head and replay finish, an arbitrary continuation
runs with the whole actual capture. No definedness assumption on b. -/
theorem source_body_at (g : MGrammar) (s : Strategy) (T : Table)
    (k n : Nat) (b : MExp) :
    let x := input k n
    let w := captured k n
    evV g x s T [w] (.seq scanner (.seq (.param 0) b)) x.length=
      evV g x s T [w] b ('!'::w).length := by
  dsimp only []
  let x := input k n
  let w := captured k n
  have hx : x=block k++(w++('!'::w)) := by simp [x,w,input,List.append_assoc]
  have hs : sfx x x.length=block k++(w++('!'::w)) := by rw [sfx_self]; exact hx
  have hh := PrefixCodeCapture.scanner_at g x s T [w] x.length k (w++('!'::w)) (Nat.le_refl _) hs
  have hr : sfx x (w++('!'::w)).length=w++('!'::w) := sfx_suffix hx
  have hp : evV g x s T [w] (.param 0) (w++('!'::w)).length=
      some (some ('!'::w).length) := literal_at g x s T [] w ('!'::w) _ hr
  rw [evV_seq_ok hh,evV_seq_ok hp]

/-- Two actual Seq values restore the whole source environment in every
first-order continuation, including failed or undefined continuations. -/
theorem split_body_at (g : MGrammar) (s : Strategy) (T : Table)
    (k n : Nat) (b : MExp) (hb : b.FirstOrder) :
    let x := input k (n+1)
    let w := captured k (n+1)
    let W := [firstPiece k,secondPiece k n]
    evV g x s T W (.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView b)))
      ('#'::(firstPiece k++'!'::w)).length=
      evV g x s T [w] b ('!'::w).length := by
  dsimp only []
  let x := input k (n+1)
  let w := captured k (n+1)
  let W := [firstPiece k,secondPiece k n]
  have hx : x=w++('#'::(firstPiece k++'!'::w)) := input_split k (n+1)
  have hs : sfx x ('#'::(firstPiece k++'!'::w)).length='#'::(firstPiece k++'!'::w) := sfx_suffix hx
  have hhash := literal_at g x s T W ['#'] (firstPiece k++'!'::w) _ hs
  have hsrun : sfx x (firstPiece k++'!'::w).length=firstPiece k++'!'::w :=
    sfx_suffix (show x=(w++['#'])++(firstPiece k++'!'::w) by simpa [List.append_assoc] using hx)
  have hrun : evV g x s T W (.param 0) (firstPiece k++'!'::w).length=
      some (some ('!'::w).length) := literal_at g x s T [] (firstPiece k) ('!'::w) _ hsrun
  rw [evV_seq_ok hhash,evV_seq_ok hrun,
    CodewordControlFilter.wholeView_eval g x s T (firstPiece k) (secondPiece k n) b hb,
    pieces_join]

/-- A local complete-partial-result bridge at the actual capture endpoints.
It does not supply the caller preflight or recursive row correspondence. -/
theorem bodies_eq (g : MGrammar) (s : Strategy) (T : Table)
    (k n : Nat) (b : MExp) (hb : b.FirstOrder) :
    let x := input k (n+1)
    evV g x s T [captured k (n+1)] (.seq scanner (.seq (.param 0) b)) x.length=
      evV g x s T [firstPiece k,secondPiece k n]
        (.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView b)))
        ('#'::(firstPiece k++'!'::captured k (n+1))).length :=
  (source_body_at g s T k (n+1) b).trans (split_body_at g s T k n b hb).symm

private theorem look_ok (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a : MExp) (p q : Nat)
    (h : evV g x s T E a p=some (some q)) :
    evV g x s T E (look a) p=some (some p) := by
  change evV g x s T E (.andP a) p=_
  rw [CallLookahead.evV_peek,h]
  rfl

private theorem word_then (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (k p : Nat) (rest : List Char) (b : MExp)
    (hs : sfx x p=('#'::firstPiece k)++rest) :
    evV g x s T [firstPiece k] (.seq (.lit ['#']) (.seq (.param 0) b)) p=
      evV g x s T [firstPiece k] b rest.length := by
  have hh := literal_at g x s T [firstPiece k] ['#'] (firstPiece k++rest) p hs
  have hs' : sfx x (firstPiece k++rest).length=firstPiece k++rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨['#'],hs⟩).choose_spec
  have hp : evV g x s T [firstPiece k] (.param 0) (firstPiece k++rest).length=
      some (some rest.length) := literal_at g x s T [] (firstPiece k) rest _ hs'
  rw [evV_seq_ok hh,evV_seq_ok hp]

/-- The actual preflight compares arbitrarily many runs of arbitrary
length. It leaves the final shifted copy outside the greedy loop and
checks the concrete continuation marker at its real endpoint. -/
theorem check_at (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (k n p : Nat) (rest : List Char) (hp : p≤x.length)
    (hs : sfx x p=power ('#'::firstPiece k) (n+1)++'!'::rest) :
    evV g x s T [firstPiece k] checkBody p=some (some ('!'::rest).length) := by
  let u := '#'::firstPiece k
  let f := fun q => evV g x s T [firstPiece k]
    (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))) q
  have loop : ∀ n p, p≤x.length → sfx x p=power u (n+1)++'!'::rest →
      evStar f p=some (some (u++'!'::rest).length) := by
    intro n
    induction n with
    | zero =>
      intro q hq hs
      have hs' : sfx x q=u++'!'::rest := by simpa [power] using hs
      have hbang : sfx x ('!'::rest).length='!'::rest :=
        sfx_suffix (suffix_trans (sfx_is_suffix x q) ⟨u,hs'⟩).choose_spec
      have hf : f q=some none := by
        rw [show f q=evV g x s T [firstPiece k]
          (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))) q from rfl,
          word_then g x s T k q ('!'::rest) _ hs']
        simp only [look,evV,hbang]
        rfl
      rw [evStar_fail hf]
      have hlen := congrArg List.length hs'
      rw [length_sfx x hq] at hlen
      exact congrArg (fun t => some (some t)) hlen
    | succ n ih =>
      intro q hq hs
      let r := power u (n+1)++'!'::rest
      have hs' : sfx x q=u++r := by simpa [r,power,List.replicate_succ,List.append_assoc] using hs
      have hr : r.length<q := by
        have hh := congrArg List.length hs'
        rw [length_sfx x hq,List.length_append] at hh
        have hu : 0<u.length := by simp [u]
        omega
      have hsr : sfx x r.length=r :=
        sfx_suffix (suffix_trans (sfx_is_suffix x q) ⟨u,hs'⟩).choose_spec
      have hhash : evV g x s T [firstPiece k] (.lit ['#']) r.length=
          some (some (firstPiece k++(power u n++'!'::rest)).length) := by
        apply literal_at
        simpa [r,power,List.replicate_succ,u,List.append_assoc] using hsr
      have hf : f q=some (some r.length) := by
        rw [show f q=evV g x s T [firstPiece k]
          (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))) q from rfl,
          word_then g x s T k q r _ hs']
        exact look_ok g x s T _ _ _ _ hhash
      rw [evStar_ok hf hr]
      exact ih r.length (by omega) hsr
  have hl := loop n p hp hs
  change evV g x s T [firstPiece k]
    (.star (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#']))))) p=_ at hl
  have hsfinal : sfx x (u++'!'::rest).length=u++'!'::rest := by
    have hh : sfx x p=power u n++(u++'!'::rest) := by
      rw [hs,LastCodewordCandidate.power_succ_right,List.append_assoc]
    exact sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨power u n,hh⟩).choose_spec
  rw [checkBody,evV_seq_ok hl,word_then g x s T k _ ('!'::rest) _ hsfinal]
  apply look_ok
  apply literal_at
  exact sfx_suffix (suffix_trans (sfx_is_suffix x (u++'!'::rest).length) ⟨u,hsfinal⟩).choose_spec

theorem input_rotated (k n : Nat) :
    input k n=firstPiece k++(power ('#'::firstPiece k) (n+1)++'!'::captured k n) := by
  have go : ∀ m, power (block k) m++firstPiece k=
      firstPiece k++power ('#'::firstPiece k) m := by
    intro m
    induction m with
    | zero => simp [power]
    | succ m ih =>
      have hleft : power (block k) (m+1)=block k++power (block k) m := by
        simp [power,List.replicate_succ]
      have hright : power ('#'::firstPiece k) (m+1)=
          ('#'::firstPiece k)++power ('#'::firstPiece k) m := by
        simp [power,List.replicate_succ]
      rw [hleft,hright,List.append_assoc,ih]
      simp [block,firstPiece,List.append_assoc]
  calc
    input k n = (power (block k) (n+1)++firstPiece k)++('!'::captured k n) := by
      simp [input,captured,power,List.replicate_succ,firstPiece,List.append_assoc]
    _ = _ := by rw [go]; simp only [List.append_assoc]

/-- The real lookahead call succeeds on every member of the unbounded
family, using the original physical stage-one Seq table. -/
theorem preflight_execution (k n : Nat) :
    let x := input k n
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) []
      (.call 0 [runA]) x.length=some (some ('!'::captured k n).length) := by
  dsimp only []
  let x := input k n
  let T := tblV target x .callByValueSeq 1
  let r := power ('#'::firstPiece k) (n+1)++'!'::captured k n
  have hx : x=firstPiece k++r := input_rotated k n
  have hr : sfx x r.length=r := sfx_suffix hx
  have hb : r.length≤x.length := by have := congrArg List.length hx; simp only [List.length_append] at this; omega
  have hrun : evV target x .callByValueSeq T [] runA x.length=some (some r.length) := by
    have h := run_at target x .callByValueSeq T [] k x.length '#'
      (firstPiece k++(power ('#'::firstPiece k) n++'!'::captured k n)) (by decide) (Nat.le_refl _) (by
        rw [sfx_self,hx]
        simp [r,power,List.replicate_succ,firstPiece,List.append_assoc])
    simpa [r,power,List.replicate_succ,List.append_assoc] using h
  have hcap : pre x x.length r.length=firstPiece k := pre_eq ⟨[],by simp⟩ hx
  have rule : ruleAtM target.rules 0=some ⟨1,checkBody⟩ := rfl
  change evV target x .callByValueSeq T [] (.call 0 [runA]) x.length=_
  rw [evV_call_seq rule rfl]
  simp only [evSeqArgs,hrun,hcap]
  rw [valAt_tblV_succ rule _ hb]
  exact check_at target x .callByValueSeq _ k n r.length (captured k n) hb hr

private theorem copy_tail (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w : List Char) (p : Nat) (hs : sfx x p='!'::w) :
    evV g x s T [w] (.seq (.lit ['!']) (.seq (.param 0) eof)) p=some (some 0) := by
  have hbang := literal_at g x s T [w] ['!'] w p hs
  have hsw : sfx x w.length=w :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨['!'],hs⟩).choose_spec
  have hw : evV g x s T [w] (.param 0) w.length=some (some 0) :=
    literal_at g x s T [] w [] _ (by simpa using hsw)
  rw [evV_seq_ok hbang,evV_seq_ok hw]
  simp [eof,evV,sfx]

/-- The single original Par grammar accepts the entire intended family,
not just the six concrete executions used to explore the candidate. -/
theorem source_execution (k n : Nat) :
    let x := input k n
    evV source x .callByValuePar (tblV source x .callByValuePar 1) [] sourceRoot x.length=
      some (some 0) := by
  dsimp only []
  let x := input k n
  let T := tblV source x .callByValuePar 1
  have hc := actual_capture source .callByValuePar T [] k n
  dsimp only [] at hc
  have rule : ruleAtM source.rules 0=some ⟨1,.seq scanner (.seq (.param 0)
      (.seq (.lit ['!']) (.seq (.param 0) eof)))⟩ := rfl
  change evV source x .callByValuePar T [] sourceRoot x.length=_
  rw [sourceRoot,evV_call_par rule rfl (by decide)]
  have harg : evV source x .callByValuePar T [] argument x.length=
      some (some ('#'::(firstPiece k++'!'::captured k n)).length) := hc.1
  have hcap : pre x x.length ('#'::(firstPiece k++'!'::captured k n)).length=captured k n := hc.2
  simp only [evParArgs,harg,hcap]
  rw [valAt_tblV_succ rule _ (Nat.le_refl _),source_body_at]
  apply copy_tail
  exact sfx_suffix (show input k n=(block k++captured k n)++('!'::captured k n) by
    simp [input,List.append_assoc])

private theorem binary_body_execution (g : MGrammar) (s : Strategy) (T : Table) (k n : Nat) :
    let x := input k (n+1)
    evV g x s T [firstPiece k,secondPiece k n] target.rules[1].body
      ('#'::(firstPiece k++'!'::captured k (n+1))).length=some (some 0) := by
  dsimp only []
  let x := input k (n+1)
  let w := captured k (n+1)
  let W := [firstPiece k,secondPiece k n]
  have hx : x=w++('#'::(firstPiece k++'!'::w)) := input_split k (n+1)
  have hs : sfx x ('#'::(firstPiece k++'!'::w)).length='#'::(firstPiece k++'!'::w) := sfx_suffix hx
  have hh := literal_at g x s T W ['#'] (firstPiece k++'!'::w) _ hs
  have hsrun : sfx x (firstPiece k++'!'::w).length=firstPiece k++'!'::w :=
    sfx_suffix (show x=(w++['#'])++(firstPiece k++'!'::w) by simpa [List.append_assoc] using hx)
  have hp : evV g x s T W (.param 0) (firstPiece k++'!'::w).length=
      some (some ('!'::w).length) := literal_at g x s T [] (firstPiece k) ('!'::w) _ hsrun
  have hsrest : sfx x ('!'::w).length='!'::w :=
    sfx_suffix (show x=(block k++w)++('!'::w) by simp [x,w,input,List.append_assoc])
  have hbang := literal_at g x s T W ['!'] w _ hsrest
  have hsw : sfx x w.length=firstPiece k++secondPiece k n := by
    rw [pieces_join]
    exact sfx_suffix (show x=((block k++w)++['!'])++w by simp [x,w,input,List.append_assoc])
  have hfirst : evV g x s T W (.param 0) w.length=some (some (secondPiece k n).length) :=
    literal_at g x s T [] (firstPiece k) (secondPiece k n) _ hsw
  have hssecond : sfx x (secondPiece k n).length=secondPiece k n :=
    sfx_suffix (suffix_trans (sfx_is_suffix x w.length) ⟨firstPiece k,hsw⟩).choose_spec
  have hsecond : evV g x s T W (.param 1) (secondPiece k n).length=some (some 0) :=
    literal_at g x s T [] (secondPiece k n) [] _ (by simpa using hssecond)
  change evV g x s T W (.seq (.lit ['#']) (.seq (.param 0) (.seq (.lit ['!'])
      (.seq (.param 0) (.seq (.param 1) eof))))) _=_
  rw [evV_seq_ok hh,evV_seq_ok hp,evV_seq_ok hbang,evV_seq_ok hfirst,evV_seq_ok hsecond]
  simp [eof,evV,sfx]

/-- The long branch's fixed grammar, including its real preflight and
actual two captures, accepts every positive-count member. -/
theorem target_positive_execution (k n : Nat) :
    let x := input k (n+1)
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) [] targetRoot x.length=
      some (some 0) := by
  dsimp only []
  let x := input k (n+1)
  let T := tblV target x .callByValueSeq 1
  let w := captured k (n+1)
  let r := captured k n++'!'::w
  have hx : x=block k++(block k++r) := by
    simp [x,r,w,input,captured,power,List.replicate_succ,List.append_assoc]
  have hfirst := PrefixCodeCapture.scanner_at target x .callByValueSeq T [] x.length k
    (block k++r) (Nat.le_refl _) (by rw [sfx_self]; exact hx)
  have hbound : (block k++r).length≤x.length := by
    have hh := congrArg List.length hx; simp only [List.length_append] at hh ⊢; omega
  have hsecond := PrefixCodeCapture.scanner_at target x .callByValueSeq T [] (block k++r).length k r
    hbound (sfx_suffix hx)
  have hlong : evV target x .callByValueSeq T [] longTest x.length=some (some x.length) := by
    apply look_ok
    rw [evV_seq_ok hfirst]
    exact hsecond
  have hc : evV target x .callByValueSeq T [] (.call 0 [runA]) x.length=
      some (some ('!'::w).length) := preflight_execution k (n+1)
  have hcheck := look_ok target x .callByValueSeq T [] _ _ _ hc
  have hargs := (actual_split target .callByValueSeq T [] k n).1
  change evSeqArgs target x .callByValueSeq T [] [runA,restArgument] x.length=
      some (some ([firstPiece k,secondPiece k n],('#'::(firstPiece k++'!'::w)).length)) at hargs
  have rule : ruleAtM target.rules 1=some ⟨2,target.rules[1].body⟩ := rfl
  have hq : ('#'::(firstPiece k++'!'::w)).length≤x.length := by
    have hh := congrArg List.length (input_split k (n+1))
    simp only [List.length_append] at hh
    change ('#'::(firstPiece k++'!'::captured k (n+1))).length≤(input k (n+1)).length
    simp only [firstPiece] at *
    omega
  have hcall : evV target x .callByValueSeq T [] (.call 1 [runA,restArgument]) x.length=some (some 0) := by
    rw [evV_call_seq rule rfl,hargs]
    simp only []
    rw [valAt_tblV_succ rule _ hq]
    exact binary_body_execution target .callByValueSeq _ k n
  change evV target x .callByValueSeq T [] targetRoot x.length=_
  rw [targetRoot,evV_seq_ok hcheck]
  apply evV_alt_ok
  rw [evV_seq_ok hlong]
  exact hcall

/-- The zero-count branch keeps a possibly empty run shorter than its
runtime header; it does not invoke the binary-capture branch. -/
theorem target_zero_execution (k : Nat) :
    let x := input k 0
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) [] targetRoot x.length=
      some (some 0) := by
  dsimp only []
  let x := input k 0
  let T := tblV target x .callByValueSeq 1
  let w := firstPiece k
  let r := w++'!'::w
  have hx : x=w++('#'::r) := by simp [x,w,r,input,captured,power,block,firstPiece,List.append_assoc]
  have hr : sfx x r.length=r := sfx_suffix
    (show x=(w++['#'])++r by simpa [List.append_assoc] using hx)
  have hbound : r.length≤x.length := by
    have hh := congrArg List.length hx
    simp only [List.length_append,List.length_cons] at hh
    omega
  have hrun := run_at target x .callByValueSeq T [] k x.length '#' r (by decide)
    (Nat.le_refl _) (by rw [sfx_self]; exact hx)
  have hrun' := run_at target x .callByValueSeq T [] k r.length '!' w (by decide) hbound hr
  have hbang : sfx x ('!'::w).length='!'::w :=
    sfx_suffix (suffix_trans (sfx_is_suffix x r.length) ⟨w,hr⟩).choose_spec
  have hstop : evV target x .callByValueSeq T [] scanner r.length=some none := by
    rw [show scanner=.seq runA (.lit ['#']) from rfl,evV_seq_ok hrun']
    simp only [evV,hbang]
    rfl
  have hfirst := PrefixCodeCapture.scanner_at target x .callByValueSeq T [] x.length k r
    (Nat.le_refl _) (by rw [sfx_self]; simpa [block,w,firstPiece,List.append_assoc] using hx)
  have hlong : evV target x .callByValueSeq T [] longTest x.length=some none := by
    change evV target x .callByValueSeq T [] (.andP (.seq scanner scanner)) x.length=_
    rw [CallLookahead.evV_peek,evV_seq_ok hfirst,hstop]
    rfl
  have hnot : evV target x .callByValueSeq T [] (.notP longTest) x.length=some (some x.length) := by
    simp only [evV,hlong]
  have hc : evV target x .callByValueSeq T [] (.call 0 [runA]) x.length=
      some (some ('!'::w).length) := preflight_execution k 0
  have hcheck := look_ok target x .callByValueSeq T [] _ _ _ hc
  have hcap : pre x x.length ('#'::r).length=w := pre_eq ⟨[],by simp⟩ hx
  have rule : ruleAtM target.rules 2=some ⟨1,target.rules[2].body⟩ := rfl
  have hq : ('#'::r).length≤x.length := by
    have hh := congrArg List.length hx
    simp only [List.length_append] at hh
    omega
  have hcall : evV target x .callByValueSeq T [] (.call 2 [runA]) x.length=some (some 0) := by
    rw [evV_call_seq rule rfl]
    simp only [evSeqArgs,hrun,hcap]
    rw [valAt_tblV_succ rule _ hq]
    have hs : sfx x ('#'::r).length=('#'::w)++('!'::w) := by
      simpa [r] using sfx_suffix hx
    change evV target x .callByValueSeq (tblV target x .callByValueSeq 0) [w]
      (.seq (.lit ['#']) (.seq (.param 0) (.seq (.lit ['!']) (.seq (.param 0) eof)))) _=_
    rw [word_then target x .callByValueSeq _ k _ ('!'::w) _ hs]
    exact copy_tail target x .callByValueSeq _ w _ hbang
  change evV target x .callByValueSeq T [] targetRoot x.length=_
  rw [targetRoot,evV_seq_ok hcheck,evV_alt_fail (evV_seq_fail hlong),evV_seq_ok hnot]
  exact hcall

theorem target_execution (k n : Nat) :
    let x := input k n
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) [] targetRoot x.length=
      some (some 0) := by
  cases n with
  | zero => exact target_zero_execution k
  | succ n => exact target_positive_execution k n

/-- Both single fixed grammars accept on the original strings for every
runtime word length and every number of captured complete words. This
remains a positive family, not an all-input equivalence theorem. -/
theorem family_observations (k n : Nat) :
    SObs source .callByValuePar sourceRoot (input k n) (some []) ∧
    SObs target .callByValueSeq targetRoot (input k n) (some []) := by
  have derive (g : MGrammar) (s : Strategy) (e : MExp)
      (hg : g.FirstOrder) (hs : s≠.callByName) (he : e.FirstOrder)
      (h : evV g (input k n) s (tblV g (input k n) s 1) [] e (input k n).length=some (some 0)) :
      SObs g s e (input k n) (some []) := by
    obtain ⟨o,hd,ho⟩ := evV_derives hg hs he 1 (Nat.le_refl _) h
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  exact ⟨derive source .callByValuePar sourceRoot firstOrder.1 (by decide)
      firstOrder.2.2.1 (source_execution k n),
    derive target .callByValueSeq targetRoot firstOrder.2.1 (by decide)
      firstOrder.2.2.2 (target_execution k n)⟩

end Shallot.MacroPeg.CBV.PartialCodewordExecution
