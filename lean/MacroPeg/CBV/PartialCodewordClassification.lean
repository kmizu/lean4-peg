import MacroPeg.CBV.PartialCodewordExecution
import MacroPeg.CBV.OverlapNecessity

/-! Converse facts derived from the actual partial-codeword candidate.
The word count below is an execution witness, not grammar advice. -/
namespace Shallot.MacroPeg.CBV.PartialCodewordClassification
open PartialCodewordCapture
open PartialCodewordExecution (firstPiece)
open CodewordReplay (power)
open RuntimeShiftFilter (block scanner)
open PartialCodewordExecution (secondPiece)
open ClockFreezing (Table)

private theorem seq_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a b : MExp) (p q : Nat)
    (h : evV g x s T E (.seq a b) p=some (some q)) :
    ∃ j, evV g x s T E a p=some (some j) ∧ evV g x s T E b j=some (some q) := by
  cases ha : evV g x s T E a p with
  | none => rw [evV_seq_none ha] at h; cases h
  | some r => cases r with
    | none => rw [evV_seq_fail ha] at h; cases h
    | some j => rw [evV_seq_ok ha] at h; exact ⟨j,rfl,h⟩

private theorem look_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a : MExp) (p q : Nat)
    (h : evV g x s T E (look a) p=some (some q)) :
    q=p ∧ ∃ j, evV g x s T E a p=some (some j) := by
  change evV g x s T E (.andP a) p=_ at h
  rw [CallLookahead.evV_peek] at h
  cases ha : evV g x s T E a p with
  | none => simp [CallLookahead.peek,ha] at h
  | some r => cases r with
    | none => simp [CallLookahead.peek,ha] at h
    | some j =>
      have he : p=q := by simpa [CallLookahead.peek,ha] using h
      exact ⟨he.symm,j,rfl⟩

private theorem literal_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (w : List Char) (p q : Nat)
    (h : evV g x s T E (.lit w) p=some (some q)) :
    sfx x p=w++sfx x q := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [evV,hs] at h
  | some rest =>
    have hq : rest.length=q := by simpa only [evV,hs,Option.some.injEq] using h
    have hh := (CBVtoCBN.stripPrefix_exact _ _ _).mp hs
    have hr : sfx x rest.length=rest :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨w,hh⟩).choose_spec
    rw [←hq,hr]
    exact hh

private theorem word_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u : List Char) (b : MExp) (p q : Nat)
    (h : evV g x s T [u] (.seq (.lit ['#']) (.seq (.param 0) b)) p=some (some q)) :
    ∃ j, sfx x p=('#'::u)++sfx x j ∧ evV g x s T [u] b j=some (some q) := by
  obtain ⟨i,hh,ht⟩ := seq_success g x s T [u] _ _ p q h
  obtain ⟨j,hv,hb⟩ := seq_success g x s T [u] _ _ i q ht
  have hhash := literal_success g x s T [u] ['#'] p i hh
  have hword := literal_success g x s T [] u i j hv
  exact ⟨j,by simpa only [hword,List.singleton_append,List.cons_append,List.nil_append] using hhash,hb⟩

/-- Every successful real checker run supplies its own exact repetition
count and marker endpoint, even on arbitrary malformed input. No uniform
input form, nonempty held word, or SoundTV premise is supplied. -/
theorem check_inverse (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u : List Char) (p q : Nat)
    (h : evV g x s T [u] checkBody p=some (some q)) :
    ∃ n rest, sfx x p=power ('#'::u) (n+1)++'!'::rest ∧ sfx x q='!'::rest := by
  let f := fun j => evV g x s T [u]
    (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))) j
  obtain ⟨j,hs,ht⟩ := seq_success g x s T [u] _ _ p q h
  change evStar f p=some (some j) at hs
  obtain ⟨n,trace,hstop⟩ := InlineRepeat.star_trace f p j hs
  have hprefix : sfx x p=power ('#'::u) n++sfx x j := by
    clear h ht hs hstop
    induction trace with
    | zero p => simp [power]
    | @succ p z n j hv hz tail ih =>
      obtain ⟨v,hv',hl⟩ := word_success g x s T u _ p z hv
      obtain ⟨he,_⟩ := look_success g x s T [u] _ v z hl
      rw [←he] at hv'
      rw [hv',ih]
      simp [power,List.replicate_succ,List.append_assoc]
  obtain ⟨v,hv,hlook⟩ := word_success g x s T u _ j q ht
  obtain ⟨he,z,hbang⟩ := look_success g x s T [u] _ v q hlook
  have hmarker := literal_success g x s T [u] ['!'] v z hbang
  refine ⟨n,sfx x z,?_,?_⟩
  · rw [hprefix,hv,←he]
    rw [←he] at hmarker
    rw [hmarker,LastCodewordCandidate.power_succ_right]
    simp [List.append_assoc]
  · rw [←he] at hmarker
    exact hmarker

/-- The greedy first argument itself supplies its a-run length and value.
No runtime word length is assumed by the caller. -/
theorem run_shape (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E runA p=some (some q)) :
    ∃ k, pre x p q=firstPiece k ∧ sfx x p=firstPiece k++sfx x q := by
  let before := (sfx x p).takeWhile (NestedScannerArguments.accepts ['a'])
  let after := (sfx x p).dropWhile (NestedScannerArguments.accepts ['a'])
  have hs : sfx x p=before++after := List.takeWhile_append_dropWhile.symm
  have hq : after.length=q := by
    rw [runA,NestedScannerArguments.scan_eval g x s T E ['a'] p hp] at h
    exact Option.some.inj (Option.some.inj h)
  have ha : sfx x q=after := by
    rw [←hq]
    exact sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨before,hs⟩).choose_spec
  have hb : before=firstPiece before.length := by
    apply List.eq_replicate_of_mem
    intro c hc
    have hh := List.all_eq_true.mp
      (List.all_takeWhile (p := NestedScannerArguments.accepts ['a']) (l := sfx x p)) c hc
    simp only [NestedScannerArguments.accepts,Shallot.beqChar,Bool.or_false,beq_iff_eq] at hh
    exact Char.toNat_inj.mp hh.symm
  refine ⟨before.length,?_,?_⟩
  · have hc := pre_eq (sfx_is_suffix x p) hs
    rw [length_sfx x hp,hq] at hc
    exact hc.trans hb
  · rw [ha,←hb]
    exact hs

/-- Successful physical preflight calls on arbitrary original inputs are
classified by their actual first capture and checker trace. The copy after
! is not constrained here; the actual user body must still check it. -/
theorem preflight_shape (x : List Char) (m p q : Nat) (E : List (List Char))
    (hp : p≤x.length)
    (h : evV target x .callByValueSeq (tblV target x .callByValueSeq m) E
      (.call 0 [runA]) p=some (some q)) :
    ∃ k n rest, sfx x p=firstPiece k++(power ('#'::firstPiece k) (n+1)++'!'::rest) ∧
      sfx x q='!'::rest := by
  have rule : ruleAtM target.rules 0=some ⟨1,checkBody⟩ := rfl
  rw [evV_call_seq rule rfl] at h
  cases hv : evV target x .callByValueSeq (tblV target x .callByValueSeq m) E runA p with
  | none => simp only [evSeqArgs,hv] at h; cases h
  | some r => cases r with
    | none => simp only [evSeqArgs,hv] at h; cases h
    | some j =>
      simp only [evSeqArgs,hv] at h
      have hj := evV_ok (tblV_ok target x .callByValueSeq m) runA p hp j hv
      obtain ⟨k,hcap,hs⟩ := run_shape target x .callByValueSeq _ E p j hp hv
      rw [hcap] at h
      cases m with
      | zero => simp [tblV,valAt] at h
      | succ m =>
        rw [valAt_tblV_succ rule _ hj] at h
        obtain ⟨n,rest,hn,he⟩ := check_inverse target x .callByValueSeq _ (firstPiece k) j q h
        exact ⟨k,n,rest,by rw [hs,hn],he⟩

private theorem eof_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p q : Nat)
    (h : evV g x s T E eof p=some (some q)) : sfx x p=[] := by
  cases hs : sfx x p with
  | nil => rfl
  | cons c rest => simp [eof,evV,hs] at h

/-- A successful binary user body validates the entire restored capture,
including the second piece and the end of the original input. -/
theorem binary_body_inverse (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u v : List Char) (p q : Nat)
    (h : evV g x s T [u,v] target.rules[1].body p=some (some q)) :
    sfx x p='#'::(u++'!'::(u++v)) := by
  obtain ⟨j,hhash,h⟩ := seq_success g x s T [u,v] _ _ p q h
  obtain ⟨l,hu,h⟩ := seq_success g x s T [u,v] _ _ j q h
  obtain ⟨m,hbang,h⟩ := seq_success g x s T [u,v] _ _ l q h
  obtain ⟨o,hu',h⟩ := seq_success g x s T [u,v] _ _ m q h
  obtain ⟨t,hv,h⟩ := seq_success g x s T [u,v] _ _ o q h
  have hh := literal_success g x s T [u,v] ['#'] p j hhash
  have h1 := literal_success g x s T [] u j l hu
  have hb := literal_success g x s T [u,v] ['!'] l m hbang
  have h2 := literal_success g x s T [] u m o hu'
  have h3 := literal_success g x s T [] v o t hv
  have he := eof_success g x s T [u,v] t q h
  simpa [h1,hb,h2,h3,he] using hh

theorem unary_body_inverse (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u : List Char) (p q : Nat)
    (h : evV g x s T [u] target.rules[2].body p=some (some q)) :
    sfx x p='#'::(u++'!'::u) := by
  obtain ⟨j,hhash,h⟩ := seq_success g x s T [u] _ _ p q h
  obtain ⟨l,hu,h⟩ := seq_success g x s T [u] _ _ j q h
  obtain ⟨m,hbang,h⟩ := seq_success g x s T [u] _ _ l q h
  obtain ⟨t,hu',h⟩ := seq_success g x s T [u] _ _ m q h
  have hh := literal_success g x s T [u] ['#'] p j hhash
  have h1 := literal_success g x s T [] u j l hu
  have hb := literal_success g x s T [u] ['!'] l m hbang
  have h2 := literal_success g x s T [] u m t hu'
  have he := eof_success g x s T [u] t q h
  simpa [h1,hb,h2,he] using hh

/-- Normalize the successful preflight's rotated-prefix description back
to the original head-plus-capture order, with an arbitrary remaining copy. -/
theorem preflight_original_shape (x : List Char) (m p q : Nat) (E : List (List Char))
    (hp : p≤x.length)
    (h : evV target x .callByValueSeq (tblV target x .callByValueSeq m) E
      (.call 0 [runA]) p=some (some q)) :
    ∃ k n rest, sfx x p=RuntimeShiftFilter.block k++captured k n++'!'::rest ∧ sfx x q='!'::rest := by
  obtain ⟨k,n,rest,hs,he⟩ := preflight_shape x m p q E hp h
  have heq : RuntimeShiftFilter.block k++captured k n=
      firstPiece k++power ('#'::firstPiece k) (n+1) := by
    have hi := PartialCodewordExecution.input_rotated k n
    simp only [input,List.append_assoc,List.singleton_append] at hi
    have hh : (RuntimeShiftFilter.block k++captured k n)++('!'::captured k n)=
        (firstPiece k++power ('#'::firstPiece k) (n+1))++('!'::captured k n) := by
      simpa only [List.append_assoc] using hi
    exact (List.append_left_inj _).mp hh
  refine ⟨k,n,rest,?_,he⟩
  rw [hs,heq,List.append_assoc]

theorem unary_call_inverse (x : List Char) (m q : Nat) (E : List (List Char))
    (h : evV target x .callByValueSeq (tblV target x .callByValueSeq (m+1)) E
      (.call 2 [runA]) x.length=some (some q)) : ∃ k, x=input k 0 := by
  have rule : ruleAtM target.rules 2=some ⟨1,target.rules[2].body⟩ := rfl
  rw [evV_call_seq rule rfl] at h
  cases hv : evV target x .callByValueSeq (tblV target x .callByValueSeq (m+1)) E runA x.length with
  | none => simp only [evSeqArgs,hv] at h; cases h
  | some r => cases r with
    | none => simp only [evSeqArgs,hv] at h; cases h
    | some j =>
      simp only [evSeqArgs,hv] at h
      have hj := evV_ok (tblV_ok target x .callByValueSeq (m+1)) runA _ (Nat.le_refl _) j hv
      obtain ⟨k,hcap,hs⟩ := run_shape target x .callByValueSeq _ E _ j (Nat.le_refl _) hv
      rw [hcap,valAt_tblV_succ rule _ hj] at h
      have hb := unary_body_inverse target x .callByValueSeq _ (firstPiece k) j q h
      refine ⟨k,?_⟩
      rw [sfx_self,hb] at hs
      simpa [input,captured,block,power,firstPiece,List.append_assoc] using hs

private theorem short_argument (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (k p : Nat) (rest : List Char) (hp : p≤x.length)
    (hs : sfx x p=firstPiece k++'!'::rest) :
    evV g x s T E argument p=some (some ('!'::rest).length) := by
  have hr := run_at g x s T E k p '!' rest (by decide) hp hs
  have hbang : sfx x ('!'::rest).length='!'::rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨firstPiece k,hs⟩).choose_spec
  have hscan : evV g x s T E scanner p=some none := by
    rw [show scanner=.seq runA (.lit ['#']) from rfl,evV_seq_ok hr]
    simp only [evV,hbang]
    rfl
  have hstep : evV g x s T E (.seq scanner (look scanner)) p=some none := evV_seq_fail hscan
  have hstar : evV g x s T E (.star (.seq scanner (look scanner))) p=some (some p) := evStar_fail hstep
  rw [argument,evV_seq_ok hstar]
  exact hr

/-- The binary branch cannot accept a preflight input with zero complete
captured words: its second argument would pass the required # endpoint. -/
theorem binary_zero_impossible (x : List Char) (m q k : Nat) (rest : List Char)
    (E : List (List Char)) (hx : x=block k++captured k 0++'!'::rest) :
    evV target x .callByValueSeq (tblV target x .callByValueSeq (m+1)) E
      (.call 1 [runA,restArgument]) x.length≠some (some q) := by
  intro h
  let T := tblV target x .callByValueSeq (m+1)
  let r := firstPiece k++'!'::rest
  have hs : x=firstPiece k++('#'::r) := by
    simpa [captured,power,block,firstPiece,r,List.append_assoc] using hx
  have hj : ('#'::r).length≤x.length := by
    have hh := congrArg List.length hs; simp only [List.length_append] at hh; omega
  have hrb : r.length≤x.length := by simp only [List.length_cons] at hj; omega
  have hrun := run_at target x .callByValueSeq T E k x.length '#' r (by decide)
    (Nat.le_refl _) (by rw [sfx_self]; exact hs)
  have hsr : sfx x ('#'::r).length='#'::r := sfx_suffix hs
  have hhash := LastCodewordCandidate.literal_at target x .callByValueSeq T E ['#'] r _ hsr
  have hsa : sfx x r.length=r :=
    sfx_suffix (show x=(firstPiece k++['#'])++r by simpa [List.append_assoc] using hs)
  have ha := short_argument target x .callByValueSeq T E k r.length rest hrb hsa
  have hsecond : evV target x .callByValueSeq T E restArgument ('#'::r).length=
      some (some ('!'::rest).length) := by rw [restArgument,evV_seq_ok hhash]; exact ha
  have hfinal : ('!'::rest).length≤x.length := by
    have hh := congrArg List.length hs
    simp only [List.length_append,List.length_cons,r] at hh
    simp only [List.length_cons] at hh ⊢
    omega
  have hbang : sfx x ('!'::rest).length='!'::rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x r.length) ⟨firstPiece k,hsa⟩).choose_spec
  have rule : ruleAtM target.rules 1=some ⟨2,target.rules[1].body⟩ := rfl
  change evV target x .callByValueSeq T E (.call 1 [runA,restArgument]) x.length=_ at h
  rw [evV_call_seq rule rfl] at h
  simp only [evSeqArgs,hrun,hsecond] at h
  rw [valAt_tblV_succ rule _ hfinal] at h
  obtain ⟨j,hhash',_⟩ := seq_success target x .callByValueSeq _ _ _ _ _ q h
  simp only [evV,hbang] at hhash'
  cases hhash'

/-- Every successful binary call on a real successful-preflight prefix
also verifies the remaining copy, so the entire input has the source form. -/
theorem binary_call_inverse (x : List Char) (m q k n : Nat) (rest : List Char)
    (E : List (List Char)) (hx : x=block k++captured k (n+1)++'!'::rest)
    (h : evV target x .callByValueSeq (tblV target x .callByValueSeq (m+1)) E
      (.call 1 [runA,restArgument]) x.length=some (some q)) : x=input k (n+1) := by
  have hx' : x=power (block k) (n+2)++firstPiece k++'!'::rest := by
    simpa [captured,power,List.replicate_succ,firstPiece,List.append_assoc] using hx
  have hargs := PartialCodewordExecution.split_arguments target x .callByValueSeq
    (tblV target x .callByValueSeq (m+1)) E k n x.length rest (Nat.le_refl _) (by rw [sfx_self]; exact hx')
  have hxq : x=captured k (n+1)++('#'::(firstPiece k++'!'::rest)) :=
    hx'.trans (PartialCodewordExecution.word_boundary k (n+1) rest)
  have hq : ('#'::(firstPiece k++'!'::rest)).length≤x.length := by
    have hh := congrArg List.length hxq; simp only [List.length_append] at hh; omega
  have rule : ruleAtM target.rules 1=some ⟨2,target.rules[1].body⟩ := rfl
  rw [evV_call_seq rule rfl,hargs] at h
  simp only [] at h
  rw [valAt_tblV_succ rule _ hq] at h
  have hb := binary_body_inverse target x .callByValueSeq _ (firstPiece k) (secondPiece k n) _ q h
  rw [PartialCodewordExecution.pieces_join] at hb
  have heq := (sfx_suffix hxq).symm.trans hb
  have he : rest=captured k (n+1) := by
    have h1 := (List.cons.inj heq).2
    have h2 := (List.append_right_inj (firstPiece k)).mp h1
    exact (List.cons.inj h2).2
  rw [he] at hx
  simpa [input,List.append_assoc] using hx

/-- All successful ordinary Seq executions, at any physical stage, are
classified on arbitrary original input. The result excludes false positives
without assuming a well-formed prefix or a correct trailing copy. -/
theorem target_inverse (x : List Char) (m q : Nat)
    (h : evV target x .callByValueSeq (tblV target x .callByValueSeq m) []
      targetRoot x.length=some (some q)) : ∃ k n, x=input k n := by
  obtain ⟨p,hlook,hbranches⟩ := seq_success target x .callByValueSeq _ [] _ _ x.length q h
  obtain ⟨he,j,hpre⟩ := look_success target x .callByValueSeq _ [] _ x.length p hlook
  subst p
  obtain ⟨k,n,rest,hx,_⟩ := preflight_original_shape x m x.length j [] (Nat.le_refl _) hpre
  rw [sfx_self] at hx
  cases m with
  | zero =>
    have rule : ruleAtM target.rules 0=some ⟨1,checkBody⟩ := rfl
    rw [evV_call_seq rule rfl] at hpre
    cases ha : evSeqArgs target x .callByValueSeq (tblV target x .callByValueSeq 0) [] [runA] x.length with
    | none => simp only [ha] at hpre; cases hpre
    | some r =>
      simp only [ha] at hpre
      cases r with
      | none => cases hpre
      | some v => simp [tblV,valAt] at hpre
  | succ m =>
    cases hl : evV target x .callByValueSeq (tblV target x .callByValueSeq (m+1)) []
        (.seq longTest (.call 1 [runA,restArgument])) x.length with
    | none => rw [evV_alt_none hl] at hbranches; cases hbranches
    | some r => cases r with
      | none =>
        rw [evV_alt_fail hl] at hbranches
        obtain ⟨p,hneg,hcall⟩ := seq_success target x .callByValueSeq _ [] _ _ x.length q hbranches
        have hpos : p=x.length := by
          cases ht : evV target x .callByValueSeq (tblV target x .callByValueSeq (m+1)) [] longTest x.length with
          | none => simp only [evV,ht] at hneg; cases hneg
          | some r => cases r with
            | none =>
              rw [evV_not_fail ht] at hneg
              exact (Option.some.inj (Option.some.inj hneg)).symm
            | some v => rw [evV_not_ok ht] at hneg; cases hneg
        subst p
        obtain ⟨k,hk⟩ := unary_call_inverse x m q [] hcall
        exact ⟨k,0,hk⟩
      | some z =>
        obtain ⟨p,hguard,hcall⟩ := seq_success target x .callByValueSeq _ [] _ _ x.length z hl
        obtain ⟨he,_⟩ := look_success target x .callByValueSeq _ [] _ x.length p hguard
        subst p
        cases n with
        | zero => exact False.elim (binary_zero_impossible x m z k rest [] hx hcall)
        | succ n => exact ⟨k,n+1,binary_call_inverse x m z k n rest [] hx hcall⟩

/-- Exact recognition by the single fixed Seq candidate on all original
strings. The original Par converse is established below independently. -/
theorem target_language (x : List Char) :
    SObs target .callByValueSeq targetRoot x (some []) ↔ ∃ k n, x=input k n := by
  constructor
  · rintro ⟨o,hd,ho⟩
    cases o with
    | fail => simp [MOutcome.restOf] at ho
    | ok tree rest =>
      have hr : rest=[] := Option.some.inj ho
      subst rest
      obtain ⟨m,hm⟩ := derivesV_ev (x := x) firstOrder.2.1 (by decide) hd firstOrder.2.2.2 ⟨[],by simp⟩
      exact target_inverse x m 0 hm
  · rintro ⟨k,n,rfl⟩
    exact (PartialCodewordExecution.family_observations k n).2

theorem target_to_source (x : List Char)
    (h : SObs target .callByValueSeq targetRoot x (some [])) :
    SObs source .callByValuePar sourceRoot x (some []) := by
  obtain ⟨k,n,rfl⟩ := (target_language x).mp h
  exact (PartialCodewordExecution.family_observations k n).1

/-- The actual last greedy a-run cannot stop immediately before another a.
This is independent of all rule tables and applies to every successful
argument execution, not just to the intended positive family. -/
theorem argument_stop (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p q : Nat) (hp : p≤x.length) (hT : OkTV x.length T)
    (h : evV g x s T E argument p=some (some q)) :
    (sfx x q).head?≠some 'a' := by
  obtain ⟨j,hstar,hrun⟩ := seq_success g x s T E _ _ p q h
  have hj := evV_ok hT _ p hp j hstar
  rw [runA,NestedScannerArguments.scan_eval g x s T E ['a'] j hj] at hrun
  have hq : ((sfx x j).dropWhile (NestedScannerArguments.accepts ['a'])).length=q :=
    Option.some.inj (Option.some.inj hrun)
  have hs : sfx x q=(sfx x j).dropWhile (NestedScannerArguments.accepts ['a']) := by
    rw [←hq]
    exact sfx_suffix (suffix_trans (sfx_is_suffix x j)
      ⟨(sfx x j).takeWhile (NestedScannerArguments.accepts ['a']),List.takeWhile_append_dropWhile.symm⟩).choose_spec
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

private theorem copies_power (u : List Char) (n : Nat) : BlockCapture.copies u n=power u n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BlockCapture.copies,power,List.replicate_succ,ih]

/-- Periodic overlap plus the actual greedy stopping condition forces the
complete final a-run. The captured word is derived from the original
input equation; no number of complete words or final phase is assumed. -/
theorem stopped_overlap (k : Nat) (w suffix : List Char)
    (hx : (block k++w)++('!'::w)=w++suffix)
    (hstop : suffix.head?≠some 'a') : ∃ n, w=captured k n := by
  have hp : w.IsPrefix (block k++w) :=
    List.prefix_of_prefix_length_le ⟨suffix,hx.symm⟩ ⟨'!'::w,rfl⟩ (by simp)
  obtain ⟨n,left,right,hr,hw,hlen⟩ := OverlapNecessity.prefix_periodic (block k) (by simp [block]) w hp
  have hle : left.length≤k := by simp only [block,List.length_append,List.length_replicate,List.length_singleton] at hlen; omega
  have hleft : left=List.replicate left.length 'a' := by
    have hh := congrArg (List.take left.length) hr
    rw [List.take_append_length,block,List.take_append_of_le_length (by simpa using hle)] at hh
    simpa only [List.take_replicate,Nat.min_eq_left hle] using hh.symm
  have hright : right=List.replicate (k-left.length) 'a'++['#'] := by
    have hh := congrArg (List.drop left.length) hr
    rw [List.drop_append_length,block,List.drop_append_of_le_length (by simpa using hle)] at hh
    simpa only [List.drop_replicate] using hh.symm
  have rotate : block k++w=w++(right++left) := by
    rw [hw,hr]
    exact BlockCapture.rotate left right n
  rw [rotate,List.append_assoc] at hx
  have hrem : (right++left)++('!'::w)=suffix := (List.append_right_inj w).mp hx
  have he : left.length=k := by
    by_cases he : left.length=k
    · exact he
    · exfalso
      have hd : 0<k-left.length := by omega
      cases hh : k-left.length with
      | zero => omega
      | succ t =>
        apply hstop
        rw [←hrem,hright,hh]
        simp [List.replicate_succ]
  refine ⟨n,?_⟩
  rw [hw,copies_power,hleft,he]
  rfl

theorem scanner_shape (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E scanner p=some (some q)) :
    ∃ k, sfx x p=block k++sfx x q := by
  obtain ⟨j,hr,hh⟩ := seq_success g x s T E _ _ p q h
  obtain ⟨k,_,hk⟩ := run_shape g x s T E p j hp hr
  have hhash := literal_success g x s T E ['#'] j q hh
  refine ⟨k,?_⟩
  simpa [hhash,block,firstPiece,List.append_assoc] using hk

theorem source_body_inverse (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w : List Char) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T [w] source.rules[0].body p=some (some q)) :
    ∃ k, sfx x p=(block k++w)++('!'::w) := by
  obtain ⟨j,ha,h⟩ := seq_success g x s T [w] _ _ p q h
  obtain ⟨l,hw,h⟩ := seq_success g x s T [w] _ _ j q h
  obtain ⟨m,hb,h⟩ := seq_success g x s T [w] _ _ l q h
  obtain ⟨t,hw',h⟩ := seq_success g x s T [w] _ _ m q h
  obtain ⟨k,hk⟩ := scanner_shape g x s T [w] p j hp ha
  have h1 := literal_success g x s T [] w j l hw
  have hb' := literal_success g x s T [w] ['!'] l m hb
  have h2 := literal_success g x s T [] w m t hw'
  have he := eof_success g x s T [w] t q h
  exact ⟨k,by simpa [h1,hb',h2,he,List.append_assoc] using hk⟩

theorem source_inverse (x : List Char) (m q : Nat)
    (h : evV source x .callByValuePar (tblV source x .callByValuePar m) []
      sourceRoot x.length=some (some q)) : ∃ k n, x=input k n := by
  have rule : ruleAtM source.rules 0=some ⟨1,source.rules[0].body⟩ := rfl
  rw [sourceRoot,evV_call_par rule rfl (by decide)] at h
  cases ha : evV source x .callByValuePar (tblV source x .callByValuePar m) [] argument x.length with
  | none => simp only [evParArgs,ha] at h; cases h
  | some r => cases r with
    | none => simp only [evParArgs,ha] at h; cases h
    | some j =>
      simp only [evParArgs,ha] at h
      have hstop := argument_stop source x .callByValuePar _ [] x.length j
        (Nat.le_refl _) (tblV_ok source x .callByValuePar m) ha
      have hf : argument.FirstOrder := by
        simp [argument,runA,look,RuntimeShiftFilter.scanner,NestedScannerArguments.scan,
          NestedScannerArguments.choice,MExp.failAlways,MExp.FirstOrder]
      have hprefix := (ReplayFusion.success_prefix
        (tblV_sound firstOrder.1 (by decide) m) [] argument hf x.length j (Nat.le_refl _) ha).2
      rw [sfx_self] at hprefix
      cases m with
      | zero => simp [tblV,valAt] at h
      | succ m =>
        rw [valAt_tblV_succ rule _ (Nat.le_refl _)] at h
        obtain ⟨k,hk⟩ := source_body_inverse source x .callByValuePar _ _ x.length q (Nat.le_refl _) h
        rw [sfx_self] at hk
        obtain ⟨n,hn⟩ := stopped_overlap k _ _ (hk.symm.trans hprefix) hstop
        exact ⟨k,n,by simpa [input,hn] using hk⟩

theorem source_language (x : List Char) :
    SObs source .callByValuePar sourceRoot x (some []) ↔ ∃ k n, x=input k n := by
  constructor
  · rintro ⟨o,hd,ho⟩
    cases o with
    | fail => simp [MOutcome.restOf] at ho
    | ok tree rest =>
      have hr : rest=[] := Option.some.inj ho
      subst rest
      obtain ⟨m,hm⟩ := derivesV_ev (x := x) firstOrder.1 (by decide) hd firstOrder.2.2.1 ⟨[],by simp⟩
      exact source_inverse x m 0 hm
  · rintro ⟨k,n,rfl⟩
    exact (PartialCodewordExecution.family_observations k n).1

/-- Both fixed grammars recognize exactly the same original strings.
This concrete equality does not claim a general inverse compiler. -/
theorem language_eq (x : List Char) :
    SObs source .callByValuePar sourceRoot x (some []) ↔
      SObs target .callByValueSeq targetRoot x (some []) := by
  rw [source_language,target_language]

end Shallot.MacroPeg.CBV.PartialCodewordClassification
