import MacroPeg.CBV.LastCodewordRotation
import MacroPeg.CBV.CodewordReplay
import MacroPeg.CBV.RuntimeShiftFilter
import MacroPeg.CBV.PrefixCodeCapture

/-! A fixed candidate keeps the whole last-preserving capture. Its header
length and capture's codeword count are both selected by the input. Positive
families below are extended to all inputs in LastCodewordExamples. -/
namespace Shallot.MacroPeg.CBV.LastCodewordCandidate
open RuntimeShiftFilter (block scanner)
open CodewordReplay (power)
open ClockFreezing (Table)

def captured : MExp := LastCodewordRotation.argument scanner
def tail : MExp := .seq (.lit ['!']) (.param 0)
def verifier : MExp := .seq (.star (.seq (.andP scanner) (.param 0))) (.notP scanner)
def source : MGrammar := ⟨[⟨1,.seq scanner (.seq (.param 0) tail)⟩]⟩
def target : MGrammar := ⟨[⟨1,.seq scanner tail⟩,⟨1,verifier⟩]⟩
def sourceEntry : MExp := .call 0 [captured]
def targetEntry : MExp :=
  .seq (.andP captured) (.seq (.andP (.call 1 [scanner])) (.call 0 [captured]))

theorem power_succ_right (u : List Char) (n : Nat) : power u (n+1)=power u n++u := by
  induction n with
  | zero => simp [power,List.replicate_succ]
  | succ n ih => simpa [power,List.replicate_succ,List.append_assoc] using congrArg (List.append u) ih

/-- Uniform block behavior generates actual strict finite traces; neither
block length nor iteration count needs a fixed bound. -/
theorem constant_trace (x u : List Char) (hu : u≠[]) (f : Nat → Res)
    (hf : ∀ p rest, p≤x.length → sfx x p=u++rest → f p=some (some rest.length)) :
    ∀ n p rest, p≤x.length → sfx x p=power u n++rest → InlineRepeat.Trace f p n rest.length := by
  intro n
  induction n with
  | zero =>
    intro p rest hp hs
    have he : p=rest.length := by simpa [power,length_sfx x hp] using congrArg List.length hs
    subst p
    exact .zero _
  | succ n ih =>
    intro p rest hp hs
    have hs' : sfx x p=u++(power u n++rest) := by simpa [power,List.replicate_succ,List.append_assoc] using hs
    let rem := power u n++rest
    have hbound : rem.length<p := by
      have hh := congrArg List.length hs'
      rw [length_sfx x hp,List.length_append] at hh
      have hpos := List.length_pos_iff.mpr hu
      change (power u n++rest).length<p
      omega
    have hrest : sfx x rem.length=rem :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨u,hs'⟩).choose_spec
    exact .succ (hf p rem hp hs') hbound (ih rem.length rest (by omega) hrest)

theorem scanner_stop (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p : Nat) (rest : List Char) (hp : p≤x.length)
    (hs : sfx x p='!'::rest) : evV g x s T E scanner p=some none := by
  have hx : ∃ pre, x=pre++('!'::rest) := (sfx_is_suffix x p).imp (fun pre h => h.trans (by rw [hs]))
  rw [RuntimeShiftFilter.scanner,evV_seq_ok (NestedScannerArguments.scan_eval g x s T E ['a'] p hp)]
  simp only [hs,List.dropWhile_cons,NestedScannerArguments.accepts,Shallot.beqChar]
  have hsp : sfx x (rest.length+1)='!'::rest := by simpa using sfx_suffix hx.choose_spec
  simp [evV,hsp,Shallot.stripPrefix?,Shallot.beqChar]

theorem literal_at (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (w rest : List Char) (p : Nat) (hs : sfx x p=w++rest) :
    evV g x s T E (.lit w) p=some (some rest.length) := by
  simp only [evV,hs]
  rw [(CBVtoCBN.stripPrefix_exact _ _ _).mpr rfl]

/-- The ordinary closed argument captures n runtime blocks while leaving
one more block before the delimiter, for every n including zero. -/
theorem capture_at (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (k n p : Nat) (rest : List Char) (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+1)++('!'::rest)) :
    evV g x s T E captured p=some (some (block k++('!'::rest)).length) := by
  let A := fun q => evV g x s T E scanner q
  have hblock : block k≠[] := by simp [RuntimeShiftFilter.block]
  have hstep : ∀ j r, j≤x.length → sfx x j=block k++r → A j=some (some r.length) :=
    fun j r hj hr => PrefixCodeCapture.scanner_at g x s T E j k r hj hr
  have ht := constant_trace x (block k) hblock A hstep (n+1) p ('!'::rest) hp hs
  have hend : A ('!'::rest).length=some none := by
    apply scanner_stop g x s T E _ rest
    · have hh := InlineRepeat.trace_le ht; omega
    · exact sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨power (block k) (n+1),hs⟩).choose_spec
  obtain ⟨q,hq,hAq,hstar⟩ := LastCodewordRotation.last_trace A n p _ ht hend
  have hs' : sfx x p=power (block k) n++(block k++('!'::rest)) := by
    rw [hs,power_succ_right,List.append_assoc]
  have ht' := constant_trace x (block k) hblock A hstep n p (block k++('!'::rest)) hp hs'
  have he : q=(block k++('!'::rest)).length := by
    have hh := (InlineRepeat.trace_steps (LastCodewordRotation.step_trace hq)).symm.trans (InlineRepeat.trace_steps ht')
    simpa using hh
  rw [captured,LastCodewordRotation.argument_eval]
  exact he ▸ hstar


theorem verifier_at (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (k n p : Nat) (rest : List Char) (hp : p≤x.length)
    (hs : sfx x p=power (block k) n++('!'::rest)) :
    evV g x s T [block k] verifier p=some (some ('!'::rest).length) := by
  let f := fun q => evV g x s T [block k] (.seq (.andP scanner) (.param 0)) q
  have hblock : block k≠[] := by simp [RuntimeShiftFilter.block]
  have hstep : ∀ j r, j≤x.length → sfx x j=block k++r → f j=some (some r.length) := by
    intro j r hj hr
    have ha := PrefixCodeCapture.scanner_at g x s T [block k] j k r hj hr
    have hpeek : evV g x s T [block k] (.andP scanner) j=some (some j) := by
      rw [CallLookahead.evV_peek,ha]; rfl
    rw [show f j=evV g x s T [block k] (.seq (.andP scanner) (.param 0)) j from rfl,evV_seq_ok hpeek]
    exact literal_at g x s T [] (block k) r j hr
  have ht := constant_trace x (block k) hblock f hstep n p ('!'::rest) hp hs
  have hb : ('!'::rest).length≤x.length := by have := InlineRepeat.trace_le ht; omega
  have hrest : sfx x ('!'::rest).length='!'::rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨power (block k) n,hs⟩).choose_spec
  have hstop := scanner_stop g x s T [block k] _ rest hb hrest
  have hf : f ('!'::rest).length=some none := by
    change (match evV g x s T [block k] (.andP scanner) ('!'::rest).length with
      | some (some j) => evV g x s T [block k] (.param 0) j | other => other)=_
    rw [CallLookahead.evV_peek,hstop]; rfl
  rw [verifier,evV_seq_ok (show evV g x s T [block k] (.star (.seq (.andP scanner) (.param 0))) p=some (some ('!'::rest).length) from
    InlineRepeat.trace_star ht hf)]
  change (match evV g x s T [block k] scanner ('!'::rest).length with
    | some (some _) => some none | some none => some (some ('!'::rest).length) | none => none)=_
  rw [hstop]

def input (k n : Nat) : List Char := power (block k) (n+1)++('!'::power (block k) n)

theorem captured_value (k n : Nat) :
    pre (input k n) (input k n).length (block k++('!'::power (block k) n)).length=power (block k) n := by
  have hh : input k n=power (block k) n++(block k++('!'::power (block k) n)) := by
    simp [input,power_succ_right,List.append_assoc]
  have hp := pre_eq (show ∃ before, input k n=before++input k n from ⟨[],rfl⟩) hh
  simpa using hp

/-- The same whole capture is retained after source shifted replay or
Seq last-header consumption, for every runtime length and word count. -/
theorem body_at (g : MGrammar) (T : Table) (s : Strategy) (k n : Nat) :
    evV g (input k n) s T [power (block k) n]
      (.seq scanner (.seq (.param 0) tail)) (input k n).length=some (some 0) ∧
    evV g (input k n) s T [power (block k) n]
      (.seq scanner tail) (block k++('!'::power (block k) n)).length=some (some 0) := by
  let u := block k
  let w := power u n
  let rest := '!'::w
  let x := input k n
  have hxs : x=u++(w++rest) := by simp [x,input,w,rest,u,power,List.replicate_succ,List.append_assoc]
  have hxlast : x=w++(u++rest) := by simp [x,input,w,rest,u,power_succ_right,List.append_assoc]
  have hsfirst : sfx x (w++rest).length=w++rest := sfx_suffix hxs
  have hslast : sfx x (u++rest).length=u++rest := sfx_suffix hxlast
  have hsrest : sfx x rest.length=rest := sfx_suffix (show x=(u++w)++rest by rw [hxs,List.append_assoc])
  have hsw : sfx x w.length=w := sfx_suffix (show x=((u++w)++['!'])++w by simp [hxs,rest,List.append_assoc])
  have h1 := PrefixCodeCapture.scanner_at g x s T [w] x.length k (w++rest) (Nat.le_refl _) (by rw [sfx_self]; exact hxs)
  have h2 := PrefixCodeCapture.scanner_at g x s T [w] (u++rest).length k rest
    (by have := congrArg List.length hxlast; simp only [List.length_append] at this ⊢; omega) hslast
  have hparam : evV g x s T [w] (.param 0) (w++rest).length=some (some rest.length) :=
    literal_at g x s T [] w rest _ hsfirst
  have hbang := literal_at g x s T [w] ['!'] w rest.length hsrest
  have hend : evV g x s T [w] (.param 0) w.length=some (some 0) :=
    literal_at g x s T [] w [] _ (by simpa using hsw)
  constructor
  · rw [evV_seq_ok h1,evV_seq_ok hparam,tail,evV_seq_ok hbang]
    exact hend
  · rw [evV_seq_ok h2,tail,evV_seq_ok hbang]
    exact hend

theorem source_execution (k n : Nat) :
    evV source (input k n) .callByValuePar (tblV source (input k n) .callByValuePar 1) []
      sourceEntry (input k n).length=some (some 0) := by
  have hr : ruleAtM source.rules 0=some ⟨1,.seq scanner (.seq (.param 0) tail)⟩ := rfl
  rw [sourceEntry,evV_call_par hr rfl (by decide)]
  simp only [evParArgs,capture_at source (input k n) .callByValuePar _ [] k n _ _ (Nat.le_refl _) (by rw [sfx_self]; rfl)]
  rw [captured_value,valAt_tblV_succ hr _ (Nat.le_refl _)]
  exact (body_at source _ .callByValuePar k n).1

theorem target_execution (k n : Nat) :
    evV target (input k n) .callByValueSeq (tblV target (input k n) .callByValueSeq 1) []
      targetEntry (input k n).length=some (some 0) := by
  let x := input k n
  let T := tblV target x .callByValueSeq 1
  let u := block k
  let w := power u n
  let rest := '!'::w
  have hb : evV target x .callByValueSeq T [] captured x.length=some (some (u++rest).length) :=
    capture_at target x .callByValueSeq T [] k n _ _ (Nat.le_refl _) (by rw [sfx_self]; rfl)
  have hpre : evV target x .callByValueSeq T [] (.andP captured) x.length=some (some x.length) := by
    rw [CallLookahead.evV_peek,hb]; rfl
  have hv : evV target x .callByValueSeq T [] (.call 1 [scanner]) x.length=some (some rest.length) := by
    have hr : ruleAtM target.rules 1=some ⟨1,verifier⟩ := rfl
    rw [evV_call_seq hr rfl]
    simp only [evSeqArgs]
    have hs : sfx x x.length=u++(w++rest) := by
      rw [sfx_self]
      simp [x,input,w,rest,u,power,List.replicate_succ,List.append_assoc]
    rw [PrefixCodeCapture.scanner_at target x .callByValueSeq T [] x.length k (w++rest) (Nat.le_refl _) hs]
    simp only []
    have hcap : pre x x.length (w++rest).length=u := by
      have hh := pre_eq (sfx_is_suffix x x.length) hs
      simpa [length_sfx x (Nat.le_refl _)] using hh
    rw [hcap,valAt_tblV_succ hr _ (by have := congrArg List.length hs; rw [length_sfx x (Nat.le_refl _),List.length_append] at this; omega)]
    apply verifier_at target x .callByValueSeq _ k n _ w
    · have := congrArg List.length hs; rw [length_sfx x (Nat.le_refl _),List.length_append] at this; omega
    · exact sfx_suffix (by simpa [sfx_self] using hs)
  have hvpre : evV target x .callByValueSeq T [] (.andP (.call 1 [scanner])) x.length=some (some x.length) := by
    rw [CallLookahead.evV_peek,hv]; rfl
  rw [targetEntry,evV_seq_ok hpre,evV_seq_ok hvpre]
  have hr : ruleAtM target.rules 0=some ⟨1,.seq scanner tail⟩ := rfl
  rw [evV_call_seq hr rfl]
  simp only [evSeqArgs,hb]
  rw [captured_value,valAt_tblV_succ hr _ (by
    have hh : x=w++(u++rest) := by simp [x,input,w,u,rest,power_succ_right,List.append_assoc]
    have := congrArg List.length hh; simp only [List.length_append] at this ⊢; omega)]
  exact (body_at target _ .callByValueSeq k n).2


theorem scanner_firstOrder : scanner.FirstOrder := by
  simp [RuntimeShiftFilter.scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
    MExp.FirstOrder,MExp.failAlways]

theorem source_firstOrder : source.FirstOrder := by
  intro r hr
  simp only [source,List.mem_singleton] at hr
  subst r
  exact ⟨scanner_firstOrder,True.intro,True.intro,True.intro⟩

theorem target_firstOrder : target.FirstOrder := by
  intro r hr
  simp only [target,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨scanner_firstOrder,True.intro,True.intro⟩
  · exact ⟨⟨scanner_firstOrder,True.intro⟩,scanner_firstOrder⟩

theorem entries_firstOrder : sourceEntry.FirstOrder ∧ targetEntry.FirstOrder := by
  have hc : captured.FirstOrder := ⟨scanner_firstOrder,scanner_firstOrder⟩
  exact ⟨⟨hc,True.intro⟩,hc,⟨scanner_firstOrder,True.intro⟩,hc,True.intro⟩

/-- One fixed pair of actual grammars accepts this entire family with
unbounded header length and unbounded captured word count. This is a
positive family; LastCodewordExamples.all_inputs covers all other inputs. -/
theorem observations (k n : Nat) :
    SObs source .callByValuePar sourceEntry (input k n) (some []) ∧
    SObs target .callByValueSeq targetEntry (input k n) (some []) := by
  have accept (g : MGrammar) (hg : g.FirstOrder) (s : Strategy) (hs : s≠.callByName)
      (e : MExp) (he : e.FirstOrder)
      (h : evV g (input k n) s (tblV g (input k n) s 1) [] e (input k n).length=some (some 0)) :
      SObs g s e (input k n) (some []) := by
    obtain ⟨o,hd,ho⟩ := evV_derives hg hs he 1 (Nat.le_refl _) h
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  exact ⟨accept source source_firstOrder .callByValuePar (by decide) sourceEntry entries_firstOrder.1 (source_execution k n),
    accept target target_firstOrder .callByValueSeq (by decide) targetEntry entries_firstOrder.2 (target_execution k n)⟩


namespace LateUndefined

def head : MExp := .alt scanner (.star (.lit []))
def arg : MExp := LastCodewordRotation.argument head
def check : MExp := .seq (.star (.seq (.andP head) (.param 0))) (.notP head)
def source : MGrammar := ⟨[⟨1,.seq head (.param 0)⟩]⟩
def target : MGrammar := ⟨[⟨1,head⟩,⟨1,check⟩]⟩
def probe : MExp := .call 1 [head]
def raw : MExp := .seq (.andP probe) (.call 0 [arg])
def guarded : MExp := .seq (.andP arg) raw

theorem argument_guard_required :
    evV source "a#aa#Z".toList .callByValuePar
      (tblV source "a#aa#Z".toList .callByValuePar 1) [] (.call 0 [arg]) 6=none ∧
    evV target "a#aa#Z".toList .callByValueSeq
      (tblV target "a#aa#Z".toList .callByValueSeq 1) [] raw 6=some none ∧
    evV target "a#aa#Z".toList .callByValueSeq
      (tblV target "a#aa#Z".toList .callByValueSeq 1) [] guarded 6=none := by
  decide +kernel

end LateUndefined

end Shallot.MacroPeg.CBV.LastCodewordCandidate
