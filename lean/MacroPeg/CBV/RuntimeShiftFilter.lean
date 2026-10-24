import MacroPeg.CBV.PeriodicCaptureMachine
import MacroPeg.CBV.CaptureOrbit
import MacroPeg.CBV.NestedScannerArguments

/-! A fixed finite capture filter cannot replace the shift-indexed phase
machines when the shift is a runtime-delimited word. This is a limitation
of that compilation method, not a lower bound for CBV-Seq grammars. -/
namespace Shallot.MacroPeg.CBV.RuntimeShiftFilter
open RegularCaptureProduct (Machine run run_append run_bound)

def block (n : Nat) : List Char := List.replicate n 'a'++['#']

def scanner : MExp := .seq (NestedScannerArguments.scan ['a']) (.lit ['#'])

/-- This is the actual consuming source prefix, with an unbounded shift
length selected by the ordinary input, for either evaluation strategy. -/
theorem scanner_eval (g : MGrammar) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (n : Nat) (rest : List Char) :
    evV g (block n++rest) s T E scanner (block n++rest).length=some (some rest.length) := by
  have hd : (block n++rest).dropWhile (NestedScannerArguments.accepts ['a'])='#'::rest := by
    induction n with
    | zero => simp [block,NestedScannerArguments.accepts,Shallot.beqChar]
    | succ n ih => simp [block,List.replicate_succ,NestedScannerArguments.accepts,Shallot.beqChar] at *
  rw [scanner,evV_seq_ok (by
    rw [NestedScannerArguments.scan_eval g (block n++rest) s T E ['a'] _ (Nat.le_refl _),sfx_self,hd])]
  have hs : sfx (block n++rest) ('#'::rest).length='#'::rest := by
    apply sfx_suffix (pre := List.replicate n 'a')
    simp [block,List.append_assoc]
  simp only [evV,hs]
  rfl

/-- The first delimiter identifies the length of the runtime shift. -/
theorem block_prefix (m n : Nat) (rest : List Char) :
    (block m).IsPrefix (block n++rest) ↔ m=n := by
  induction m generalizing n with
  | zero => cases n <;> simp [block,List.replicate_succ]
  | succ m ih =>
    cases n with
    | zero => simp [block,List.replicate_succ]
    | succ n => simpa [block,List.replicate_succ] using ih n

/-- For a capture containing two delimited blocks, overlap with its own
first block forces equality of the two block lengths. -/
theorem overlap_iff (n m : Nat) :
    (block n++block m).IsPrefix (block n++(block n++block m)) ↔ n=m := by
  rw [List.prefix_append_right_inj,block_prefix]
  exact eq_comm

/-- Every correct finite filter would have to distinguish all first-block
lengths before reading the common continuation. -/
theorem distinguish (D : Machine) (accept : Nat → Prop)
    (correct : ∀ n m, accept (run D 0 (block n++block m)) ↔
      (block n++block m).IsPrefix (block n++(block n++block m)))
    (n m : Nat) (same : run D 0 (block n)=run D 0 (block m)) : n=m := by
  have hn := (correct n n).mpr ((overlap_iff n n).mpr rfl)
  have hm : accept (run D 0 (block m++block n)) := by
    simpa only [run_append,←same] using hn
  exact ((overlap_iff m n).mp ((correct m n).mp hm)).symm

/-- No finite machine, with any choice of accepting states, uniformly
recognizes the required overlap condition for these runtime shifts. -/
theorem no_uniform_filter (D : Machine) (valid : D.Valid) (accept : Nat → Prop) :
    ¬(∀ n m, accept (run D 0 (block n++block m)) ↔
      (block n++block m).IsPrefix (block n++(block n++block m))) := by
  intro correct
  obtain ⟨n,m,hnm,_,same⟩ := CaptureOrbit.bounded_collision
    (fun n => run D 0 (block n)) D.width (fun n _ => run_bound valid 0 valid.1 (block n))
  have := distinguish D accept correct n m same
  omega

/-- Each individual shift still has the existing exact phase machine.
The impossibility is uniformity in the unbounded runtime shift. -/
theorem fixed_shift_filter (n m : Nat) :
    run (PeriodicCaptureMachine.machine (block n)) 0 (block n++block m)<(block n).length ↔ n=m := by
  rw [←PeriodicCaptureMachine.prefix_iff_nonsink]
  · exact overlap_iff n m
  · simp [block]

def replayGrammar : MGrammar := ⟨[⟨1,.param 0⟩]⟩
def replayEntry : MExp := .call 0 [scanner]

theorem strip_block (n m : Nat) :
    Shallot.stripPrefix? (block n) (block m)=if n=m then some [] else none := by
  induction n generalizing m with
  | zero => cases m <;> simp [block,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar]
  | succ n ih =>
    cases m with
    | zero => simp [block,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar]
    | succ m => simpa [block,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar] using ih m

/-- Keeping the runtime block itself solves this comparison in Seq. The
same fixed grammar tests equality at every pair of unbounded lengths. -/
theorem seq_compare_blocks (n m : Nat) :
    evV replayGrammar (block n++block m) .callByValueSeq
      (tblV replayGrammar (block n++block m) .callByValueSeq 1) [] replayEntry
      (block n++block m).length=if n=m then some (some 0) else some none := by
  have rule : ruleAtM replayGrammar.rules 0=some ⟨1,.param 0⟩ := rfl
  have cap : pre (block n++block m) (block n++block m).length (block m).length=block n :=
    pre_eq ⟨[],by simp⟩ rfl
  rw [replayEntry,evV_call_seq rule rfl]
  simp only [evSeqArgs,scanner_eval,cap]
  rw [valAt_tblV_succ rule [block n] (by simp)]
  have hs : sfx (block n++block m) (block m).length=block m := sfx_suffix rfl
  simp only [evV,List.getElem?_cons_zero,hs]
  rw [strip_block]
  by_cases h : n=m <;> simp [h]

/-- The physical calculation supplies genuine finite Seq observations,
including finite rejection for every unequal pair. -/
theorem seq_observations (n m : Nat) :
    SObs replayGrammar .callByValueSeq replayEntry (block n++block m)
      (if n=m then some [] else none) := by
  have hf : replayGrammar.FirstOrder := by
    intro r hr
    simp [replayGrammar] at hr
    subst r
    trivial
  have he : replayEntry.FirstOrder := by
    exact ⟨⟨NestedScannerArguments.scan_firstOrder ['a'],True.intro⟩,True.intro⟩
  by_cases h : n=m
  · obtain ⟨o,hd,ho⟩ := evV_derives (s := .callByValueSeq) (x := block n++block m) hf (by decide) he 1 (Nat.le_refl _)
      (by simpa [h] using seq_compare_blocks n m)
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,by simp [h,MOutcome.restOf]⟩
  · obtain ⟨o,hd,ho⟩ := evV_derives (s := .callByValueSeq) (x := block n++block m) hf (by decide) he 1 (Nat.le_refl _)
      (by simpa [h] using seq_compare_blocks n m)
    rw [sfx_self,obsR_fail ho] at hd
    exact ⟨_,hd,by simp [h,MOutcome.restOf]⟩

end Shallot.MacroPeg.CBV.RuntimeShiftFilter
