import MacroPeg.CBV.ControlledPartialCapture
import MacroPeg.CBV.AdjacentCodewordControl

/-! A caller-position filter for earlier partial captures. The exact trace
predicate below is discharged by ordinary Seq comparison rules; a full
recursive translation is still to be connected. -/
namespace Shallot.MacroPeg.CBV.ControlledPartialPreflight
open ControlledPartialCapture
open PartialCodewordCapture (runA look)
open RuntimeShiftFilter (scanner)
open ClockFreezing (Table)

def control (test : MExp) : CodewordControlFilter.Expr :=
  .star (.seq .token (.test (.seq scanner test)))

def preflight (test : MExp) : MExp := .seq (look (argument test))
  (.seq (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) (control test))
    (.seq (look (.call 1 [runA])) runA))

theorem control_render (test : MExp) :
    CodewordControlFilter.render scanner (control test)=.star (step test) := rfl

theorem preflight_firstOrder (test : MExp) (ht : test.FirstOrder) :
    (preflight test).FirstOrder := by
  have hA : scanner.FirstOrder := by
    simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
      MExp.FirstOrder,MExp.failAlways]
  have hR : runA.FirstOrder := hA.1
  have hF := AdjacentCodewordControl.filter_firstOrder scanner (.call 0 [scanner]) hA
    (by simpa [MExp.FirstOrder,MExp.FirstOrderArgs] using hA) (control test)
    (by simpa [control_render,step,look,MExp.FirstOrder] using And.intro hA (And.intro hA ht))
  exact ⟨argument_firstOrder test ht,hF,⟨hR,True.intro⟩,hR⟩

/-- An actual final codeword anchors the entire adjacent chain, without
assuming that this is the maximal run of codewords in the input. -/
theorem linked_terminal_uniform {C : List Char → Prop}
    (hc : PrefixCodeCapture.PrefixFree C) (u : List Char) (hu : C u)
    (ws : List (List Char)) (hw : ∀ w∈ws, C w) (rest : List Char)
    (hl : AdjacentCodewordControl.Linked ws rest) (hend : u.IsPrefix rest) :
    ws=List.replicate ws.length u := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hws := ih (fun v hv => hw v (by simp [hv])) hl.2
    have hu' : u.IsPrefix (ws.flatten++rest) := by
      rw [hws]
      cases ws.length with
      | zero => simpa using hend
      | succ n => exact ⟨(List.replicate n u).flatten++rest,
          by simp [List.replicate_succ,List.append_assoc]⟩
    obtain ⟨suffix,hinput⟩ := hu'
    have he : w=u := PrefixCodeCapture.prefix_identifies hc (hw w (by simp)) hu
      (by have hh := hl.1; rw [←hinput] at hh; exact hh)
    change w::ws=u::List.replicate ws.length u
    rw [he]
    exact congrArg (List.cons u) hws

private theorem block_not_run (k l : Nat) :
    ¬(RuntimeShiftFilter.block k).IsPrefix (PartialCodewordExecution.firstPiece l) := by
  intro h
  have he : k=l := (RuntimeShiftFilter.block_prefix k l []).mp (by
    apply List.IsPrefix.trans h
    exact ⟨['#'],by simp [RuntimeShiftFilter.block,PartialCodewordExecution.firstPiece]⟩)
  have hl := List.IsPrefix.length_le h
  simp only [RuntimeShiftFilter.block,PartialCodewordExecution.firstPiece,
    List.length_append,List.length_replicate,List.length_singleton] at hl
  omega

/-- Decode complete codewords followed by the actual partial run. No
alternative word count or final run can describe the same captured value. -/
theorem partial_decode (k n : Nat) (ws : List (List Char)) (l : Nat)
    (hw : ∀ w∈ws, ∃ m, w=RuntimeShiftFilter.block m)
    (he : PartialCodewordCapture.captured k n=
      ws.flatten++PartialCodewordExecution.firstPiece l) :
    l=k ∧ ws=List.replicate n (RuntimeShiftFilter.block k) := by
  induction ws generalizing n with
  | nil =>
    cases n with
    | zero =>
      have hl := congrArg List.length he
      simp only [PartialCodewordCapture.captured,CodewordReplay.power,List.replicate_zero,
        List.flatten_nil,List.nil_append,PartialCodewordExecution.firstPiece,
        List.length_replicate] at hl
      exact ⟨hl.symm,rfl⟩
    | succ n =>
      exfalso
      apply block_not_run k l
      exact ⟨CodewordReplay.power (RuntimeShiftFilter.block k) n++
        PartialCodewordExecution.firstPiece k,
        by simpa [PartialCodewordCapture.captured,CodewordReplay.power,
          List.replicate_succ,PartialCodewordExecution.firstPiece,List.append_assoc] using he⟩
  | cons w ws ih =>
    obtain ⟨m,rfl⟩ := hw w (by simp)
    have hws : ∀ w∈ws, ∃ m, w=RuntimeShiftFilter.block m := fun w h => hw w (by simp [h])
    cases n with
    | zero =>
      exfalso
      apply block_not_run m k
      exact ⟨ws.flatten++PartialCodewordExecution.firstPiece l,
        by simpa [PartialCodewordCapture.captured,CodewordReplay.power,
          PartialCodewordExecution.firstPiece,List.append_assoc] using he.symm⟩
    | succ n =>
      have hm : m=k := (RuntimeShiftFilter.block_prefix m k _).mp
        ⟨ws.flatten++PartialCodewordExecution.firstPiece l,by
          simpa [PartialCodewordCapture.captured,CodewordReplay.power,
            List.replicate_succ,PartialCodewordExecution.firstPiece,List.append_assoc]
            using he.symm⟩
      subst m
      have ht : PartialCodewordCapture.captured k n=
          ws.flatten++PartialCodewordExecution.firstPiece l := by
        apply (List.append_right_inj (RuntimeShiftFilter.block k)).mp
        simpa [PartialCodewordCapture.captured,CodewordReplay.power,
          List.replicate_succ,PartialCodewordExecution.firstPiece,List.append_assoc] using he
      obtain ⟨hl,hwords⟩ := ih n hws ht
      exact ⟨hl,by simp only [List.replicate_succ]; rw [hwords]⟩

/-- The adjacent full-word checks plus the rotated final partial-run
check imply a real scanner/whole-capture replay on the unchanged input. -/
theorem trace_replay (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (ws : List (List Char)) (k p q : Nat) (hp : p≤x.length)
    (hw : ∀ w∈ws, ∃ n, w=RuntimeShiftFilter.block n)
    (htrace : sfx x p=(ws.flatten++PartialCodewordExecution.firstPiece k)++sfx x q)
    (hl : AdjacentCodewordControl.Linked ws
      (PartialCodewordExecution.firstPiece k++sfx x q))
    (hend : ('#'::PartialCodewordExecution.firstPiece k).IsPrefix (sfx x q)) :
    ∃ r, evV g x s T [ws.flatten++PartialCodewordExecution.firstPiece k]
      (.seq scanner (.param 0)) p=some (some r) := by
  obtain ⟨suffix,hsuffix⟩ := hend
  have hu : (RuntimeShiftFilter.block k).IsPrefix
      (PartialCodewordExecution.firstPiece k++sfx x q) := by
    refine ⟨PartialCodewordExecution.firstPiece k++suffix,?_⟩
    rw [←hsuffix]
    simp [RuntimeShiftFilter.block,PartialCodewordExecution.firstPiece,List.append_assoc]
  have hws := linked_terminal_uniform PrefixCodeCapture.delimited_prefixFree
    (RuntimeShiftFilter.block k) ⟨k,rfl⟩ ws hw _ hl hu
  have hwhole : ws.flatten++PartialCodewordExecution.firstPiece k=
      PartialCodewordCapture.captured k ws.length := by
    rw [hws]
    simp only [PartialCodewordCapture.captured,CodewordReplay.power,
      List.length_replicate,PartialCodewordExecution.firstPiece]
  have hinput : sfx x p=RuntimeShiftFilter.block k++
      (PartialCodewordCapture.captured k ws.length++suffix) := by
    rw [htrace,hwhole,←hsuffix]
    have hh := PartialCodewordPreflight.word_boundary k ws.length suffix
    simpa [PartialCodewordCapture.captured,CodewordReplay.power,List.replicate_succ,
      PartialCodewordExecution.firstPiece,List.append_assoc] using hh.symm
  have hhead := PrefixCodeCapture.scanner_at g x s T
    [PartialCodewordCapture.captured k ws.length] p k _ hp hinput
  have hrest : sfx x (PartialCodewordCapture.captured k ws.length++suffix).length=
      PartialCodewordCapture.captured k ws.length++suffix :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p)
      ⟨RuntimeShiftFilter.block k,hinput⟩).choose_spec
  refine ⟨suffix.length,?_⟩
  rw [hwhole,evV_seq_ok hhead]
  exact LastCodewordCandidate.literal_at g x s T []
    (PartialCodewordCapture.captured k ws.length) suffix _ hrest

/-- Preflight propagates original argument undefinedness before inspecting
any comparison rule, even with arbitrary rule tables. -/
theorem undefined (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (test : MExp) (p : Nat)
    (h : evV g x s T E (argument test) p=none) :
    evV g x s T E (preflight test) p=none := by
  apply evV_seq_none
  change evV g x s T E (.andP (argument test)) p=none
  rw [CallLookahead.evV_peek,h]; rfl

/-- The last unary helper compares # followed by the actual captured run.
It does not consume a greedy replacement for that retained run. -/
theorem physical_tail_compare (g : MGrammar) (x : List Char) (i m : Nat)
    (hr : ruleAtM g.rules i=some ⟨1,.seq (.lit ['#']) (.param 0)⟩)
    (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E runA p=
      some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (look (.call i [runA])) p=
      if ('#'::pre x p q).IsPrefix (sfx x q) then some (some p) else some none := by
  have hq := evV_ok (tblV_ok g x .callByValueSeq (m+1)) runA p hp q ha
  change evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
    (.andP (.call i [runA])) p=_
  rw [CallLookahead.evV_peek,evV_call_seq hr rfl]
  simp only [evSeqArgs,ha]
  rw [valAt_tblV_succ hr _ hq]
  have hb : evV g x .callByValueSeq (tblV g x .callByValueSeq m) [pre x p q]
      (.seq (.lit ['#']) (.param 0)) q=
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) []
        (.lit ('#'::pre x p q)) q := by
    change evV g x .callByValueSeq (tblV g x .callByValueSeq m) []
      (.seq (.lit ['#']) (.lit (pre x p q))) q=_
    exact CaptureViews.sequence_literals _ _ _ _ _ _ _ _
  rw [hb]
  cases hh : Shallot.stripPrefix? ('#'::pre x p q) (sfx x q) with
  | none =>
    have hn : ¬('#'::pre x p q).IsPrefix (sfx x q) := by
      rintro ⟨rest,he⟩
      have hv := (CBVtoCBN.stripPrefix_exact ('#'::pre x p q) _ rest).mpr he.symm
      rw [hh] at hv; cases hv
    simp only [if_neg hn,evV,hh,CallLookahead.peek]
  | some rest =>
    have hy : ('#'::pre x p q).IsPrefix (sfx x q) :=
      ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm⟩
    simp only [if_pos hy,evV,hh,CallLookahead.peek]

private theorem seq_success (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (a b : MExp) (p q : Nat)
    (h : evV g x s T E (.seq a b) p=some (some q)) :
    ∃ j, evV g x s T E a p=some (some j) ∧ evV g x s T E b j=some (some q) := by
  cases ha : evV g x s T E a p with
  | none => rw [evV_seq_none ha] at h; cases h
  | some r => cases r with
    | none => rw [evV_seq_fail ha] at h; cases h
    | some j => rw [evV_seq_ok ha] at h; exact ⟨j,rfl,h⟩

/-- On every successful actual controlled argument, physical Seq tables
give the exact caller-position filter result and preserve its endpoint.
The codeword trace and final run are obtained from execution, including
parent-dependent and recursive stopping tests. -/
theorem physical_trace (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p q : Nat) (E : List (List Char)) (test : MExp) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument test) p=some (some q)) :
    ∃ (ws : List (List Char)) (k : Nat),
      (∀ w∈ws, ∃ n, w=RuntimeShiftFilter.block n) ∧
      pre x p q=ws.flatten++PartialCodewordExecution.firstPiece k ∧
      sfx x p=(ws.flatten++PartialCodewordExecution.firstPiece k)++sfx x q ∧
      evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (preflight test) p=
        if AdjacentCodewordControl.Linked ws
              (PartialCodewordExecution.firstPiece k++sfx x q) ∧
            ('#'::PartialCodewordExecution.firstPiece k).IsPrefix (sfx x q)
        then some (some q) else some none := by
  let T := tblV g x .callByValueSeq (m+1)
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  obtain ⟨j,hstar,hrun⟩ := seq_success g x .callByValueSeq T E _ _ p q ha
  have hj := evV_ok hOk _ p hp j hstar
  have hq := evV_ok hOk _ j hj q hrun
  have hA : scanner.FirstOrder := by
    simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
      MExp.FirstOrder,MExp.failAlways]
  obtain ⟨ws,hw,htrace,hfilter⟩ := AdjacentCodewordControl.success g x .callByValueSeq
    (by decide) T (tblV_sound hg (by decide) (m+1)) hOk scanner hA
    PrefixCodeCapture.delimited_prefixFree E (.call 0 [scanner])
    (fun p q hp ha => AdjacentCodewordControl.physical_compare g x 0 m r0 E scanner p q hp ha)
    (fun p q hp ha => by
      obtain ⟨k,hk⟩ := PartialCodewordClassification.scanner_shape g x .callByValueSeq T E p q hp ha
      exact ⟨k,by simpa only [length_sfx x hp,length_sfx x (evV_ok hOk _ p hp q ha)]
        using pre_eq (sfx_is_suffix x p) hk⟩)
    (control test) p j hp hstar
  obtain ⟨k,hpre,hs⟩ := PartialCodewordClassification.run_shape g x .callByValueSeq T E j q hj hrun
  have htrace' : sfx x p=(ws.flatten++PartialCodewordExecution.firstPiece k)++sfx x q := by
    rw [htrace,hs,List.append_assoc]
  have hcap : pre x p q=ws.flatten++PartialCodewordExecution.firstPiece k := by
    simpa only [length_sfx x hp,length_sfx x hq] using pre_eq (sfx_is_suffix x p) htrace'
  refine ⟨ws,k,hw,hcap,htrace',?_⟩
  rw [preflight,evV_seq_ok (show evV g x .callByValueSeq T E (look (argument test)) p=
      some (some p) by
    change evV g x .callByValueSeq T E (.andP (argument test)) p=_
    rw [CallLookahead.evV_peek,ha]; rfl)]
  change (match evV g x .callByValueSeq T E
      (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) (control test)) p with
    | some (some z) => evV g x .callByValueSeq T E
        (.seq (look (.call 1 [runA])) runA) z | other => other)=_
  rw [hfilter,hs]
  by_cases hl : AdjacentCodewordControl.Linked ws
      (PartialCodewordExecution.firstPiece k++sfx x q)
  · rw [if_pos hl]
    change (match evV g x .callByValueSeq T E (look (.call 1 [runA])) j with
      | some (some z) => evV g x .callByValueSeq T E runA z | other => other)=_
    rw [physical_tail_compare g x 1 m r1 E j q hj hrun,hpre]
    by_cases ht : ('#'::PartialCodewordExecution.firstPiece k).IsPrefix (sfx x q)
    · simp [ht,hl,hrun]
    · simp [ht,hl]
  · simp [hl]

/-- Accepting the physical filter cannot invent a successful source
replay. The original controlled argument's capture is retained verbatim. -/
theorem physical_sound (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p q r : Nat) (E : List (List Char)) (test : MExp) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument test) p=some (some q))
    (hf : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (preflight test) p=some (some r)) :
    r=q ∧ ∃ z, evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p q] (.seq scanner (.param 0)) p=some (some z) := by
  obtain ⟨ws,k,hw,hcap,htrace,hfilter⟩ := physical_trace g hg x m p q E test hp r0 r1 ha
  rw [hfilter] at hf
  split at hf
  next h =>
    have he : q=r := Option.some.inj (Option.some.inj hf)
    refine ⟨he.symm,?_⟩
    rw [hcap]
    exact trace_replay g x .callByValueSeq _ ws k p q hp hw htrace h.1 h.2
  next h => cases hf

/-- Every successful actual source prefix passes the physical caller
filter, including earlier stops and tests dependent on retained values.
This proves the other direction on all original inputs, not just examples. -/
theorem physical_complete (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p q r : Nat) (E : List (List Char)) (test : MExp) (ht : test.FirstOrder)
    (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument test) p=some (some q))
    (hh : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p q] (.seq scanner (.param 0)) p=some (some r)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (preflight test) p=some (some q) := by
  obtain ⟨ws,k,hw,hcap,_,hfilter⟩ := physical_trace g hg x m p q E test hp r0 r1 ha
  obtain ⟨l,n,hsource,_,hend⟩ := source_prefix_shape g x .callByValueSeq (by decide)
    _ (tblV_sound hg (by decide) (m+1)) E test ht p q r hp ha hh
  obtain ⟨hkl,hws⟩ := partial_decode l n ws k hw (hsource.symm.trans hcap)
  subst k
  have ht : ('#'::PartialCodewordExecution.firstPiece l).IsPrefix (sfx x q) :=
    ⟨sfx x r,by simpa using hend.symm⟩
  have hu : (RuntimeShiftFilter.block l).IsPrefix
      (PartialCodewordExecution.firstPiece l++sfx x q) := by
    refine ⟨PartialCodewordExecution.firstPiece l++sfx x r,?_⟩
    rw [hend]
    simp [RuntimeShiftFilter.block,PartialCodewordExecution.firstPiece,List.append_assoc]
  have hl : AdjacentCodewordControl.Linked ws
      (PartialCodewordExecution.firstPiece l++sfx x q) := by
    rw [hws]
    cases n with
    | zero => trivial
    | succ n =>
      rw [List.replicate_succ]
      apply (AdjacentCodewordControl.linked_uniform PrefixCodeCapture.delimited_prefixFree
        (RuntimeShiftFilter.block l) ⟨l,rfl⟩ (List.replicate n (RuntimeShiftFilter.block l))
        (fun w hw => by obtain ⟨_,rfl⟩ := List.mem_replicate.mp hw; exact ⟨l,rfl⟩) _).mpr
      exact ⟨by simp,hu⟩
  rw [hfilter,if_pos ⟨hl,ht⟩]

theorem physical_iff (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p q : Nat) (E : List (List Char)) (test : MExp) (ht : test.FirstOrder)
    (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument test) p=some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (preflight test) p=some (some q) ↔
    ∃ r, evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p q] (.seq scanner (.param 0)) p=some (some r) := by
  constructor
  · intro hf; exact (physical_sound g hg x m p q q E test hp r0 r1 ha hf).2
  · rintro ⟨r,hr⟩; exact physical_complete g hg x m p q r E test ht hp r0 r1 ha hr

/-- Exact success/failure correspondence after a successful original
argument. Success returns its capture endpoint; the lexical source prefix
has its own replay endpoint. No observation is replaced by a mere Boolean. -/
theorem physical_result (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p q : Nat) (E : List (List Char)) (test : MExp) (ht : test.FirstOrder)
    (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,.seq (.lit ['#']) (.param 0)⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument test) p=some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (preflight test) p=
      match evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
          [pre x p q] (.seq scanner (.param 0)) p with
      | some (some _) => some (some q) | other => other := by
  obtain ⟨r,hr⟩ := PartialCodewordTotality.prefix_total g x .callByValueSeq _
    (tblV_ok g x .callByValueSeq (m+1)) (pre x p q) p hp
  rw [hr]
  cases r with
  | some r => exact physical_complete g hg x m p q r E test ht hp r0 r1 ha hr
  | none =>
    obtain ⟨ws,k,hw,hcap,htrace,hf⟩ := physical_trace g hg x m p q E test hp r0 r1 ha
    rw [hf]
    split
    next h =>
      exfalso
      obtain ⟨r,hreplay⟩ := trace_replay g x .callByValueSeq _ ws k p q hp hw htrace h.1 h.2
      rw [←hcap,hr] at hreplay
      cases hreplay
    next h => rfl

end Shallot.MacroPeg.CBV.ControlledPartialPreflight
