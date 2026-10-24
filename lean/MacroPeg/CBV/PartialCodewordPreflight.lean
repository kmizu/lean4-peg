import MacroPeg.CBV.PartialCodewordClassification

/-! Marker-free partial-codeword preflight. The stop is a real scanner
failure, independent of any following continuation syntax. -/
namespace Shallot.MacroPeg.CBV.PartialCodewordPreflight
open PartialCodewordCapture (runA argument restArgument look captured)
open PartialCodewordExecution (firstPiece secondPiece pieces_join)
open RuntimeShiftFilter (block scanner)
open CodewordReplay (power)
open ClockFreezing (Table)
open LastCodewordCandidate (literal_at)

/-- Compare complete shifted runs, then require the next full scanner to
fail before consuming the final held a-run. No delimiter is prescribed. -/
def checkBody : MExp := .seq
  (.star (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))))
  (.seq (.lit ['#']) (.seq (.notP scanner) (.param 0)))

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

private theorem copies_power (u : List Char) (n : Nat) : BlockCapture.copies u n=power u n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BlockCapture.copies,power,List.replicate_succ,ih]

theorem stopped_overlap_tail (k : Nat) (w rest suffix : List Char)
    (hx : (block k++w)++rest=w++suffix)
    (hstop : suffix.head?≠some 'a') : ∃ n, w=captured k n := by
  have hp : w.IsPrefix (block k++w) :=
    List.prefix_of_prefix_length_le ⟨suffix,hx.symm⟩ ⟨rest,rfl⟩ (by simp)
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
  have hrem : (right++left)++rest=suffix := (List.append_right_inj w).mp hx
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


/-- Every successful marker-free checker derives its count, endpoint,
and real terminal scanner failure from its own execution trace. -/
theorem check_inverse (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u : List Char) (p q : Nat) (hp : p≤x.length) (hT : OkTV x.length T)
    (h : evV g x s T [u] checkBody p=some (some q)) :
    ∃ n j, sfx x p=power ('#'::u) (n+1)++sfx x q ∧
      sfx x j=u++sfx x q ∧ evV g x s T [u] scanner j=some none ∧ j≤x.length := by
  let f := fun j => evV g x s T [u]
    (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))) j
  obtain ⟨j,hs,ht⟩ := seq_success g x s T [u] _ _ p q h
  change evStar f p=some (some j) at hs
  obtain ⟨n,trace,hloopstop⟩ := InlineRepeat.star_trace f p j hs
  have hprefix : sfx x p=power ('#'::u) n++sfx x j := by
    clear h ht hs hloopstop hp hT
    induction trace with
    | zero p => simp [power]
    | @succ p z n j hv hz tail ih =>
      obtain ⟨v,hv',hl⟩ := word_success g x s T u _ p z hv
      obtain ⟨he,_⟩ := look_success g x s T [u] _ v z hl
      rw [←he] at hv'
      rw [hv',ih]
      simp [power,List.replicate_succ,List.append_assoc]
  obtain ⟨v,hh,ht⟩ := seq_success g x s T [u] _ _ j q ht
  obtain ⟨z,hn,hword⟩ := seq_success g x s T [u] _ _ v q ht
  have hfail : evV g x s T [u] scanner v=some none := by
    cases ha : evV g x s T [u] scanner v with
    | none => simp [evV,ha] at hn
    | some r => cases r with
      | none => rfl
      | some t => rw [evV_not_ok ha] at hn; cases hn
  rw [evV_not_fail hfail] at hn
  have hvz : v=z := Option.some.inj (Option.some.inj hn)
  subst z
  have hhash := literal_success g x s T [u] ['#'] j v hh
  have hword' := literal_success g x s T [] u v q hword
  have hj : j≤x.length := Nat.le_trans (InlineRepeat.trace_le trace) hp
  have hv := evV_ok hT _ j hj v hh
  refine ⟨n,v,?_,hword',hfail,hv⟩
  rw [hprefix,hhash,hword',LastCodewordCandidate.power_succ_right]
  simp [List.append_assoc]

/-- The scanner has no rule calls or environment reads. A physical stop
proved in the checker is therefore the same stop in the original caller. -/
theorem scanner_context (g g' : MGrammar) (x : List Char) (s s' : Strategy)
    (T T' : Table) (E E' : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E scanner p=evV g' x s' T' E' scanner p := by
  rw [scanner,evV_seq_ok (NestedScannerArguments.scan_eval g x s T E ['a'] p hp),
    evV_seq_ok (NestedScannerArguments.scan_eval g' x s' T' E' ['a'] p hp)]
  rfl

private theorem failed_scanner_not_hash (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (k p : Nat) (rest : List Char)
    (hp : p≤x.length) (hs : sfx x p=firstPiece k++rest)
    (hf : evV g x s T E scanner p=some none) :
    evV g x s T E (.lit ['#']) rest.length=some none := by
  have hsrest : sfx x rest.length=rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨firstPiece k,hs⟩).choose_spec
  cases rest with
  | nil =>
    simp only [List.length_nil] at hsrest ⊢
    simp [evV,hsrest,Shallot.stripPrefix?]
  | cons c rest =>
    by_cases hc : c='#'
    · subst c
      have hh := PrefixCodeCapture.scanner_at g x s T E p k rest hp
        (by simpa [block,firstPiece,List.append_assoc] using hs)
      rw [hf] at hh
      cases hh
    · simp only [evV,hsrest,Shallot.stripPrefix?]
      have hchar : Shallot.beqChar '#' c=false := by
        simp only [Shallot.beqChar]
        exact beq_eq_false_iff_ne.mpr (fun he => hc (Char.toNat_inj.mp he.symm))
      simp [hchar]

/-- A successful maximal scanner run supplies the exact original capture
for an arbitrary following suffix. No continuation marker is assumed. -/
theorem argument_at (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (k n p : Nat) (rest : List Char)
    (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+1)++firstPiece k++rest)
    (hend : evV g x s T E scanner (firstPiece k++rest).length=some none) :
    evV g x s T E argument p=
      some (some ('#'::(firstPiece k++rest)).length) := by
  let A := fun q => evV g x s T E scanner q
  let finalRest := firstPiece k++rest
  have hblock : block k≠[] := by simp [block]
  have hstep : ∀ j r, j≤x.length → sfx x j=block k++r → A j=some (some r.length) :=
    fun j r hj hr => PrefixCodeCapture.scanner_at g x s T E j k r hj hr
  have ht := LastCodewordCandidate.constant_trace x (block k) hblock A hstep
    (n+1) p finalRest hp (by simpa only [finalRest,List.append_assoc] using hs)
  obtain ⟨q,hq,_,hstar⟩ := LastCodewordRotation.last_trace A n p _ ht hend
  have hs' : sfx x p=power (block k) n++(block k++finalRest) := by
    rw [hs,LastCodewordCandidate.power_succ_right]
    simp only [finalRest,List.append_assoc]
  have ht' := LastCodewordCandidate.constant_trace x (block k) hblock A hstep
    n p (block k++finalRest) hp hs'
  have he : q=(block k++finalRest).length := by
    have hh := (InlineRepeat.trace_steps (LastCodewordRotation.step_trace hq)).symm.trans
      (InlineRepeat.trace_steps ht')
    simpa using hh
  have hsuffix : sfx x (block k++finalRest).length=block k++finalRest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨power (block k) n,hs'⟩).choose_spec
  have hb' : (block k++finalRest).length≤x.length := by
    have := InlineRepeat.trace_le ht'; omega
  have hstar' : evV g x s T E (.star (.seq scanner (look scanner))) p=
      some (some (block k++finalRest).length) := by
    change evV g x s T E (LastCodewordRotation.argument scanner) p=_
    rw [LastCodewordRotation.argument_eval]
    exact he ▸ hstar
  rw [argument,evV_seq_ok hstar']
  exact PartialCodewordCapture.run_at g x s T E k _ '#' finalRest (by decide) hb'
    (by simpa only [block,firstPiece,List.append_assoc,List.singleton_append] using hsuffix)

/-- The real checker accepts a uniform run exactly to the replay endpoint
whenever the next scanner actually fails. The following continuation may
begin with a, fail, diverge, or inspect the whole retained capture. -/
theorem check_at (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (k n p : Nat) (rest : List Char) (hp : p≤x.length)
    (hs : sfx x p=power ('#'::firstPiece k) (n+1)++rest)
    (hend : evV g x s T [firstPiece k] scanner (firstPiece k++rest).length=some none) :
    evV g x s T [firstPiece k] checkBody p=some (some rest.length) := by
  let u := '#'::firstPiece k
  have hfinal : sfx x (u++rest).length=u++rest := by
    have hh : sfx x p=power u n++(u++rest) := by
      rw [hs,LastCodewordCandidate.power_succ_right,List.append_assoc]
    exact sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨power u n,hh⟩).choose_spec
  have hsr : sfx x (firstPiece k++rest).length=firstPiece k++rest := by
    exact sfx_suffix (suffix_trans (sfx_is_suffix x (u++rest).length) ⟨['#'],hfinal⟩).choose_spec
  have hb : (firstPiece k++rest).length≤x.length := by
    have hbound : (u++rest).length≤x.length := by
      have hh := congrArg List.length hs
      rw [length_sfx x hp,List.length_append] at hh
      change p=(power u (n+1)).length+rest.length at hh
      have hh' := congrArg List.length (show power u (n+1)=power u n++u from LastCodewordCandidate.power_succ_right _ _)
      simp only [List.length_append] at hh'
      simp only [List.length_append]
      omega
    change (firstPiece k++rest).length≤x.length
    have hu : (u++rest).length=(firstPiece k++rest).length+1 := by simp [u]
    omega
  have hhashfail := failed_scanner_not_hash g x s T [firstPiece k] k _ rest hb hsr hend
  let f := fun q => evV g x s T [firstPiece k]
    (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))) q
  have loop : ∀ n p, p≤x.length → sfx x p=power u (n+1)++rest →
      evStar f p=some (some (u++rest).length) := by
    intro n
    induction n with
    | zero =>
      intro q hq hs
      have hs' : sfx x q=u++rest := by simpa [power] using hs
      have hf : f q=some none := by
        rw [show f q=evV g x s T [firstPiece k]
          (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))) q from rfl,
          word_then g x s T k q rest _ hs']
        change evV g x s T [firstPiece k] (.andP (.lit ['#'])) rest.length=_
        rw [CallLookahead.evV_peek,hhashfail]
        rfl
      rw [evStar_fail hf]
      have hlen := congrArg List.length hs'
      rw [length_sfx x hq] at hlen
      exact congrArg (fun t => some (some t)) hlen
    | succ n ih =>
      intro q hq hs
      let r := power u (n+1)++rest
      have hs' : sfx x q=u++r := by simpa [r,power,List.replicate_succ,List.append_assoc] using hs
      have hr : r.length<q := by
        have hh := congrArg List.length hs'
        rw [length_sfx x hq,List.length_append] at hh
        have hu : 0<u.length := by simp [u]
        omega
      have hsr' : sfx x r.length=r :=
        sfx_suffix (suffix_trans (sfx_is_suffix x q) ⟨u,hs'⟩).choose_spec
      have hhash : evV g x s T [firstPiece k] (.lit ['#']) r.length=
          some (some (firstPiece k++(power u n++rest)).length) := by
        apply literal_at
        simpa [r,power,List.replicate_succ,u,List.append_assoc] using hsr'
      have hf : f q=some (some r.length) := by
        rw [show f q=evV g x s T [firstPiece k]
          (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))) q from rfl,
          word_then g x s T k q r _ hs']
        exact look_ok g x s T _ _ _ _ hhash
      rw [evStar_ok hf hr]
      exact ih r.length (by omega) hsr'
  have hl := loop n p hp hs
  change evV g x s T [firstPiece k]
    (.star (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#']))))) p=_ at hl
  have hh := literal_at g x s T [firstPiece k] ['#'] (firstPiece k++rest) (u++rest).length hfinal
  have hw := literal_at g x s T [] (firstPiece k) rest (firstPiece k++rest).length hsr
  rw [checkBody,evV_seq_ok hl,evV_seq_ok hh,evV_seq_ok (evV_not_fail hend)]
  exact hw

theorem word_boundary (k n : Nat) (rest : List Char) :
    power (block k) (n+1)++firstPiece k++rest=
      captured k n++('#'::(firstPiece k++rest)) := by
  rw [LastCodewordCandidate.power_succ_right]
  simp [captured,block,firstPiece,List.append_assoc]

/-- Both actual Seq arguments retain the full original value, with no
marker premise and with the unchanged caller environment for both. -/
theorem split_arguments (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (k n p : Nat) (rest : List Char)
    (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+2)++firstPiece k++rest)
    (hend : evV g x s T E scanner (firstPiece k++rest).length=some none) :
    evSeqArgs g x s T E [runA,restArgument] p=
      some (some ([firstPiece k,secondPiece k n],
        ('#'::(firstPiece k++rest)).length)) := by
  let r := power (block k) (n+1)++firstPiece k++rest
  have hs' : sfx x p=firstPiece k++'#'::r := by
    simpa [r,firstPiece,block,power,List.replicate_succ,List.append_assoc] using hs
  have hfirst := PartialCodewordCapture.run_at g x s T E k p '#' r (by decide) hp hs'
  have hlen := congrArg List.length hs'
  rw [length_sfx x hp,List.length_append] at hlen
  have hj : ('#'::r).length≤x.length := by omega
  have hsfirst : sfx x ('#'::r).length='#'::r :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨firstPiece k,hs'⟩).choose_spec
  have hsafter : sfx x r.length=r :=
    sfx_suffix (suffix_trans (sfx_is_suffix x ('#'::r).length) ⟨['#'],hsfirst⟩).choose_spec
  have hr : r.length≤x.length := by simp only [List.length_cons] at hj; omega
  have hhash := literal_at g x s T E ['#'] r ('#'::r).length hsfirst
  have harg := argument_at g x s T E k n r.length rest hr hsafter hend
  have hsecond : evV g x s T E restArgument ('#'::r).length=
      some (some ('#'::(firstPiece k++rest)).length) := by
    rw [restArgument,evV_seq_ok hhash]
    exact harg
  have hcfirst : pre x p ('#'::r).length=firstPiece k := by
    have hh := pre_eq (sfx_is_suffix x p) hs'
    simpa only [length_sfx x hp] using hh
  have hssecond : sfx x ('#'::r).length=
      secondPiece k n++('#'::(firstPiece k++rest)) := by
    rw [hsfirst]
    simp only [r]
    rw [word_boundary]
    rfl
  have hcsecond : pre x ('#'::r).length ('#'::(firstPiece k++rest)).length=
      secondPiece k n := by
    have hh := pre_eq (sfx_is_suffix x ('#'::r).length) hssecond
    simpa only [length_sfx x hj] using hh
  rw [evSeq_cons_ok hfirst,evSeq_cons_ok hsecond]
  simp only [evSeqArgs,hcfirst,hcsecond]


/-- Complete partial continuation results agree at the actual split
endpoint, for arbitrary first-order b and arbitrary following suffix. -/
theorem bodies_eq (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (k n p : Nat) (rest : List Char) (b : MExp) (hb : b.FirstOrder)
    (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+2)++firstPiece k++rest) :
    evV g x s T [captured k (n+1)] (.seq scanner (.seq (.param 0) b)) p=
      evV g x s T [firstPiece k,secondPiece k n]
        (.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView b)))
        ('#'::(firstPiece k++rest)).length := by
  have hs' : sfx x p=block k++(captured k (n+1)++rest) := by
    simpa [captured,power,List.replicate_succ,firstPiece,List.append_assoc] using hs
  have hhead := PrefixCodeCapture.scanner_at g x s T [captured k (n+1)] p k _ hp hs'
  have hsr : sfx x (captured k (n+1)++rest).length=captured k (n+1)++rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨block k,hs'⟩).choose_spec
  have hreplay : evV g x s T [captured k (n+1)] (.param 0) (captured k (n+1)++rest).length=some (some rest.length) := literal_at g x s T [] (captured k (n+1)) rest _ hsr
  rw [evV_seq_ok hhead,evV_seq_ok hreplay]
  have hs'' : sfx x p=captured k (n+1)++('#'::(firstPiece k++rest)) := by
    rw [hs,word_boundary k (n+1) rest]
  have hsend : sfx x ('#'::(firstPiece k++rest)).length='#'::(firstPiece k++rest) :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨captured k (n+1),hs''⟩).choose_spec
  have hhash := literal_at g x s T [firstPiece k,secondPiece k n] ['#'] (firstPiece k++rest) _ hsend
  have hsrun : sfx x (firstPiece k++rest).length=firstPiece k++rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x ('#'::(firstPiece k++rest)).length) ⟨['#'],hsend⟩).choose_spec
  have hparam : evV g x s T [firstPiece k,secondPiece k n] (.param 0)
      (firstPiece k++rest).length=some (some rest.length) :=
    literal_at g x s T [] (firstPiece k) rest _ hsrun
  rw [evV_seq_ok hhash,evV_seq_ok hparam,
    CodewordControlFilter.wholeView_eval g x s T (firstPiece k) (secondPiece k n) b hb,
    pieces_join]

/-- Rotate the uniform source head/replay prefix into the checker view. -/
theorem rotated (k n : Nat) (rest : List Char) :
    power (block k) (n+1)++firstPiece k++rest=
      firstPiece k++(power ('#'::firstPiece k) (n+1)++rest) := by
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
  rw [←List.append_assoc,go,List.append_assoc]

/-- The actual stage-m+1 preflight invokes the generated checker rule.
The caller supplies no semantic row oracle or continuation marker. -/
theorem preflight_at (g : MGrammar) (x : List Char) (m p k n : Nat)
    (E : List (List Char)) (rest : List Char)
    (rule : ruleAtM g.rules 0=some ⟨1,checkBody⟩) (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+1)++firstPiece k++rest)
    (hend : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      scanner (firstPiece k++rest).length=some none) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (.call 0 [runA]) p=some (some rest.length) := by
  let T := tblV g x .callByValueSeq (m+1)
  let r := power ('#'::firstPiece k) (n+1)++rest
  have hs' : sfx x p=firstPiece k++r := by rw [hs,rotated]
  have hfirst : evV g x .callByValueSeq T E runA p=some (some r.length) := by
    apply PartialCodewordCapture.run_at g x .callByValueSeq T E k p '#' _ (by decide) hp
    simpa [r,power,firstPiece,List.replicate_succ,List.append_assoc] using hs'
  have hr : r.length≤x.length := by
    have hh := congrArg List.length hs'
    rw [length_sfx x hp,List.length_append] at hh
    omega
  have hsr : sfx x r.length=r :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨firstPiece k,hs'⟩).choose_spec
  have hcap : pre x p r.length=firstPiece k := by
    have hh := pre_eq (sfx_is_suffix x p) hs'
    simpa only [length_sfx x hp] using hh
  have htail : (firstPiece k++rest).length≤x.length := by
    have hh := congrArg List.length hs
    rw [length_sfx x hp,List.length_append,List.length_append] at hh
    simp only [List.length_append]
    omega
  have hend' : evV g x .callByValueSeq (tblV g x .callByValueSeq m)
      [firstPiece k] scanner (firstPiece k++rest).length=some none :=
    (scanner_context g g x .callByValueSeq .callByValueSeq _ _ _ _ _ htail).trans hend
  change evV g x .callByValueSeq T E (.call 0 [runA]) p=_
  rw [evV_call_seq rule rfl]
  simp only [evSeqArgs,hfirst,hcap]
  rw [valAt_tblV_succ rule _ hr]
  exact check_at g x .callByValueSeq _ k n r.length rest hr hsr hend'

/-- The real source argument and initial replay, on any input, force the
uniform partial-codeword shape and its terminal scanner failure. Neither
shape nor terminal stop is an extra caller assumption. -/
theorem source_prefix_shape (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p j q : Nat) (E : List (List Char)) (hp : p≤x.length)
    (ha : evV g x .callByValuePar (tblV g x .callByValuePar m) E argument p=some (some j))
    (hh : evV g x .callByValuePar (tblV g x .callByValuePar m) [pre x p j]
      (.seq scanner (.param 0)) p=some (some q)) :
    ∃ k n, pre x p j=captured k n ∧
      sfx x p=power (block k) (n+1)++firstPiece k++sfx x q ∧
      evV g x .callByValuePar (tblV g x .callByValuePar m) E
        scanner (firstPiece k++sfx x q).length=some none := by
  let T := tblV g x .callByValuePar m
  let w := pre x p j
  have hT := tblV_ok g x .callByValuePar m
  have hf : argument.FirstOrder := by
    simp [argument,runA,look,scanner,NestedScannerArguments.scan,
      NestedScannerArguments.choice,MExp.failAlways,MExp.FirstOrder]
  have hprefix := (ReplayFusion.success_prefix (tblV_sound hg (by decide) m)
    E argument hf p j hp ha).2
  have hstop := PartialCodewordClassification.argument_stop g x .callByValuePar T E p j hp hT ha
  obtain ⟨v,hscan,hw⟩ := seq_success g x .callByValuePar T [w] _ _ p q hh
  obtain ⟨k,hk⟩ := PartialCodewordClassification.scanner_shape g x .callByValuePar T [w] p v hp hscan
  have hw' := literal_success g x .callByValuePar T [] w v q hw
  have hsource : sfx x p=(block k++w)++sfx x q := by
    rw [hk,hw',List.append_assoc]
  obtain ⟨n,hn⟩ := stopped_overlap_tail k w (sfx x q) (sfx x j)
    (hsource.symm.trans hprefix) hstop
  have hshape : sfx x p=power (block k) (n+1)++firstPiece k++sfx x q := by
    simpa [hn,captured,firstPiece,power,List.replicate_succ,List.append_assoc] using hsource
  have hargend : sfx x j='#'::(firstPiece k++sfx x q) := by
    have hs' : sfx x p=captured k n++('#'::(firstPiece k++sfx x q)) := by
      rw [hshape,word_boundary]
    have he : w++sfx x j=w++('#'::(firstPiece k++sfx x q)) := by
      rw [←hprefix,hn]
      exact hs'
    exact (List.append_right_inj w).mp he
  obtain ⟨z,hstar,hrun⟩ := seq_success g x .callByValuePar T E _ _ p j ha
  have hhash := literal_at g x .callByValuePar T E ['#'] (firstPiece k++sfx x q) j hargend
  have hlast : evV g x .callByValuePar T E scanner z=
      some (some (firstPiece k++sfx x q).length) := by
    change evV g x .callByValuePar T E (.seq runA (.lit ['#'])) z=_
    rw [evV_seq_ok hrun]
    exact hhash
  change evV g x .callByValuePar T E (LastCodewordRotation.argument scanner) p=_ at hstar
  rw [LastCodewordRotation.argument_eval] at hstar
  rcases LastCodewordRotation.capture_endpoint _ p z hstar with hzero | ⟨r,hr,hend⟩
  · rw [hzero.2] at hlast
    cases hlast
  · have he : r=(firstPiece k++sfx x q).length :=
      Option.some.inj (Option.some.inj (hr.symm.trans hlast))
    exact ⟨k,n,hn,hshape,he ▸ hend⟩

/-- An arbitrary successful source prefix is accepted by the physical
marker-free target preflight, even across unrelated rule tables. -/
theorem source_to_preflight (g g' : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m m' p j q : Nat) (E E' : List (List Char)) (hp : p≤x.length)
    (rule : ruleAtM g'.rules 0=some ⟨1,checkBody⟩)
    (ha : evV g x .callByValuePar (tblV g x .callByValuePar m) E argument p=some (some j))
    (hh : evV g x .callByValuePar (tblV g x .callByValuePar m) [pre x p j]
      (.seq scanner (.param 0)) p=some (some q)) :
    evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
      (.call 0 [runA]) p=some (some q) := by
  obtain ⟨k,n,_,hs,hend⟩ := source_prefix_shape g hg x m p j q E hp ha hh
  have hq := evV_ok (tblV_ok g x .callByValuePar m) _ p hp q hh
  have htail : (firstPiece k++sfx x q).length≤x.length := by
    have hl := congrArg List.length hs
    rw [length_sfx x hp,List.length_append,List.length_append] at hl
    simp only [List.length_append]
    omega
  have hend' : evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
      scanner (firstPiece k++sfx x q).length=some none :=
    (scanner_context g' g x .callByValueSeq .callByValuePar _ _ _ _ _ htail).trans hend
  have he := preflight_at g' x m' p k n E' (sfx x q) rule hp hs hend'
  simpa only [length_sfx x hq] using he

/-- Successful physical preflight calls derive the original uniform
prefix and terminal scanner stop on arbitrary input. -/
theorem preflight_inverse (g : MGrammar) (x : List Char) (m p q : Nat)
    (E : List (List Char)) (rule : ruleAtM g.rules 0=some ⟨1,checkBody⟩)
    (hp : p≤x.length)
    (h : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (.call 0 [runA]) p=some (some q)) :
    ∃ k n, sfx x p=power (block k) (n+1)++firstPiece k++sfx x q ∧
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) [firstPiece k]
        scanner (firstPiece k++sfx x q).length=some none := by
  rw [evV_call_seq rule rfl] at h
  cases hv : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E runA p with
  | none => simp only [evSeqArgs,hv] at h; cases h
  | some r => cases r with
    | none => simp only [evSeqArgs,hv] at h; cases h
    | some j =>
      simp only [evSeqArgs,hv] at h
      have hj := evV_ok (tblV_ok g x .callByValueSeq (m+1)) runA p hp j hv
      obtain ⟨k,hcap,hs⟩ := PartialCodewordClassification.run_shape g x .callByValueSeq _ E p j hp hv
      rw [hcap,valAt_tblV_succ rule _ hj] at h
      obtain ⟨n,v,hn,hv',hend,hvbound⟩ := check_inverse g x .callByValueSeq _
        (firstPiece k) j q hj (tblV_ok g x .callByValueSeq m) h
      have he : v=(firstPiece k++sfx x q).length := by
        have hh := congrArg List.length hv'
        rwa [length_sfx x hvbound] at hh
      refine ⟨k,n,?_,he ▸ hend⟩
      rw [rotated,hs,hn]

/-- Any successful target preflight reconstructs the real original Par
argument and its initial replay, in an unrelated grammar and clock. -/
theorem preflight_to_source (g g' : MGrammar) (x : List Char)
    (m m' p q : Nat) (E E' : List (List Char)) (hp : p≤x.length)
    (rule : ruleAtM g'.rules 0=some ⟨1,checkBody⟩)
    (h : evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
      (.call 0 [runA]) p=some (some q)) :
    ∃ j, evV g x .callByValuePar (tblV g x .callByValuePar m) E argument p=some (some j) ∧
      evV g x .callByValuePar (tblV g x .callByValuePar m) [pre x p j]
        (.seq scanner (.param 0)) p=some (some q) := by
  obtain ⟨k,n,hs,hend⟩ := preflight_inverse g' x m' p q E' rule hp h
  have hq := evV_ok (tblV_ok g' x .callByValueSeq (m'+1)) _ p hp q h
  have htail : (firstPiece k++sfx x q).length≤x.length := by
    have hl := congrArg List.length hs
    rw [length_sfx x hp,List.length_append,List.length_append] at hl
    simp only [List.length_append]
    omega
  have hend' : evV g x .callByValuePar (tblV g x .callByValuePar m) E
      scanner (firstPiece k++sfx x q).length=some none :=
    (scanner_context g g' x .callByValuePar .callByValueSeq _ _ _ _ _ htail).trans hend
  have ha := argument_at g x .callByValuePar (tblV g x .callByValuePar m) E k n p
    (sfx x q) hp hs hend'
  have hs' : sfx x p=captured k n++('#'::(firstPiece k++sfx x q)) := by
    rw [hs,word_boundary]
  have hcap : pre x p ('#'::(firstPiece k++sfx x q)).length=captured k n := by
    have hh := pre_eq (sfx_is_suffix x p) hs'
    simpa only [length_sfx x hp] using hh
  refine ⟨_,ha,?_⟩
  rw [hcap]
  have hshead : sfx x p=block k++(captured k n++sfx x q) := by
    simpa [captured,power,firstPiece,List.replicate_succ,List.append_assoc] using hs
  have hhead := PrefixCodeCapture.scanner_at g x .callByValuePar (tblV g x .callByValuePar m) [captured k n] p k _ hp hshead
  rw [evV_seq_ok hhead]
  have hsword : sfx x (captured k n++sfx x q).length=captured k n++sfx x q :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨block k,hshead⟩).choose_spec
  have hw := literal_at g x .callByValuePar (tblV g x .callByValuePar m) [] (captured k n) (sfx x q) _ hsword
  change evV g x .callByValuePar (tblV g x .callByValuePar m) []
    (.lit (captured k n)) (captured k n++sfx x q).length=_
  simpa only [length_sfx x hq] using hw

/-- All-input, same-endpoint equivalence of the real source capture plus
initial replay and the physical marker-free target preflight. This is an
entry theorem, not a recursive user-row simulation. -/
theorem preflight_iff_source_prefix (g g' : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m m' p q : Nat) (E E' : List (List Char)) (hp : p≤x.length)
    (rule : ruleAtM g'.rules 0=some ⟨1,checkBody⟩) :
    evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
      (.call 0 [runA]) p=some (some q) ↔
    ∃ j, evV g x .callByValuePar (tblV g x .callByValuePar m) E argument p=some (some j) ∧
      evV g x .callByValuePar (tblV g x .callByValuePar m) [pre x p j]
        (.seq scanner (.param 0)) p=some (some q) := by
  constructor
  · exact preflight_to_source g g' x m m' p q E E' hp rule
  · rintro ⟨j,ha,hh⟩
    exact source_to_preflight g g' hg x m m' p j q E E' hp rule ha hh

/-- A concrete grammar family for operational checks. General recursive
row correspondence for these generated bodies is a separate obligation. -/
def source (b : MExp) : MGrammar := ⟨[⟨1,.seq scanner (.seq (.param 0) b)⟩]⟩
def target (b : MExp) : MGrammar := ⟨[
  ⟨1,checkBody⟩,
  ⟨2,.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView b))⟩,
  ⟨1,.seq (.lit ['#']) (.seq (.param 0) b)⟩]⟩
def sourceRoot : MExp := PartialCodewordCapture.sourceRoot
def targetRoot : MExp := PartialCodewordCapture.targetRoot

theorem firstOrder (b : MExp) (hb : b.FirstOrder) :
    (source b).FirstOrder ∧ (target b).FirstOrder := by
  have hw := CodewordControlFilter.wholeView_firstOrder b hb
  simp [MGrammar.FirstOrder,source,target,checkBody,scanner,look,
    NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,
    MExp.FirstOrder,hb,hw]

private def reuseTail : MExp := .seq (.lit "aZ".toList)
  (.seq (.param 0) PartialCodewordCapture.eof)

/-- These actual Par/Seq executions have no ! delimiter. The continuation
starts with a and reuses a zero-word, empty, or multiword whole capture. -/
theorem marker_free_executions : ∀ x ∈
    ["#aZ".toList,"##aZ#".toList,"a#aaZa".toList,"a#a#aaZa#a".toList],
    evV (source reuseTail) x .callByValuePar (tblV (source reuseTail) x .callByValuePar 1)
      [] sourceRoot x.length=some (some 0) ∧
    evV (target reuseTail) x .callByValueSeq (tblV (target reuseTail) x .callByValueSeq 1)
      [] targetRoot x.length=some (some 0) := by
  decide +kernel

/-- Entry success leaves the arbitrary continuation's undefinedness
intact. A malformed prefix still fails before reaching that continuation. -/
theorem undefined_continuation :
    let b := MExp.star (.lit [])
    let x := "a#a#aaZ".toList
    let y := "#a#!#a".toList
    evV (source b) x .callByValuePar (tblV (source b) x .callByValuePar 1)
      [] sourceRoot x.length=none ∧
    evV (target b) x .callByValueSeq (tblV (target b) x .callByValueSeq 1)
      [] targetRoot x.length=none ∧
    evV (source b) y .callByValuePar (tblV (source b) y .callByValuePar 1)
      [] sourceRoot y.length=some none ∧
    evV (target b) y .callByValueSeq (tblV (target b) y .callByValueSeq 1)
      [] targetRoot y.length=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.PartialCodewordPreflight
