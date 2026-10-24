import MacroPeg.CBV.ControlledFragmentReplay

/-! Syntax-derived partial a-fragments and terminal-delimiter recovery. -/
namespace Shallot.MacroPeg.CBV.ControlledFragmentPreflight
open ClockFreezing (Table)
open PartialCodewordCapture (look runA)
open RuntimeShiftFilter (scanner block)
open ControlledFragmentReplay (argument preflight tailBody)

/-- Each successful iteration consumes one a. J remains a caller-side
lookahead and can stop the fragment before the end of the run. -/
def fragment (J : MExp) : MExp := .star (.seq (.chr 'a') (look J))

theorem fragment_firstOrder (J : MExp) (hJ : J.FirstOrder) :
    (fragment J).FirstOrder := ⟨True.intro,hJ⟩

private theorem step_shape (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (J : MExp) (p q : Nat)
    (h : evV g x s T E (.seq (.chr 'a') (look J)) p=some (some q)) :
    ∃ rest, sfx x p='a'::rest ∧ q=rest.length := by
  cases hc : evV g x s T E (.chr 'a') p with
  | none => rw [evV_seq_none hc] at h; cases h
  | some v => cases v with
    | none => rw [evV_seq_fail hc] at h; cases h
    | some j =>
      rw [evV_seq_ok hc] at h
      change evV g x s T E (.andP J) j=some (some q) at h
      rw [CallLookahead.evV_peek] at h
      have hpos : j=q := by
        cases hj : evV g x s T E J j with
        | none => simp [hj,CallLookahead.peek] at h
        | some v => cases v with
          | none => simp [hj,CallLookahead.peek] at h
          | some r => simpa [hj,CallLookahead.peek] using h
      cases hx : sfx x p with
      | nil => simp [evV,hx] at hc
      | cons c rest =>
        simp only [evV,hx] at hc
        cases hb : Shallot.beqChar 'a' c with
        | false => simp [hb] at hc
        | true =>
          have he : c='a' := (Char.toNat_inj.mp (by
            simpa only [Shallot.beqChar,beq_iff_eq] using hb)).symm
          subst c
          exact ⟨rest,rfl,by simpa [hb,hpos] using hc.symm⟩

/-- Actual successful evaluation supplies an a-only capture, for every
input/table/caller, without a semantic fragment certificate from a caller. -/
theorem fragment_shape (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (J : MExp) :
    ∀ p q, p≤x.length → evV g x s T E (fragment J) p=some (some q) →
      ∃ l, pre x p q=List.replicate l 'a' ∧
        sfx x p=List.replicate l 'a'++sfx x q := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro q hp hv
    change evStar (fun z => evV g x s T E (.seq (.chr 'a') (look J)) z) p=_ at hv
    cases ha : evV g x s T E (.seq (.chr 'a') (look J)) p with
    | none => rw [evStar_none ha] at hv; cases hv
    | some v => cases v with
      | none =>
        rw [evStar_fail ha] at hv
        have he : p=q := by simpa using hv
        subst q
        refine ⟨0,?_,by simp⟩
        simpa [length_sfx x hp] using pre_eq (sfx_is_suffix x p)
          (show sfx x p=[]++sfx x p from rfl)
      | some j =>
        by_cases hj : j<p
        · rw [evStar_ok ha hj] at hv
          obtain ⟨rest,hs,hjrest⟩ := step_shape g x s T E J p j ha
          have hrest : sfx x j=rest := by
            rw [hjrest]
            exact sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨['a'],hs⟩).choose_spec
          obtain ⟨l,_,hl⟩ := ih j hj q (by omega) hv
          have hfull : sfx x p=List.replicate (l+1) 'a'++sfx x q := by
            rw [hs,←hrest,hl,List.replicate_succ,List.cons_append]
          have hq : q≤x.length := Nat.le_trans (evStar_le j q hv) (by omega)
          refine ⟨l+1,?_,hfull⟩
          simpa only [length_sfx x hp,length_sfx x hq] using
            pre_eq (sfx_is_suffix x p) hfull
        · rw [evStar_stuck ha hj] at hv; cases hv

/-- A full delimited word after an a-only fragment forces the remaining
part of that same word to reach #. This also covers an empty fragment. -/
theorem block_prefix_after_fragment : ∀ l k (rest : List Char),
    (block k).IsPrefix (List.replicate l 'a'++rest) →
    ∃ r tail, k=l+r ∧ rest=List.replicate r 'a'++'#'::tail := by
  intro l
  induction l with
  | zero =>
    intro k rest h
    obtain ⟨tail,ht⟩ := h
    exact ⟨k,tail,by omega,by simpa [block,List.append_assoc] using ht.symm⟩
  | succ l ih =>
    intro k rest h
    cases k with
    | zero =>
      obtain ⟨tail,ht⟩ := h
      have he := congrArg List.head? ht
      simp [block,List.replicate_succ] at he
    | succ k =>
      have h' : (block k).IsPrefix (List.replicate l 'a'++rest) := by
        simpa [block,List.replicate_succ] using h
      obtain ⟨r,tail,hk,hr⟩ := ih k rest h'
      exact ⟨r,tail,by omega,hr⟩

private theorem seq_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a b : MExp) (p q : Nat)
    (h : evV g x s T E (.seq a b) p=some (some q)) :
    ∃ j, evV g x s T E a p=some (some j) ∧ evV g x s T E b j=some (some q) := by
  cases ha : evV g x s T E a p with
  | none => rw [evV_seq_none ha] at h; cases h
  | some v => cases v with
    | none => rw [evV_seq_fail ha] at h; cases h
    | some j => rw [evV_seq_ok ha] at h; exact ⟨j,rfl,h⟩

private theorem parameter_prefix (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w : List Char) (p q : Nat)
    (h : evV g x s T [w] (.param 0) p=some (some q)) : w.IsPrefix (sfx x p) := by
  cases he : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [evV,he] at h
  | some rest => exact ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp he).symm⟩

/-- Source success itself supplies the delimiter missing from the earlier
local theorem. The full-word trace and a-only fragment need not be maximal. -/
theorem terminal_of_replay (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (ws : List (List Char)) (l p q z : Nat) (hp : p≤x.length)
    (hw : ∀ w∈ws, ∃ k, w=block k)
    (hi : sfx x p=ws.flatten++List.replicate l 'a'++sfx x q)
    (hh : evV g x s T [ws.flatten++List.replicate l 'a']
      (.seq scanner (.param 0)) p=some (some z)) :
    ∃ r tail, sfx x q=List.replicate r 'a'++'#'::tail := by
  cases ws with
  | nil =>
    obtain ⟨j,hscan,_⟩ := seq_success g x s T _ _ _ p z hh
    obtain ⟨k,hk⟩ := PartialCodewordClassification.scanner_shape g x s T _ p j hp hscan
    have hu : (block k).IsPrefix (List.replicate l 'a'++sfx x q) := by
      refine ⟨sfx x j,?_⟩
      simpa only [List.flatten_nil,List.nil_append] using hk.symm.trans hi
    obtain ⟨r,tail,_,ht⟩ := block_prefix_after_fragment l k _ hu
    exact ⟨r,tail,ht⟩
  | cons u vs =>
    obtain ⟨k,rfl⟩ := hw u (by simp)
    have hscan := PrefixCodeCapture.scanner_at g x s T
      [(block k::vs).flatten++List.replicate l 'a'] p k
      (vs.flatten++List.replicate l 'a'++sfx x q) hp
      (by simpa [List.append_assoc] using hi)
    rw [evV_seq_ok hscan] at hh
    have hparam := parameter_prefix g x s T _ _ z hh
    have hsf : sfx x (vs.flatten++List.replicate l 'a'++sfx x q).length=
        vs.flatten++List.replicate l 'a'++sfx x q :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p)
        ⟨block k,by simpa [List.append_assoc] using hi⟩).choose_spec
    rw [hsf] at hparam
    have hshort : (block k++vs.flatten).IsPrefix
        (vs.flatten++(List.replicate l 'a'++sfx x q)) := by
      apply List.IsPrefix.trans (show (block k++vs.flatten).IsPrefix
        ((block k::vs).flatten++List.replicate l 'a') from ⟨_,rfl⟩)
      simpa only [List.append_assoc] using hparam
    have hl := (AdjacentCodewordControl.linked_replay
      PrefixCodeCapture.delimited_prefixFree (block k) ⟨k,rfl⟩ vs
      (fun w h => hw w (by simp [h])) _).mpr hshort
    have hu := ((AdjacentCodewordControl.linked_uniform
      PrefixCodeCapture.delimited_prefixFree (block k) ⟨k,rfl⟩ vs
      (fun w h => hw w (by simp [h])) _).mp hl).2
    obtain ⟨r,tail,_,ht⟩ := block_prefix_after_fragment l k _ hu
    exact ⟨r,tail,ht⟩

/-- Recover the exact full-word trace from physical evaluation. -/
theorem star_trace (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p j : Nat) (E : List (List Char)) (G : MExp) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (hstar : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (.star (ControlledPartialCapture.step G)) p=some (some j)) :
    ∃ ws, (∀ w∈ws, ∃ k, w=block k) ∧ sfx x p=ws.flatten++sfx x j ∧
      evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
        (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
          (ControlledPartialPreflight.control G)) p=
        if AdjacentCodewordControl.Linked ws (sfx x j) then some (some j) else some none := by
  let T := tblV g x .callByValueSeq (m+1)
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  have hA : scanner.FirstOrder := by
    simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
      MExp.FirstOrder,MExp.failAlways]
  exact AdjacentCodewordControl.success g x .callByValueSeq (by decide) T
    (tblV_sound hg (by decide) (m+1)) hOk scanner hA
    PrefixCodeCapture.delimited_prefixFree E (.call 0 [scanner])
    (fun p q hp ha => AdjacentCodewordControl.physical_compare g x 0 m r0 E scanner p q hp ha)
    (fun p q hp ha => by
      obtain ⟨k,hk⟩ := PartialCodewordClassification.scanner_shape g x .callByValueSeq T E p q hp ha
      exact ⟨k,by simpa only [length_sfx x hp,length_sfx x (evV_ok hOk _ p hp q ha)]
        using pre_eq (sfx_is_suffix x p) hk⟩)
    (ControlledPartialPreflight.control G) p j hp hstar

/-- A physical helper always evaluates the original retained H value at
its actual endpoint. This equality also handles a missing terminal #. -/
theorem tail_result (g : MGrammar) (x : List Char) (m i p q : Nat)
    (hr : ruleAtM g.rules i=some ⟨1,tailBody⟩) (E : List (List Char))
    (H : MExp) (hp : p≤x.length)
    (hh : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E H p=some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (look (.call i [H])) p=
      CallLookahead.peek p (evV g x .callByValueSeq (tblV g x .callByValueSeq m)
        [pre x p q] (.seq scanner (.param 0)) q) := by
  have hq := evV_ok (tblV_ok g x .callByValueSeq (m+1)) H p hp q hh
  change evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (.andP (.call i [H])) p=_
  rw [CallLookahead.evV_peek,evV_call_seq hr rfl]
  simp only [evSeqArgs,hh]
  rw [valAt_tblV_succ hr _ hq]
  rfl

/-- Recover the trace and the exact preflight result on every successful
actual argument, including inputs with no final delimiter. -/
theorem physical_trace (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p j q : Nat) (E : List (List Char)) (G H : MExp) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,tailBody⟩)
    (hs : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (.star (ControlledPartialCapture.step G)) p=some (some j))
    (hh : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E H j=some (some q)) :
    ∃ ws, (∀ w∈ws, ∃ k, w=block k) ∧ sfx x p=ws.flatten++sfx x j ∧
      evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (preflight G H) p=
        if AdjacentCodewordControl.Linked ws (sfx x j) then
          match evV g x .callByValueSeq (tblV g x .callByValueSeq m)
            [pre x j q] (.seq scanner (.param 0)) q with
          | some (some _) => some (some q) | other => other
        else some none := by
  let T := tblV g x .callByValueSeq (m+1)
  have hj := evV_ok (tblV_ok g x .callByValueSeq (m+1)) _ p hp j hs
  obtain ⟨ws,hw,htrace,hfilter⟩ := star_trace g hg x m p j E G hp r0 hs
  refine ⟨ws,hw,htrace,?_⟩
  have ha : evV g x .callByValueSeq T E (argument G H) p=some (some q) := by
    rw [argument,evV_seq_ok hs]; exact hh
  have hlook : evV g x .callByValueSeq T E (look (argument G H)) p=some (some p) := by
    change evV g x .callByValueSeq T E (.andP (argument G H)) p=_
    rw [CallLookahead.evV_peek,ha]; rfl
  rw [preflight,evV_seq_ok hlook]
  change (match evV g x .callByValueSeq T E
      (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
        (ControlledPartialPreflight.control G)) p with
    | some (some z) => evV g x .callByValueSeq T E (.seq (look (.call 1 [H])) H) z
    | other => other)=_
  rw [hfilter]
  by_cases hl : AdjacentCodewordControl.Linked ws (sfx x j)
  · rw [if_pos hl]
    change (match evV g x .callByValueSeq T E (look (.call 1 [H])) j with
      | some (some z) => evV g x .callByValueSeq T E H z | other => other)=_
    rw [tail_result g x m 1 j q r1 E H hj hh,if_pos hl]
    cases hb : evV g x .callByValueSeq (tblV g x .callByValueSeq m)
        [pre x j q] (.seq scanner (.param 0)) q with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some z => exact hh
  · simp [hl]

/-- All-input success correspondence for the syntactic a-fragment.
No capture-shape, delimiter, trace, or word-count hypothesis remains. -/
theorem physical_iff (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p q : Nat) (E : List (List Char)) (G J : MExp) (hJ : J.FirstOrder)
    (hp : p≤x.length) (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,tailBody⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument G (fragment J)) p=some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (preflight G (fragment J)) p=some (some q) ↔
    ∃ z, evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p q] (.seq scanner (.param 0)) p=some (some z) := by
  let T := tblV g x .callByValueSeq (m+1)
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  obtain ⟨j,hs,hh⟩ := seq_success g x .callByValueSeq T E _ _ p q ha
  have hj := evV_ok hOk _ p hp j hs
  have hq := evV_ok hOk _ j hj q hh
  obtain ⟨l,hz,hfrag⟩ := fragment_shape g x .callByValueSeq T E J j q hj hh
  obtain ⟨ws,hw,htrace,hresult⟩ := physical_trace g hg x m p j q E G _ hp r0 r1 hs hh
  have hi : sfx x p=ws.flatten++List.replicate l 'a'++sfx x q := by
    rw [htrace,hfrag,List.append_assoc]
  have hcap : pre x p q=ws.flatten++List.replicate l 'a' := by
    simpa only [length_sfx x hp,length_sfx x hq] using pre_eq (sfx_is_suffix x p) hi
  constructor
  · intro hf
    have hf' := hf
    rw [hresult] at hf'
    split at hf'
    next hl =>
      cases hb : evV g x .callByValueSeq (tblV g x .callByValueSeq m)
          [pre x j q] (.seq scanner (.param 0)) q with
      | none => rw [hb] at hf'; cases hf'
      | some v => cases v with
        | none => rw [hb] at hf'; cases hf'
        | some z =>
          obtain ⟨v,hscan,_⟩ := seq_success g x .callByValueSeq _ _ _ _ q z hb
          obtain ⟨r,hr⟩ := PartialCodewordClassification.scanner_shape g x .callByValueSeq _ _ q v hq hscan
          exact (ControlledFragmentReplay.physical_preflight_iff g hg x m p j q l r E G _
            (fragment_firstOrder J hJ) (sfx x v) hp r0 r1 hs hh hz
            (by simpa [block,List.append_assoc] using hr)).mp hf
    next hl => cases hf'
  · rintro ⟨z,hhsource⟩
    have hb := hhsource
    rw [hcap] at hb
    obtain ⟨r,tail,hr⟩ := terminal_of_replay g x .callByValueSeq T ws l p q z hp hw hi hb
    exact (ControlledFragmentReplay.physical_preflight_iff g hg x m p j q l r E G _
      (fragment_firstOrder J hJ) tail hp r0 r1 hs hh hz hr).mpr ⟨z,hhsource⟩

/-- A successful actual argument gives either its exact capture endpoint
or finite comparison failure; a missing delimiter cannot create None. -/
theorem physical_range (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p q : Nat) (E : List (List Char)) (G H : MExp) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,tailBody⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument G H) p=some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (preflight G H) p=some (some q) ∨
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (preflight G H) p=some none := by
  let T := tblV g x .callByValueSeq (m+1)
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  obtain ⟨j,hs,hh⟩ := seq_success g x .callByValueSeq T E _ _ p q ha
  have hj := evV_ok hOk _ p hp j hs
  have hq := evV_ok hOk _ j hj q hh
  obtain ⟨ws,_,_,hresult⟩ := physical_trace g hg x m p j q E G H hp r0 r1 hs hh
  obtain ⟨v,hv⟩ := PartialCodewordTotality.prefix_total g x .callByValueSeq
    (tblV g x .callByValueSeq m) (tblV_ok g x .callByValueSeq m) (pre x j q) q hq
  rw [hresult,hv]
  cases v <;> by_cases h : AdjacentCodewordControl.Linked ws (sfx x j) <;> simp [h]

/-- Complete caller-position partial result for every input and valid
position. Undefined/failing original arguments are preserved first; on a
successful argument the physical filter tests exactly its whole replay.
No a-only-value, successful-star, or delimiter premise remains. -/
theorem physical_result (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p : Nat) (E : List (List Char)) (G J : MExp) (hJ : J.FirstOrder)
    (hp : p≤x.length) (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,tailBody⟩) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (preflight G (fragment J)) p=
    match evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
        (argument G (fragment J)) p with
    | none => none
    | some none => some none
    | some (some q) =>
      match evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
          [pre x p q] (.seq scanner (.param 0)) p with
      | some (some _) => some (some q) | other => other := by
  let T := tblV g x .callByValueSeq (m+1)
  cases ha : evV g x .callByValueSeq T E (argument G (fragment J)) p with
  | none => exact ControlledFragmentReplay.preflight_none g x .callByValueSeq T E G _ p ha
  | some v => cases v with
    | none => exact ControlledFragmentReplay.preflight_fail g x .callByValueSeq T E G _ p ha
    | some q =>
      dsimp only []
      obtain ⟨v,hv⟩ := PartialCodewordTotality.prefix_total g x .callByValueSeq T
        (tblV_ok g x .callByValueSeq (m+1)) (pre x p q) p hp
      have hiff := physical_iff g hg x m p q E G J hJ hp r0 r1 ha
      rw [hv]
      cases v with
      | none =>
        rcases physical_range g hg x m p q E G _ hp r0 r1 ha with hf | hf
        · obtain ⟨z,hz⟩ := hiff.mp hf
          rw [hv] at hz; cases hz
        · exact hf
      | some z => exact hiff.mpr ⟨z,hv⟩

end Shallot.MacroPeg.CBV.ControlledFragmentPreflight
