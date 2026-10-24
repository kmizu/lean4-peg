import MacroPeg.CBV.ControlledPartialPreflight

/-! Shifted replay with an independently selected final fragment. Unlike
ControlledPartialCapture, the final fragment need not exhaust the a-run.
The physical helper below preserves the actual fragment parser and caller.
This is a local bridge, not an unrestricted recursive compiler. -/
namespace Shallot.MacroPeg.CBV.ControlledFragmentReplay
open ClockFreezing (Table)
open PartialCodewordCapture (runA look)
open RuntimeShiftFilter (scanner block)

def argument (G H : MExp) : MExp := .seq (.star (ControlledPartialCapture.step G)) H

def preflight (G H : MExp) : MExp :=
  .seq (look (argument G H))
    (.seq (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
      (ControlledPartialPreflight.control G))
      (.seq (look (.call 1 [H])) H))

def entry (G H : MExp) : MExp :=
  .seq (look (preflight G H))
    (.alt (.seq (look (ControlledPartialCapture.step G))
      (.call 2 [runA,.seq (.lit ['#']) (.star (ControlledPartialCapture.step G)),H]))
      (.seq (.notP (ControlledPartialCapture.step G)) (.call 3 [H])))

/-- Original argument divergence is observed before any comparison. -/
theorem preflight_none (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (G H : MExp) (p : Nat)
    (ha : evV g x s T E (argument G H) p=none) :
    evV g x s T E (preflight G H) p=none := by
  apply evV_seq_none
  change evV g x s T E (.andP (argument G H)) p=none
  rw [CallLookahead.evV_peek,ha]; rfl

/-- A failing fragment remains a failing argument before comparisons. -/
theorem preflight_fail (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (G H : MExp) (p : Nat)
    (ha : evV g x s T E (argument G H) p=some none) :
    evV g x s T E (preflight G H) p=some none := by
  apply evV_seq_fail
  change evV g x s T E (.andP (argument G H)) p=some none
  rw [CallLookahead.evV_peek,ha]; rfl

/-- A zero-consuming loop in the fragment parser is never replaced by a
shorter finite capture, at any physical clock or arbitrary rule table. -/
theorem fragment_loop_none (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (G : MExp) (p j : Nat)
    (hstar : evV g x s T E (.star (ControlledPartialCapture.step G)) p=some (some j)) :
    evV g x s T E (argument G (.star .eps)) p=none ∧
    evV g x s T E (preflight G (.star .eps)) p=none := by
  have ha : evV g x s T E (argument G (.star .eps)) p=none := by
    rw [argument,evV_seq_ok hstar]
    exact evStar_stuck (j:=j) rfl (Nat.lt_irrefl j)
  exact ⟨ha,preflight_none g x s T E G _ p ha⟩

/-- Appending an arbitrary fragment to the complete-word trace requires
one additional comparison beyond the adjacent full-word comparisons. -/
theorem linked_fragment_iff {C : List Char → Prop}
    (hc : PrefixCodeCapture.PrefixFree C) (u v z tail : List Char)
    (vs : List (List Char)) (hu : C u) (hv : C v)
    (hvs : ∀ w∈vs, C w) :
    (u++vs.flatten++z).IsPrefix (vs.flatten++v++tail) ↔
      AdjacentCodewordControl.Linked (u::vs) (v++tail) ∧ z.IsPrefix tail := by
  constructor
  · intro h
    have hshort : (u++vs.flatten).IsPrefix (vs.flatten++(v++tail)) := by
      apply List.IsPrefix.trans (show (u++vs.flatten).IsPrefix
        (u++vs.flatten++z) from ⟨z,rfl⟩)
      simpa only [List.append_assoc] using h
    have hl := (AdjacentCodewordControl.linked_replay hc u hu vs hvs _).mpr hshort
    obtain ⟨he,hend⟩ := (AdjacentCodewordControl.linked_uniform hc u hu vs hvs _).mp hl
    have huv : u=v := PrefixCodeCapture.prefix_identifies hc hu hv hend
    have hrot := AdjacentCodewordControl.uniform_rotate u vs he
    have hz : z.IsPrefix tail := by
      rw [←huv, hrot] at h
      simp only [List.append_assoc] at h
      have h' := (List.prefix_append_right_inj vs.flatten).mp h
      exact (List.prefix_append_right_inj u).mp h'
    exact ⟨hl,hz⟩
  · rintro ⟨hl,hz⟩
    obtain ⟨he,hend⟩ := (AdjacentCodewordControl.linked_uniform hc u hu vs hvs _).mp hl
    have huv : u=v := PrefixCodeCapture.prefix_identifies hc hu hv hend
    rw [←huv,AdjacentCodewordControl.uniform_rotate u vs he]
    simp only [List.append_assoc]
    apply (List.prefix_append_right_inj vs.flatten).mpr
    exact (List.prefix_append_right_inj u).mpr hz

private theorem replay_success_iff (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (w rest : List Char) (k p : Nat) (hp : p≤x.length)
    (hi : sfx x p=block k++rest) :
    (∃ q, evV g x s T [w] (.seq scanner (.param 0)) p=some (some q)) ↔
      w.IsPrefix rest := by
  have hscan := PrefixCodeCapture.scanner_at g x s T [w] p k rest hp hi
  have hr : sfx x rest.length=rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨block k,hi⟩).choose_spec
  rw [evV_seq_ok hscan]
  change (∃ q, (match Shallot.stripPrefix? w (sfx x rest.length) with
    | some t => some (some t.length) | none => some none)=some (some q)) ↔ _
  rw [hr]
  cases he : Shallot.stripPrefix? w rest with
  | none =>
    constructor
    · rintro ⟨q,hq⟩; cases hq
    · rintro ⟨t,ht⟩
      have hh := (CBVtoCBN.stripPrefix_exact w rest t).mpr ht.symm
      rw [he] at hh; cases hh
  | some t =>
    exact ⟨fun _ => ⟨t,((CBVtoCBN.stripPrefix_exact _ _ _).mp he).symm⟩,
      fun _ => ⟨t.length,rfl⟩⟩

/-- Exact success/failure criterion for the original whole replay, at
any complete-word trace followed by an independently selected a-fragment.
The fragment can be strictly shorter than the terminal run. Its length
and the number and lengths of words are unbounded. -/
theorem trace_replay_iff (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (ws : List (List Char)) (l r p : Nat) (tail : List Char) (hp : p≤x.length)
    (hw : ∀ w∈ws, ∃ k, w=block k)
    (hi : sfx x p=ws.flatten++List.replicate l 'a'++List.replicate r 'a'++'#'::tail) :
    (∃ q, evV g x s T [ws.flatten++List.replicate l 'a']
      (.seq scanner (.param 0)) p=some (some q)) ↔
      AdjacentCodewordControl.Linked ws (block (l+r)++tail) ∧
        (List.replicate l 'a').IsPrefix tail := by
  have hjoin : List.replicate l 'a'++List.replicate r 'a'++'#'::tail=
      block (l+r)++tail := by
    simp only [block,←List.replicate_append_replicate,List.append_assoc,List.singleton_append]
  cases ws with
  | nil =>
    simp only [List.flatten_nil,List.nil_append] at hi ⊢
    rw [hjoin] at hi
    simpa [AdjacentCodewordControl.Linked] using
      replay_success_iff g x s T (List.replicate l 'a') tail (l+r) p hp hi
  | cons u vs =>
    obtain ⟨k,rfl⟩ := hw u (by simp)
    have hinput : sfx x p=block k++(vs.flatten++(block (l+r)++tail)) := by
      simp only [List.flatten_cons,List.append_assoc] at hi
      have hj := hjoin
      simp only [List.append_assoc] at hj
      rw [hj] at hi
      exact hi
    rw [replay_success_iff g x s T _ _ k p hp hinput]
    simpa only [List.flatten_cons,List.append_assoc] using
      linked_fragment_iff PrefixCodeCapture.delimited_prefixFree (block k) (block (l+r))
        (List.replicate l 'a') tail vs ⟨k,rfl⟩ ⟨l+r,rfl⟩
        (fun w h => hw w (by simp [h]))

/-- The helper starts at the real capture endpoint, scans the remaining
part of the a-run and delimiter, then replays the retained fragment. -/
def tailBody : MExp := .seq scanner (.param 0)

/-- On a successful actual fragment capture, an ordinary Seq helper
checks precisely the bytes after the rest of the terminal codeword.
H can read caller values, recurse, or have other results on other inputs.
No substitute greedy capture is used for H. -/
theorem physical_tail_compare (g : MGrammar) (x : List Char) (i m : Nat)
    (hr : ruleAtM g.rules i=some ⟨1,tailBody⟩)
    (E : List (List Char)) (H : MExp) (p q r : Nat) (tail : List Char)
    (hp : p≤x.length)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E H p=
      some (some q))
    (hs : sfx x q=List.replicate r 'a'++'#'::tail) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (look (.call i [H])) p=
      if (pre x p q).IsPrefix tail then some (some p) else some none := by
  have hq := evV_ok (tblV_ok g x .callByValueSeq (m+1)) H p hp q ha
  have hscan := PrefixCodeCapture.scanner_at g x .callByValueSeq
    (tblV g x .callByValueSeq m) [pre x p q] q r tail hq (by simpa [block,List.append_assoc] using hs)
  have ht : sfx x tail.length=tail :=
    sfx_suffix (suffix_trans (sfx_is_suffix x q)
      ⟨block r,by simpa [block,List.append_assoc] using hs⟩).choose_spec
  change evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
    (.andP (.call i [H])) p=_
  rw [CallLookahead.evV_peek,evV_call_seq hr rfl]
  simp only [evSeqArgs,ha]
  rw [valAt_tblV_succ hr _ hq]
  rw [tailBody,evV_seq_ok hscan]
  change CallLookahead.peek p
    (match Shallot.stripPrefix? (pre x p q) (sfx x tail.length) with
      | some rest => some (some rest.length) | none => some none)=_
  rw [ht]
  cases hh : Shallot.stripPrefix? (pre x p q) tail with
  | none =>
    have hn : ¬(pre x p q).IsPrefix tail := by
      rintro ⟨rest,he⟩
      have hv := (CBVtoCBN.stripPrefix_exact (pre x p q) _ rest).mpr he.symm
      rw [hh] at hv; cases hv
    simp only [if_neg hn,CallLookahead.peek]
  | some rest =>
    have hy : (pre x p q).IsPrefix tail :=
      ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm⟩
    simp only [if_pos hy,CallLookahead.peek]

/-- The same source capture is held in three consecutive, real Seq
arguments. All argument expressions see the unchanged caller E. -/
theorem split_arguments (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (G H : MExp) (hH : H.FirstOrder)
    (p k j q : Nat) (rest : List Char) (hp : p≤x.length)
    (hi : sfx x p=block k++rest)
    (hg : evV g x s T E (look (.seq scanner G)) rest.length=some (some rest.length))
    (ht : evV g x s T E (.star (ControlledPartialCapture.step G)) rest.length=some (some j))
    (hh : evV g x s T E H j=some (some q)) :
    evV g x s T E (argument G H) p=some (some q) ∧
    evSeqArgs g x s T E [runA,.seq (.lit ['#']) (.star (ControlledPartialCapture.step G)),H] p=
      some (some ([List.replicate k 'a',pre x ('#'::rest).length j,pre x j q],q)) ∧
    List.replicate k 'a'++pre x ('#'::rest).length j++pre x j q=pre x p q := by
  have hi' : sfx x p=List.replicate k 'a'++'#'::rest := by
    simpa [block,List.append_assoc] using hi
  have hlen := congrArg List.length hi'
  rw [length_sfx x hp] at hlen
  have hsmall : rest.length<p := by
    simp only [List.length_append,List.length_replicate,List.length_cons] at hlen
    omega
  have hcut : ('#'::rest).length≤p := by
    simp only [List.length_append,List.length_replicate,List.length_cons] at hlen ⊢
    omega
  have hj : j≤rest.length := evStar_le rest.length j ht
  have hfrag := WordStarFilter.success_prefix hs hT E H hH j q (by omega) hh
  have hql : q≤j := by
    have he := congrArg List.length hfrag.2
    rw [length_sfx x (by omega : j≤x.length),List.length_append,length_sfx x hfrag.1] at he
    omega
  have hrun := PartialCodewordCapture.run_at g x s T E k p '#' rest (by decide) hp hi'
  have hscan := PrefixCodeCapture.scanner_at g x s T E p k rest hp hi
  have hstep : evV g x s T E (ControlledPartialCapture.step G) p=some (some rest.length) := by
    rw [ControlledPartialCapture.step,evV_seq_ok hscan]; exact hg
  have hstar : evV g x s T E (.star (ControlledPartialCapture.step G)) p=some (some j) := by
    change evStar (fun z => evV g x s T E (ControlledPartialCapture.step G) z) p=_
    rw [evStar_ok hstep hsmall]; exact ht
  have hsf : sfx x ('#'::rest).length='#'::rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨List.replicate k 'a',hi'⟩).choose_spec
  have hhash := LastCodewordCandidate.literal_at g x s T E ['#'] rest _ hsf
  have hmiddle : evV g x s T E (.seq (.lit ['#'])
      (.star (ControlledPartialCapture.step G))) ('#'::rest).length=some (some j) := by
    rw [evV_seq_ok hhash]; exact ht
  have hfirst : pre x p ('#'::rest).length=List.replicate k 'a' := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hi'
  refine ⟨by rw [argument,evV_seq_ok hstar]; exact hh,?_,?_⟩
  · rw [evSeq_cons_ok hrun,evSeq_cons_ok hmiddle,evSeq_cons_ok hh]
    simp only [evSeqArgs,hfirst]
  · rw [ScannerFrontier.pre_concat x p ('#'::rest).length q hp hcut (by simp; omega),
      hfirst,ScannerFrontier.pre_concat x ('#'::rest).length j q (by omega) (by simp; omega) hql]
    simp only [List.append_assoc]

/-- Reconstructing a three-piece capture preserves every partial outcome
of any first-order continuation, including later recursive calls. -/
def wholeView (b : MExp) : MExp := MExp.subst [CaptureViews.prefixExpr 3] b

theorem wholeView_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u v z : List Char) (b : MExp) (hb : b.FirstOrder) (p : Nat) :
    evV g x s T [u,v,z] (wholeView b) p=evV g x s T [u++v++z] b p := by
  exact CaptureViews.body_view g x s T [u,v,z] [u++v++z] [3]
    (by simp) (by simp) b hb p

/-- The real Seq filter agrees with whole-capture replay on every actual
trace whose selected final fragment is a-only and whose remainder reaches
its delimiter. Neither the trace nor its word lengths are supplied as an
oracle: both are recovered from the original star execution. This local
bridge still assumes successful star/H executions and a terminal delimiter. -/
theorem physical_preflight_iff (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p j q l r : Nat) (E : List (List Char)) (G H : MExp) (hH : H.FirstOrder)
    (tail : List Char) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,tailBody⟩)
    (hstar : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (.star (ControlledPartialCapture.step G)) p=some (some j))
    (hh : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E H j=some (some q))
    (hz : pre x j q=List.replicate l 'a')
    (hr : sfx x q=List.replicate r 'a'++'#'::tail) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (preflight G H) p=some (some q) ↔
    ∃ z, evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p q] (.seq scanner (.param 0)) p=some (some z) := by
  let T := tblV g x .callByValueSeq (m+1)
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  have hT := tblV_sound (x := x) hg (by decide : Strategy.callByValueSeq≠.callByName) (m+1)
  have hj := evV_ok hOk _ p hp j hstar
  have hq := evV_ok hOk H j hj q hh
  have hA : scanner.FirstOrder := by
    simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
      MExp.FirstOrder,MExp.failAlways]
  obtain ⟨ws,hw,htrace,hfilter⟩ := AdjacentCodewordControl.success g x .callByValueSeq
    (by decide) T hT hOk scanner hA PrefixCodeCapture.delimited_prefixFree E (.call 0 [scanner])
    (fun p q hp ha => AdjacentCodewordControl.physical_compare g x 0 m r0 E scanner p q hp ha)
    (fun p q hp ha => by
      obtain ⟨k,hk⟩ := PartialCodewordClassification.scanner_shape g x .callByValueSeq T E p q hp ha
      exact ⟨k,by simpa only [length_sfx x hp,length_sfx x (evV_ok hOk _ p hp q ha)]
        using pre_eq (sfx_is_suffix x p) hk⟩)
    (ControlledPartialPreflight.control G) p j hp hstar
  have hfrag := (WordStarFilter.success_prefix (by decide) hT E H hH j q hj hh).2
  rw [hz] at hfrag
  have hfull : sfx x p=(ws.flatten++List.replicate l 'a')++sfx x q := by
    rw [htrace,hfrag,List.append_assoc]
  have hcap : pre x p q=ws.flatten++List.replicate l 'a' := by
    simpa only [length_sfx x hp,length_sfx x hq] using pre_eq (sfx_is_suffix x p) hfull
  have hi : sfx x p=ws.flatten++List.replicate l 'a'++List.replicate r 'a'++'#'::tail := by
    rw [hfull,hr]
    simp only [List.append_assoc]
  have hjinput : sfx x j=block (l+r)++tail := by
    rw [hfrag,hr]
    simp only [block,←List.replicate_append_replicate,List.append_assoc,List.singleton_append]
  have ha : evV g x .callByValueSeq T E (argument G H) p=some (some q) := by
    rw [argument,evV_seq_ok hstar]; exact hh
  have hlook : evV g x .callByValueSeq T E (look (argument G H)) p=some (some p) := by
    change evV g x .callByValueSeq T E (.andP (argument G H)) p=_
    rw [CallLookahead.evV_peek,ha]; rfl
  have hresult : evV g x .callByValueSeq T E (preflight G H) p=
      if AdjacentCodewordControl.Linked ws (block (l+r)++tail) ∧
        (List.replicate l 'a').IsPrefix tail then some (some q) else some none := by
    rw [preflight,evV_seq_ok hlook]
    change (match evV g x .callByValueSeq T E
        (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
          (ControlledPartialPreflight.control G)) p with
      | some (some z) => evV g x .callByValueSeq T E (.seq (look (.call 1 [H])) H) z
      | other => other)=_
    rw [hfilter,hjinput]
    by_cases hl : AdjacentCodewordControl.Linked ws (block (l+r)++tail)
    · rw [if_pos hl]
      change (match evV g x .callByValueSeq T E (look (.call 1 [H])) j with
        | some (some z) => evV g x .callByValueSeq T E H z | other => other)=_
      rw [physical_tail_compare g x 1 m r1 E H j q r tail hj hh hr,hz]
      by_cases ht : (List.replicate l 'a').IsPrefix tail
      · rw [if_pos ht,if_pos ⟨hl,ht⟩]
        exact hh
      · simp [hl,ht]
    · simp [hl]
  rw [hresult,hcap,trace_replay_iff g x .callByValueSeq T ws l r p tail hp hw hi]
  by_cases h : AdjacentCodewordControl.Linked ws (block (l+r)++tail) ∧
      (List.replicate l 'a').IsPrefix tail <;> simp [h]

end Shallot.MacroPeg.CBV.ControlledFragmentReplay
