import MacroPeg.CBV.ControlledFragmentPreflight
import MacroPeg.CBV.ControlledPartialEntry

/-! Call-entry bridges for syntax-selected final fragments. -/
namespace Shallot.MacroPeg.CBV.ControlledFragmentEntry
open ClockFreezing (Table)
open RuntimeShiftFilter (scanner block)
open PartialCodewordCapture (runA look)
open ControlledPartialCapture (step)
open ControlledFragmentReplay (argument preflight wholeView)
open ControlledFragmentPreflight (fragment)

def branches (ternary unary : Nat) (G H : MExp) : MExp :=
  .alt (.seq (look (step G)) (.call ternary [runA,.seq (.lit ['#']) (.star (step G)),H]))
    (.seq (.notP (step G)) (.call unary [H]))
def entry (ternary unary : Nat) (G J : MExp) : MExp :=
  .seq (look (preflight G (fragment J))) (branches ternary unary G (fragment J))

private theorem scanner_pure : ParserPrefixFusion.Pure scanner := by
  simp [scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
    MExp.failAlways,ParserPrefixFusion.Pure]

private theorem seq_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a b : MExp) (p q : Nat)
    (h : evV g x s T E (.seq a b) p=some (some q)) :
    ∃ j, evV g x s T E a p=some (some j) ∧ evV g x s T E b j=some (some q) := by
  cases ha : evV g x s T E a p with
  | none => rw [evV_seq_none ha] at h; cases h
  | some v => cases v with
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
  | some v => cases v with
    | none => simp [ha,CallLookahead.peek] at h
    | some j => simpa [ha,CallLookahead.peek] using h.symm

/-- Both stopping tests are related at the current caller clock. -/
theorem star_congr (g g' : MGrammar) (x : List Char) (s s' : Strategy)
    (T U : Table) (hT : OkTV x.length T) (E E' : List (List Char))
    (test test' : MExp)
    (ht : ∀ q, q≤x.length → evV g x s T E test q=evV g' x s' U E' test' q)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.star (step test)) p=evV g' x s' U E' (.star (step test')) p := by
  have hA := ParserPrefixFusion.pure_eval g g' x s s' T U E E' scanner scanner_pure
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
  exact evStar_congr p (fun q hq => hstep q (by omega))

theorem fragment_congr (g g' : MGrammar) (x : List Char) (s s' : Strategy)
    (T U : Table) (hT : OkTV x.length T) (E E' : List (List Char)) (J J' : MExp)
    (hJ : ∀ q, q≤x.length → evV g x s T E J q=evV g' x s' U E' J' q)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (fragment J) p=evV g' x s' U E' (fragment J') p := by
  apply evStar_congr p
  intro q hq
  have hc : evV g x s T E (.chr 'a') q=evV g' x s' U E' (.chr 'a') q := rfl
  change (match evV g x s T E (.chr 'a') q with
    | some (some j) => evV g x s T E (look J) j | other => other)=
    (match evV g' x s' U E' (.chr 'a') q with
    | some (some j) => evV g' x s' U E' (look J') j | other => other)
  rw [←hc]
  cases he : evV g x s T E (.chr 'a') q with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some j =>
      change evV g x s T E (.andP J) j=evV g' x s' U E' (.andP J') j
      rw [CallLookahead.evV_peek,CallLookahead.evV_peek,hJ j (evV_ok hT _ q (by omega) j he)]

theorem argument_congr (g g' : MGrammar) (x : List Char) (s s' : Strategy)
    (T U : Table) (hT : OkTV x.length T) (E E' : List (List Char)) (G G' J J' : MExp)
    (hG : ∀ q, q≤x.length → evV g x s T E G q=evV g' x s' U E' G' q)
    (hJ : ∀ q, q≤x.length → evV g x s T E J q=evV g' x s' U E' J' q)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (argument G (fragment J)) p=
      evV g' x s' U E' (argument G' (fragment J')) p := by
  have hstar := star_congr g g' x s s' T U hT E E' G G' hG p hp
  change (match evV g x s T E (.star (step G)) p with
    | some (some q) => evV g x s T E (fragment J) q | other => other)=
    (match evV g' x s' U E' (.star (step G')) p with
    | some (some q) => evV g' x s' U E' (fragment J') q | other => other)
  rw [←hstar]
  cases hs : evV g x s T E (.star (step G)) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q =>
      exact fragment_congr g g' x s s' T U hT E E' J J' hJ q
        (by have hle := evStar_le p q hs; omega)

/-- Both components are stars, so no finite argument failure can occur. -/
theorem argument_ne_fail (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (G J : MExp) (p : Nat) :
    evV g x s T E (argument G (fragment J)) p≠some none := by
  change (match evV g x s T E (.star (step G)) p with
    | some (some q) => evV g x s T E (fragment J) q | other => other)≠_
  cases hs : evV g x s T E (.star (step G)) p with
  | none => simp
  | some v => cases v with
    | none => exact False.elim (evStar_ne_fail p hs)
    | some q => exact evStar_ne_fail q

/-- The actual fragment's retained bytes fix the rotated replay endpoint.
No greedy final-run boundary or presumed equality of positions is used. -/
theorem endpoint_state (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p j a b : Nat) (E : List (List Char)) (G J : MExp) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (hs : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (.star (step G)) p=some (some j))
    (hh : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (fragment J) j=some (some a))
    (hb : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p a] (.seq scanner (.param 0)) p=some (some b)) :
    ∃ r, sfx x a=List.replicate r 'a'++'#'::(pre x j a++sfx x b) := by
  let T := tblV g x .callByValueSeq (m+1)
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  have hj := evV_ok hOk _ p hp j hs
  have ha := evV_ok hOk _ j hj a hh
  obtain ⟨l,hl,hfrag⟩ := ControlledFragmentPreflight.fragment_shape g x .callByValueSeq T E J j a hj hh
  obtain ⟨ws,hw,htrace,_⟩ := ControlledFragmentPreflight.star_trace g hg x m p j E G hp r0 hs
  have hi : sfx x p=(ws.flatten++List.replicate l 'a')++sfx x a := by
    rw [htrace,hfrag,List.append_assoc]
  have hcap : pre x p a=ws.flatten++List.replicate l 'a' := by
    simpa only [length_sfx x hp,length_sfx x ha] using pre_eq (sfx_is_suffix x p) hi
  have hb' := hb
  rw [hcap] at hb'
  obtain ⟨r,tail,hr⟩ := ControlledFragmentPreflight.terminal_of_replay g x .callByValueSeq T ws l p a b hp hw hi hb'
  have hi' : sfx x p=ws.flatten++List.replicate l 'a'++List.replicate r 'a'++'#'::tail := by
    rw [hi,hr]; simp only [List.append_assoc]
  have hchecks := (ControlledFragmentReplay.trace_replay_iff g x .callByValueSeq T ws l r p tail hp hw hi').mp ⟨b,hb'⟩
  have hterminal : (block (l+r)).IsPrefix (List.replicate l 'a'++sfx x a) := by
    refine ⟨tail,?_⟩
    rw [hr]
    simp only [block,←List.replicate_append_replicate,List.append_assoc,List.singleton_append]
  have hlinked : AdjacentCodewordControl.Linked ws (List.replicate l 'a'++sfx x a) := by
    simpa only [hr,block,←List.replicate_append_replicate,List.append_assoc,List.singleton_append] using hchecks.1
  have hws := ControlledPartialPreflight.linked_terminal_uniform PrefixCodeCapture.delimited_prefixFree
    (block (l+r)) ⟨l+r,rfl⟩ ws hw _ hlinked hterminal
  have hrotate := AdjacentCodewordControl.uniform_rotate (block (l+r)) ws hws
  have hinput : sfx x p=block (l+r)++(ws.flatten++tail) := by
    have hi'' : sfx x p=ws.flatten++block (l+r)++tail := by
      simpa only [block,←List.replicate_append_replicate,List.append_assoc,List.singleton_append] using hi'
    rw [hi'',←hrotate,List.append_assoc]
  have hscan := PrefixCodeCapture.scanner_at g x .callByValueSeq T [pre x p a] p (l+r) _ hp hinput
  rw [evV_seq_ok hscan] at hb
  have hsf : sfx x (ws.flatten++tail).length=ws.flatten++tail :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨block (l+r),hinput⟩).choose_spec
  have hout : ws.flatten++tail=(pre x p a)++sfx x b := by
    cases he : Shallot.stripPrefix? (pre x p a) (sfx x (ws.flatten++tail).length) with
    | none => simp only [evV,List.getElem?_cons_zero,he] at hb; cases hb
    | some rest =>
      have heq : rest.length=b := by simpa only [evV,List.getElem?_cons_zero,he,Option.some.injEq] using hb
      have hbytes := (CBVtoCBN.stripPrefix_exact _ _ _).mp he
      have hrest : sfx x rest.length=rest :=
        sfx_suffix (suffix_trans (sfx_is_suffix x (ws.flatten++tail).length) ⟨pre x p a,hbytes⟩).choose_spec
      rw [heq] at hrest
      rw [←hsf,hrest]
      exact hbytes
  have ht : tail=List.replicate l 'a'++sfx x b := by
    apply (List.append_right_inj ws.flatten).mp
    simpa [hcap,List.append_assoc] using hout
  exact ⟨r,by rw [hr,ht,hl]⟩

/-- Actual first-iteration success supplies the real three-piece capture
and the residual scanner/fragment at the same replay endpoint. -/
theorem positive_state (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p a b z : Nat) (E : List (List Char)) (G J : MExp) (hJ : J.FirstOrder)
    (hp : p≤x.length) (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument G (fragment J)) p=some (some a))
    (hb : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p a] (.seq scanner (.param 0)) p=some (some b))
    (hstep : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (step G) p=some (some z)) :
    ∃ u v w r, evSeqArgs g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
        [runA,.seq (.lit ['#']) (.star (step G)),fragment J] p=some (some ([u,v,w],a)) ∧
      u++v++w=pre x p a ∧ sfx x a=List.replicate r 'a'++'#'::(w++sfx x b) := by
  let T := tblV g x .callByValueSeq (m+1)
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  obtain ⟨j,hs,hh⟩ := seq_success g x .callByValueSeq T E _ _ p a ha
  obtain ⟨v,hscan,hguard⟩ := seq_success g x .callByValueSeq T E _ _ p z hstep
  have he : z=v := look_position g x .callByValueSeq T E _ v z hguard
  subst v
  have hz := evV_ok hOk _ p hp z hscan
  have hzp := (PartialCodewordTotality.scanner_total_strict g x .callByValueSeq T hOk E p hp).2 z hscan
  obtain ⟨k,hinput⟩ := PartialCodewordClassification.scanner_shape g x .callByValueSeq T E p z hp hscan
  have ht : evV g x .callByValueSeq T E (.star (step G)) z=some (some j) := by
    change evStar (fun q => evV g x .callByValueSeq T E (step G) q) p=_ at hs
    rw [evStar_ok hstep hzp] at hs; exact hs
  obtain ⟨_,hargs,hjoin⟩ := ControlledFragmentReplay.split_arguments g x .callByValueSeq
    (by decide) T (tblV_sound hg (by decide) (m+1)) E G (fragment J)
    (ControlledFragmentPreflight.fragment_firstOrder J hJ) p k j a (sfx x z) hp hinput
    (by simpa only [length_sfx x hz] using hguard)
    (by simpa only [length_sfx x hz] using ht) hh
  obtain ⟨r,hr⟩ := endpoint_state g hg x m p j a b E G J hp r0 hs hh hb
  exact ⟨List.replicate k 'a',pre x ('#'::sfx x z).length j,pre x j a,r,hargs,hjoin,hr⟩

private theorem replay_body (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (i : Nat) (w : List Char) (hi : E[i]?=some w)
    (a b r : Nat) (ha : a≤x.length) (hb : b≤x.length)
    (hs : sfx x a=List.replicate r 'a'++'#'::(w++sfx x b)) (e : MExp) :
    evV g x s T E (.seq scanner (.seq (.param i) e)) a=evV g x s T E e b := by
  have hscan := PrefixCodeCapture.scanner_at g x s T E a r (w++sfx x b) ha
    (by simpa [block,List.append_assoc] using hs)
  have hrest : sfx x (w++sfx x b).length=w++sfx x b :=
    sfx_suffix (suffix_trans (sfx_is_suffix x a)
      ⟨block r,by simpa [block,List.append_assoc] using hs⟩).choose_spec
  have hparam : evV g x s T E (.param i) (w++sfx x b).length=some (some b) := by
    have h := LastCodewordCandidate.literal_at g x s T E w (sfx x b) _ hrest
    simpa only [evV,hi,length_sfx x hb] using h
  rw [evV_seq_ok hscan,evV_seq_ok hparam]

/-- The branch guards commit to the original first iteration. Every
partial outcome of the real callee continuation is preserved. -/
theorem branches_eq (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m ternary unary p a b : Nat) (E : List (List Char)) (G J e : MExp)
    (hJ : J.FirstOrder) (he : e.FirstOrder) (hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (rt : ruleAtM g.rules ternary=some ⟨3,.seq scanner (.seq (.param 2) (wholeView e))⟩)
    (ru : ruleAtM g.rules unary=some ⟨1,.seq scanner (.seq (.param 0) e)⟩)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (argument G (fragment J)) p=some (some a))
    (hb : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
      [pre x p a] (.seq scanner (.param 0)) p=some (some b)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (branches ternary unary G (fragment J)) p=
    evV g x .callByValueSeq (tblV g x .callByValueSeq m) [pre x p a] e b := by
  let T := tblV g x .callByValueSeq (m+1)
  have hOk := tblV_ok g x .callByValueSeq (m+1)
  have hal := evV_ok hOk _ p hp a ha
  have hbl := evV_ok hOk _ p hp b hb
  obtain ⟨j,hs,hh⟩ := seq_success g x .callByValueSeq T E _ _ p a ha
  cases hstep : evV g x .callByValueSeq T E (step G) p with
  | none =>
    have hn : evV g x .callByValueSeq T E (.star (step G)) p=none := evStar_none hstep
    rw [hs] at hn; cases hn
  | some v => cases v with
    | none =>
      have hstar : evV g x .callByValueSeq T E (.star (step G)) p=some (some p) := evStar_fail hstep
      have hj : j=p := by rw [hstar] at hs; simpa using hs.symm
      subst j
      obtain ⟨r,hr⟩ := endpoint_state g hg x m p p a b E G J hp r0 hs hh hb
      have hcall : evV g x .callByValueSeq T E (.call unary [fragment J]) p=
          evV g x .callByValueSeq (tblV g x .callByValueSeq m) [pre x p a] e b := by
        rw [evV_call_seq ru rfl]
        simp only [evSeqArgs,hh]
        dsimp only [T]
        rw [valAt_tblV_succ ru _ hal]
        exact replay_body g x .callByValueSeq _ _ 0 _ rfl a b r hal hbl hr e
      have hlo : evV g x .callByValueSeq T E (look (step G)) p=some none := by
        change evV g x .callByValueSeq T E (.andP (step G)) p=_
        rw [CallLookahead.evV_peek,hstep]; rfl
      rw [branches,evV_alt_fail (evV_seq_fail hlo),evV_seq_ok (evV_not_fail hstep)]
      exact hcall
    | some z =>
      obtain ⟨u,v,w,r,hargs,hjoin,hr⟩ := positive_state g hg x m p a b z E G J hJ hp r0 ha hb hstep
      have hcall : evV g x .callByValueSeq T E
          (.call ternary [runA,.seq (.lit ['#']) (.star (step G)),fragment J]) p=
          evV g x .callByValueSeq (tblV g x .callByValueSeq m) [pre x p a] e b := by
        rw [evV_call_seq rt rfl,hargs]
        dsimp only [T]
        rw [valAt_tblV_succ rt _ hal,
          replay_body g x .callByValueSeq _ [u,v,w] 2 w rfl a b r hal hbl hr,
          ControlledFragmentReplay.wholeView_eval g x .callByValueSeq _ u v w e he,hjoin]
      have hlo := look_ok g x .callByValueSeq T E _ p z hstep
      have hno : evV g x .callByValueSeq T E
          (.seq (.notP (step G)) (.call unary [fragment J])) p=some none :=
        evV_seq_fail (evV_not_ok hstep)
      change (match evV g x .callByValueSeq T E
          (.seq (look (step G))
            (.call ternary [runA,.seq (.lit ['#']) (.star (step G)),fragment J])) p with
        | some none => evV g x .callByValueSeq T E
            (.seq (.notP (step G)) (.call unary [fragment J])) p | other => other)=_
      rw [evV_seq_ok hlo,hno,←hcall]
      cases evV g x .callByValueSeq T E
          (.call ternary [runA,.seq (.lit ['#']) (.star (step G)),fragment J]) p with
      | none => rfl
      | some v => cases v <;> rfl

theorem entry_firstOrder (ternary unary : Nat) (G J : MExp)
    (hG : G.FirstOrder) (hJ : J.FirstOrder) : (entry ternary unary G J).FirstOrder := by
  simp [entry,branches,preflight,argument,fragment,step,look,scanner,runA,
    NestedScannerArguments.scan,NestedScannerArguments.choice,
    AdjacentCodewordControl.filter,ControlledPartialPreflight.control,CodewordControlFilter.render,
    MExp.FirstOrder,MExp.FirstOrderArgs,MExp.failAlways,MExp.andP,hG,hJ]

/-- Complete partial call transfer with both stopping tests at the current
caller clock and the callee continuation at the previous clock. -/
theorem transfer (g g' : MGrammar) (hg' : g'.FirstOrder) (x : List Char)
    (m m' i ternary unary p : Nat) (E E' : List (List Char))
    (G G' J J' b b' : MExp) (hJ' : J'.FirstOrder) (hb' : b'.FirstOrder)
    (hp : p≤x.length)
    (sourceRule : ruleAtM g.rules i=some ⟨1,.seq scanner (.seq (.param 0) b)⟩)
    (r0 : ruleAtM g'.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g'.rules 1=some ⟨1,ControlledFragmentReplay.tailBody⟩)
    (ternaryRule : ruleAtM g'.rules ternary=some ⟨3,.seq scanner (.seq (.param 2) (wholeView b'))⟩)
    (unaryRule : ruleAtM g'.rules unary=some ⟨1,.seq scanner (.seq (.param 0) b')⟩)
    (hG : ∀ q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar (m+1)) E G q=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E' G' q)
    (hJ : ∀ q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar (m+1)) E J q=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E' J' q)
    (hcont : ∀ w q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar m) [w] b q=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq m') [w] b' q) :
    evV g x .callByValuePar (tblV g x .callByValuePar (m+1)) E
      (.call i [argument G (fragment J)]) p=
    evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
      (entry ternary unary G' J') p := by
  let T := tblV g x .callByValuePar (m+1)
  let U := tblV g' x .callByValueSeq (m'+1)
  have harg := argument_congr g g' x .callByValuePar .callByValueSeq T U
    (tblV_ok g x .callByValuePar (m+1)) E E' G G' J J' hG hJ p hp
  cases ha : evV g x .callByValuePar T E (argument G (fragment J)) p with
  | none =>
    have ha' := harg.symm.trans ha
    have hf := ControlledFragmentReplay.preflight_none g' x .callByValueSeq U E' G' _ p ha'
    have hlo : evV g' x .callByValueSeq U E' (look (preflight G' (fragment J'))) p=none := by
      change evV g' x .callByValueSeq U E' (.andP (preflight G' (fragment J'))) p=_
      rw [CallLookahead.evV_peek,hf]; rfl
    rw [evV_call_par sourceRule rfl (by decide)]
    simp only [evParArgs,show evV g x .callByValuePar
      (tblV g x .callByValuePar (m+1)) E (argument G (fragment J)) p=none from ha]
    rw [entry,evV_seq_none hlo]
  | some v => cases v with
    | none => exact False.elim (argument_ne_fail g x .callByValuePar T E G J p ha)
    | some a =>
      have ha' := harg.symm.trans ha
      have hsource : evV g x .callByValuePar T E (.call i [argument G (fragment J)]) p=
          evV g x .callByValuePar (tblV g x .callByValuePar m) [pre x p a]
            (.seq scanner (.seq (.param 0) b)) p := by
        rw [evV_call_par sourceRule rfl (by decide)]
        simp only [evParArgs,ha]
        dsimp only [T]
        rw [valAt_tblV_succ sourceRule _ hp]
      rw [hsource,←LeadingReplayStar.sequence_assoc g x .callByValuePar _ _ scanner (.param 0) b p]
      have hprefixeq := LastCodewordGrammar.syntax_eval g g' x .callByValuePar .callByValueSeq
        (tblV g x .callByValuePar m) U (tblV_ok g x .callByValuePar m) [pre x p a]
        (.seq scanner (.param 0)) ⟨LastCodewordGrammar.pure_syntax scanner scanner_pure,True.intro⟩ p hp
      have hfilter := ControlledFragmentPreflight.physical_result g' hg' x m' p E' G' J' hJ' hp r0 r1
      rw [ha'] at hfilter
      obtain ⟨v,hv⟩ := PartialCodewordTotality.prefix_total g x .callByValuePar _
        (tblV_ok g x .callByValuePar m) (pre x p a) p hp
      have hv' := hprefixeq.symm.trans hv
      dsimp only [] at hfilter
      rw [hv'] at hfilter
      cases v with
      | none =>
        have hlo : evV g' x .callByValueSeq U E' (look (preflight G' (fragment J'))) p=some none := by
          change evV g' x .callByValueSeq U E' (.andP (preflight G' (fragment J'))) p=_
          rw [CallLookahead.evV_peek,hfilter]; rfl
        rw [evV_seq_fail hv,entry,evV_seq_fail hlo]
      | some bpos =>
        have hpos := evV_ok (tblV_ok g x .callByValuePar m) _ p hp bpos hv
        have hlo := look_ok g' x .callByValueSeq U E' _ p a hfilter
        rw [evV_seq_ok hv,hcont _ bpos hpos,entry,evV_seq_ok hlo]
        exact (branches_eq g' hg' x m' ternary unary p a bpos E' G' J' b'
          hJ' hb' hp r0 ternaryRule unaryRule ha' hv').symm
/-- Physical clock-zero helpers have no rows. This seed preserves both
recursive tests before any later positive-clock comparison is available. -/
theorem preflight_zero (g : MGrammar) (x : List Char) (E : List (List Char))
    (G J : MExp) (p : Nat) (_hp : p≤x.length)
    (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,ControlledFragmentReplay.tailBody⟩) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq 0) E (preflight G (fragment J)) p=none := by
  let T := tblV g x .callByValueSeq 0
  cases ha : evV g x .callByValueSeq T E (argument G (fragment J)) p with
  | none => exact ControlledFragmentReplay.preflight_none g x .callByValueSeq T E G _ p ha
  | some r => cases r with
    | none => exact False.elim (argument_ne_fail g x .callByValueSeq T E G J p ha)
    | some j =>
      obtain ⟨z,hstar,hfrag⟩ := seq_success g x .callByValueSeq T E _ _ p j ha
      have hlo := look_ok g x .callByValueSeq T E _ p j ha
      rw [preflight,evV_seq_ok hlo]
      let d : CodewordControlFilter.Expr := .seq .token (.test (.seq scanner G))
      let f := AdjacentCodewordControl.filter scanner (.call 0 [scanner]) d
      have hfstar : evV g x .callByValueSeq T E
          (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
            (ControlledPartialPreflight.control G)) p=
          evV g x .callByValueSeq T E (.seq (.star f) (.notP (step G))) p := by
        change evV g x .callByValueSeq T E
          (.seq (look (.star (step G))) (.seq (.star f) (.notP (step G)))) p=_
        rw [evV_seq_ok (look_ok g x .callByValueSeq T E _ p z hstar)]
      cases hstep : evV g x .callByValueSeq T E (step G) p with
      | none =>
        have hn : evV g x .callByValueSeq T E (.star (step G)) p=none := evStar_none hstep
        rw [hstar] at hn; cases hn
      | some r => cases r with
        | none =>
          have hf : evV g x .callByValueSeq T E f p=some none :=
            AdjacentCodewordControl.filter_fail g x .callByValueSeq T E scanner (.call 0 [scanner]) d p hstep
          have hfst : evV g x .callByValueSeq T E (.star f) p=some (some p) := evStar_fail hf
          have hfilter : evV g x .callByValueSeq T E
              (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
                (ControlledPartialPreflight.control G)) p=some (some p) := by
            rw [hfstar,evV_seq_ok hfst]; exact evV_not_fail hstep
          rw [evV_seq_ok hfilter]
          have hstart : z=p := by
            have hs : evV g x .callByValueSeq T E (.star (step G)) p=some (some p) := evStar_fail hstep
            rw [hs] at hstar; simpa using hstar.symm
          subst z
          have hc : evV g x .callByValueSeq T E (.call 1 [fragment J]) p=none := by
            rw [evV_call_seq r1 rfl]
            simp only [evSeqArgs,hfrag]
            simp only [T,tblV,valAt_nil]
          apply evV_seq_none
          change evV g x .callByValueSeq T E (.andP (.call 1 [fragment J])) p=none
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
              (.seq (look (step G))
                (.seq (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) .token)
                  (AdjacentCodewordControl.filter scanner (.call 0 [scanner]) (.test (.seq scanner G))))) p=none
            rw [evV_seq_ok (look_ok g x .callByValueSeq T E _ p q hstep),evV_seq_none htoken]
          have hfst : evV g x .callByValueSeq T E (.star f) p=none := evStar_none hf
          have hfilter : evV g x .callByValueSeq T E
              (AdjacentCodewordControl.filter scanner (.call 0 [scanner])
                (ControlledPartialPreflight.control G)) p=none := by
            rw [hfstar,evV_seq_none hfst]
          exact evV_seq_none hfilter
theorem zero (g g' : MGrammar) (x : List Char) (i ternary unary p : Nat)
    (E E' : List (List Char)) (G G' J J' b : MExp) (hp : p≤x.length)
    (sourceRule : ruleAtM g.rules i=some ⟨1,.seq scanner (.seq (.param 0) b)⟩)
    (r0 : ruleAtM g'.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g'.rules 1=some ⟨1,ControlledFragmentReplay.tailBody⟩) :
    evV g x .callByValuePar (tblV g x .callByValuePar 0) E
      (.call i [argument G (fragment J)]) p=
    evV g' x .callByValueSeq (tblV g' x .callByValueSeq 0) E'
      (entry ternary unary G' J') p := by
  have hs : evV g x .callByValuePar (tblV g x .callByValuePar 0) E
      (.call i [argument G (fragment J)]) p=none := by
    rw [evV_call_par sourceRule rfl (by decide)]
    cases ha : evV g x .callByValuePar (tblV g x .callByValuePar 0) E
        (argument G (fragment J)) p with
    | none => simp only [evParArgs,ha]
    | some v => cases v with
      | none => exact False.elim (argument_ne_fail g x .callByValuePar _ E G J p ha)
      | some j =>
        simp only [evParArgs,ha]
        simp only [tblV,valAt_nil]
  rw [hs,entry]
  symm
  apply evV_seq_none
  change evV g' x .callByValueSeq (tblV g' x .callByValueSeq 0) E'
    (.andP (preflight G' (fragment J'))) p=none
  rw [CallLookahead.evV_peek,preflight_zero g' x E' G' J' p hp r0 r1]; rfl

end Shallot.MacroPeg.CBV.ControlledFragmentEntry
