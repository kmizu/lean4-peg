import MacroPeg.CBV.RuntimeShiftFilter
import MacroPeg.CBV.WordArguments

/-! Retain a runtime codeword rather than a finite phase. A two-codeword
capture can be represented by duplication after a successful shifted replay.
This is a capture representation and local entry lemma; it does not yet
compile arbitrary argument parsers or change the recursive table's strategy. -/
namespace Shallot.MacroPeg.CBV.PrefixCodeCapture
open ClockFreezing (Table)

def PrefixFree (C : List Char → Prop) : Prop :=
  ∀ u v, C u → C v → u.IsPrefix v → u=v

/-- A complete codeword at the start of the remaining input rules out a
different codeword, regardless of what follows it. -/
theorem prefix_identifies {C : List Char → Prop} (hc : PrefixFree C)
    {u v rest : List Char} (hu : C u) (hv : C v) (h : u.IsPrefix (v++rest)) : u=v := by
  by_cases hl : u.length≤v.length
  · exact hc u v hu hv (List.prefix_of_prefix_length_le h ⟨rest,rfl⟩ hl)
  · exact (hc v u hv hu (List.prefix_of_prefix_length_le ⟨rest,rfl⟩ h (by omega))).symm

/-- The overlap equation for two complete codewords collapses them to a
single runtime word. Neither the code nor its words need be finite. -/
theorem two_word_overlap {C : List Char → Prop} (hc : PrefixFree C)
    {u v : List Char} (hu : C u) (hv : C v)
    (h : (u++v).IsPrefix (u++(u++v))) : u=v := by
  have hh : v.IsPrefix (u++v) := (List.prefix_append_right_inj u).mp h
  exact (prefix_identifies hc hv hu hh).symm

def duplicate : MExp := .seq (.param 0) (.param 0)
def view (b : MExp) : MExp := MExp.subst [duplicate] b

/-- All first-order uses of the old capture, including arguments passed to
recursive rows, can be rebound to a duplicated smaller capture. -/
theorem view_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u : List Char) (b : MExp) (hb : b.FirstOrder) (p : Nat) :
    evV g x s T [u] (view b) p=evV g x s T [u++u] b p := by
  apply CaptureViews.evV_rebind [duplicate] [u++u] _ b hb p
  intro k q
  cases k with
  | zero =>
    change evV g x s T [u] duplicate q=evV g x s T [u++u] (.param 0) q
    rw [WordArguments.word_eval g x s T [u] duplicate ⟨True.intro,True.intro⟩ q]
    rfl
  | succ k => simp [MExp.subst,argAt,evV,MExp.failAlways]

/-- Once the first codeword has been consumed, matching the original
two-word capture and using it later is exactly matching the retained first
word twice and using its duplicated view. Failure and undefined tails agree. -/
theorem collapse (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    {C : List Char → Prop} (hc : PrefixFree C) (u v rest : List Char)
    (hu : C u) (hv : C v) (p : Nat) (hs : sfx x p=v++rest)
    (b : MExp) (hb : b.FirstOrder) :
    evV g x s T [u++v] (.seq (.param 0) b) p=
      evV g x s T [u] (.seq duplicate (view b)) p := by
  by_cases he : u=v
  · subst v
    have hd : evV g x s T [u] duplicate p=evV g x s T [u++u] (.param 0) p := by
      rw [WordArguments.word_eval g x s T [u] duplicate ⟨True.intro,True.intro⟩ p]
      rfl
    change (match evV g x s T [u++u] (.param 0) p with
      | some (some q) => evV g x s T [u++u] b q | other => other)=
      (match evV g x s T [u] duplicate p with
      | some (some q) => evV g x s T [u] (view b) q | other => other)
    rw [hd]
    cases evV g x s T [u++u] (.param 0) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some q => exact (view_eval g x s T u b hb q).symm
  · have hstrip : Shallot.stripPrefix? u (v++rest)=none := by
      cases h : Shallot.stripPrefix? u (v++rest) with
      | none => rfl
      | some r =>
        exact False.elim (he (prefix_identifies hc hu hv
          ⟨r,((CBVtoCBN.stripPrefix_exact _ _ _).mp h).symm⟩))
    have hlong : Shallot.stripPrefix? (u++v) (v++rest)=none := by
      cases h : Shallot.stripPrefix? (u++v) (v++rest) with
      | none => rfl
      | some r =>
        have hp : u.IsPrefix (v++rest) := ⟨v++r,by
          simpa [List.append_assoc] using ((CBVtoCBN.stripPrefix_exact _ _ _).mp h).symm⟩
        exact False.elim (he (prefix_identifies hc hu hv hp))
    simp [evV,duplicate,hs,hstrip,hlong]

/-- An arbitrary actual argument, including dependent recursive arguments,
supplies the overlap premise. The only shape premise is that its selected
capture consists of these two complete codewords. -/
theorem actual_capture (g : MGrammar) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (E : List (List Char))
    (a head : MExp) (ha : a.FirstOrder) (hh : head.FirstOrder)
    {C : List Char → Prop} (hc : PrefixFree C) (u v : List Char) (hu : C u) (hv : C v)
    (p q j z : Nat) (hp : p≤x.length)
    (harg : evV g x .callByValuePar T E a p=some (some q))
    (hcap : pre x p q=u++v)
    (hhead : evV g x .callByValuePar T [pre x p q] head p=some (some j))
    (hword : pre x p j=u)
    (hreplay : evV g x .callByValuePar T [pre x p q] (.seq head (.param 0)) p=some (some z)) :
    u=v ∧ pre x p q=u++u := by
  have hfirst := (ReplayFusion.success_prefix hT E a ha p q hp harg).2
  have hmiddle := ReplayFusion.success_prefix hT [pre x p q] head hh p j hp hhead
  rw [evV_seq_ok hhead] at hreplay
  have hlast := (ReplayFusion.success_prefix hT [pre x p q] (.param 0) True.intro j z hmiddle.1 hreplay).2
  have hvalue := WordArguments.value_of_success g x .callByValuePar T [pre x p q]
    (.param 0) True.intro j z hmiddle.1 hreplay
  have hw : pre x j z=pre x p q := by
    simpa only [WordArguments.value,List.getElem?_cons_zero,Option.some.injEq] using hvalue.symm
  rw [hw] at hlast
  have hwhole : sfx x p=(u++pre x p q)++sfx x z := by
    rw [hmiddle.2,hword,hlast,List.append_assoc]
  obtain ⟨r,_,hr⟩ := OverlapNecessity.common_input_rotation u (pre x p q)
    (sfx x p) (sfx x q) (sfx x z) hfirst hwhole
  have ho : (u++v).IsPrefix (u++(u++v)) := by
    rw [hcap] at hr
    exact ⟨r,hr.symm⟩
  have he := two_word_overlap hc hu hv ho
  exact ⟨he,by simpa only [←he] using hcap⟩

/-- At an actual call, replace the body entry by the shorter retained
codeword. Unlike `actual_capture`, this identity also covers replay failure
and undefined continuations; no successful final replay is assumed. -/
theorem actual_entry (g : MGrammar) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (E : List (List Char)) (a head b : MExp)
    (ha : a.FirstOrder) (hh : head.FirstOrder) (hb : b.FirstOrder)
    {C : List Char → Prop} (hc : PrefixFree C) (u v : List Char) (hu : C u) (hv : C v)
    (p q j : Nat) (hp : p≤x.length)
    (harg : evV g x .callByValuePar T E a p=some (some q)) (hcap : pre x p q=u++v)
    (hhead : evV g x .callByValuePar T [pre x p q] head p=some (some j))
    (hword : pre x p j=u) :
    evV g x .callByValuePar T [pre x p q] (.seq head (.seq (.param 0) b)) p=
      evV g x .callByValuePar T [u] (.seq duplicate (view b)) j := by
  have hfirst := (ReplayFusion.success_prefix hT E a ha p q hp harg).2
  have hmiddle := (ReplayFusion.success_prefix hT [pre x p q] head hh p j hp hhead).2
  have hs : sfx x j=v++sfx x q := by
    rw [hcap] at hfirst
    rw [hword] at hmiddle
    apply (List.append_right_inj u).mp
    simpa only [List.append_assoc] using hmiddle.symm.trans hfirst
  rw [evV_seq_ok hhead,hcap]
  exact collapse g x .callByValuePar T hc u v _ hu hv j hs b hb

theorem delimited_prefixFree : PrefixFree (fun w => ∃ n, w=RuntimeShiftFilter.block n) := by
  rintro u v ⟨n,rfl⟩ ⟨m,rfl⟩ hp
  have he : n=m := (RuntimeShiftFilter.block_prefix n m []).mp (by simpa using hp)
  rw [he]

/-- The concrete runtime header works at every physical suffix, including
inside an argument that has already consumed earlier input. -/
theorem scanner_at (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p n : Nat) (rest : List Char) (hp : p≤x.length)
    (hs : sfx x p=RuntimeShiftFilter.block n++rest) :
    evV g x s T E RuntimeShiftFilter.scanner p=some (some rest.length) := by
  have hd : (RuntimeShiftFilter.block n++rest).dropWhile (NestedScannerArguments.accepts ['a'])='#'::rest := by
    induction n with
    | zero => simp [RuntimeShiftFilter.block,NestedScannerArguments.accepts,Shallot.beqChar]
    | succ n ih => simp [RuntimeShiftFilter.block,List.replicate_succ,NestedScannerArguments.accepts,Shallot.beqChar] at *
  rw [RuntimeShiftFilter.scanner,evV_seq_ok (by
    rw [NestedScannerArguments.scan_eval g x s T E ['a'] p hp,hs,hd])]
  have hpre : sfx x p=List.replicate n 'a'++('#'::rest) := by
    simpa [RuntimeShiftFilter.block,List.append_assoc] using hs
  have hxs := suffix_trans (sfx_is_suffix x p) ⟨List.replicate n 'a',hpre⟩
  simp only [evV,sfx_suffix hxs.choose_spec]
  rfl

/-- A concrete two-header argument crosses the scanner frontier, and its
actual capture can be compressed at body entry for all header lengths and
all first-order continuations. Unequal headers give matching failure. -/
theorem two_header_entry (g : MGrammar) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (E : List (List Char))
    (p n m : Nat) (rest : List Char) (hp : p≤x.length)
    (hs : sfx x p=RuntimeShiftFilter.block n++(RuntimeShiftFilter.block m++rest))
    (b : MExp) (hb : b.FirstOrder) :
    evV g x .callByValuePar T [RuntimeShiftFilter.block n++RuntimeShiftFilter.block m]
      (.seq RuntimeShiftFilter.scanner (.seq (.param 0) b)) p=
    evV g x .callByValuePar T [RuntimeShiftFilter.block n]
      (.seq duplicate (view b)) (RuntimeShiftFilter.block m++rest).length := by
  let u := RuntimeShiftFilter.block n
  let v := RuntimeShiftFilter.block m
  let j := (v++rest).length
  have hj : j≤x.length := by
    have hl := length_sfx x hp
    rw [hs] at hl
    dsimp only [j,v]
    simp only [List.length_append] at hl ⊢
    omega
  have hsj : sfx x j=v++rest := by
    have hh := suffix_trans (sfx_is_suffix x p) ⟨u,hs⟩
    exact sfx_suffix hh.choose_spec
  have hfirst := scanner_at g x .callByValuePar T E p n (v++rest) hp hs
  have hsecond := scanner_at g x .callByValuePar T E j m rest hj hsj
  have harg : evV g x .callByValuePar T E
      (.seq RuntimeShiftFilter.scanner RuntimeShiftFilter.scanner) p=some (some rest.length) := by
    rw [evV_seq_ok hfirst]
    exact hsecond
  have hcap : pre x p rest.length=u++v := by
    have hsplit : sfx x p=(u++v)++rest := by simpa [u,v,List.append_assoc] using hs
    have he := pre_eq (sfx_is_suffix x p) hsplit
    simpa only [length_sfx x hp] using he
  have hhead := scanner_at g x .callByValuePar T [pre x p rest.length] p n (v++rest) hp hs
  have hword : pre x p j=u := by
    have he := pre_eq (sfx_is_suffix x p) hs
    simpa only [length_sfx x hp] using he
  have hf : RuntimeShiftFilter.scanner.FirstOrder :=
    ⟨NestedScannerArguments.scan_firstOrder ['a'],True.intro⟩
  have he := actual_entry g x T hT E (.seq RuntimeShiftFilter.scanner RuntimeShiftFilter.scanner) RuntimeShiftFilter.scanner b ⟨hf,hf⟩ hf hb delimited_prefixFree
    u v ⟨n,rfl⟩ ⟨m,rfl⟩ p rest.length j hp harg hcap hhead hword
  simpa only [hcap] using he

end Shallot.MacroPeg.CBV.PrefixCodeCapture
