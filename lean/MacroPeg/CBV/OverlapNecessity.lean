import MacroPeg.CBV.BlockCapture

/-! Fixed-prefix replay forces periodicity for every successfully captured
word, without a periodicity condition on the argument parser. -/
namespace Shallot.MacroPeg.CBV.OverlapNecessity
open BlockCapture (copies)
open ClockFreezing (Table)

theorem prefix_periodic (u : List Char) (hu : u ≠ []) (w : List Char)
    (h : w.IsPrefix (u++w)) :
    ∃ n left right, u=left++right ∧ w=copies u n++left ∧ left.length<u.length := by
  have go : ∀ m (w : List Char), w.length=m → w.IsPrefix (u++w) →
      ∃ n left right, u=left++right ∧ w=copies u n++left ∧ left.length<u.length := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro w hw h
      by_cases hl : w.length<u.length
      · have hp : w.IsPrefix u := List.prefix_of_prefix_length_le h ⟨w,rfl⟩ (by omega)
        obtain ⟨right,hr⟩ := hp
        exact ⟨0,w,right,hr.symm,rfl,hl⟩
      · have hp : u.IsPrefix w := List.prefix_of_prefix_length_le ⟨w,rfl⟩ h (by omega)
        obtain ⟨v,hv⟩ := hp
        have hvlen : v.length<m := by
          have hl := congrArg List.length hv
          have hpos : 0<u.length := List.length_pos_iff.mpr hu
          simp only [List.length_append] at hl
          omega
        have hh : v.IsPrefix (u++v) := by
          obtain ⟨rest,hr⟩ := h
          refine ⟨rest,(List.append_right_inj u).mp ?_⟩
          rw [← hv] at hr
          simpa only [List.append_assoc] using hr
        obtain ⟨n,left,right,hr,hn,hlt⟩ := ih v.length hvlen v rfl hh
        exact ⟨n+1,left,right,hr,by rw [← hv,hn,copies,List.append_assoc],hlt⟩
  exact go w.length w rfl h

def rotations (u : List Char) : List (List Char) :=
  (List.range (u.length+1)).map (fun i => u.drop i ++ u.take i)

theorem rotations_length (u : List Char) : (rotations u).length = u.length+1 := by simp [rotations]

theorem prefix_has_rotation (u w : List Char) (h : w.IsPrefix (u++w)) :
    ∃ v ∈ rotations u, u++w=w++v := by
  by_cases hu : u=[]
  · subst u
    exact ⟨[],by simp [rotations],by simp⟩
  · obtain ⟨n,left,right,hr,hw,hlen⟩ := prefix_periodic u hu w h
    refine ⟨right++left,?_,?_⟩
    · apply List.mem_map.mpr
      refine ⟨left.length,List.mem_range.mpr (by omega),?_⟩
      rw [hr]
      simp
    · rw [hw,hr]
      exact BlockCapture.rotate left right n

theorem prefix_iff_rotation (u w : List Char) :
    w.IsPrefix (u++w) ↔ ∃ v ∈ rotations u, u++w=w++v := by
  constructor
  · exact prefix_has_rotation u w
  · rintro ⟨v,_,hv⟩
    exact ⟨v,hv.symm⟩

/-- Both words are prefixes of the same actual input. Their lengths force
capture-prefix comparability even if the capture is shorter than the shift. -/
theorem common_input_rotation (u w input a b : List Char)
    (ha : input=w++a) (hb : input=(u++w)++b) :
    ∃ v ∈ rotations u, u++w=w++v := by
  apply prefix_has_rotation u w
  exact List.prefix_of_prefix_length_le ⟨a,ha.symm⟩ ⟨b,hb.symm⟩ (by simp)

/-- An arbitrary first-order parser supplies the actual captured word.
Its successful shifted replay derives a rotation; the parser need not be
closed, independent, unary, or block-safe. -/
theorem actual_capture_rotation (g : MGrammar) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (E : List (List Char)) (a : MExp) (ha : a.FirstOrder)
    (u : List Char) (p q z : Nat) (hp : p ≤ x.length)
    (hcap : evV g x .callByValuePar T E a p = some (some q))
    (hreplay : evV g x .callByValuePar T [pre x p q] (.seq (.lit u) (.param 0)) p = some (some z)) :
    ∃ v ∈ rotations u, u++pre x p q=pre x p q++v := by
  have hfirst := (ReplayFusion.success_prefix hT E a ha p q hp hcap).2
  have hsecond := (ReplayFusion.success_prefix hT [pre x p q] (.seq (.lit u) (.param 0))
    ⟨True.intro,True.intro⟩ p z hp hreplay).2
  have hvalue := WordArguments.value_of_success g x .callByValuePar T [pre x p q]
    (.seq (.lit u) (.param 0)) ⟨True.intro,True.intro⟩ p z hp hreplay
  have hw : pre x p z = u++pre x p q := by
    simpa only [WordArguments.value,List.getElem?_cons_zero,Option.bind_some,Option.map_some,Option.some.injEq] using hvalue.symm
  rw [hw] at hsecond
  exact common_input_rotation u (pre x p q) (sfx x p) (sfx x q) (sfx x z) hfirst hsecond

theorem rotation_unique (u w v v' : List Char)
    (h : u++w=w++v) (h' : u++w=w++v') : v=v' :=
  (List.append_right_inj w).mp (h.symm.trans h')

theorem rotation_length (u w v : List Char) (h : u++w=w++v) : v.length=u.length := by
  have hh := congrArg List.length h
  simp only [List.length_append] at hh
  omega

theorem actual_capture_periodic (g : MGrammar) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (E : List (List Char)) (a : MExp) (ha : a.FirstOrder)
    (u : List Char) (hu : u ≠ []) (p q z : Nat) (hp : p ≤ x.length)
    (hcap : evV g x .callByValuePar T E a p = some (some q))
    (hreplay : evV g x .callByValuePar T [pre x p q] (.seq (.lit u) (.param 0)) p = some (some z)) :
    ∃ n left right, u=left++right ∧ pre x p q=copies u n++left ∧ left.length<u.length :=
  prefix_periodic u hu _ ((prefix_iff_rotation u _).mpr
    (actual_capture_rotation g x T hT E a ha u p q z hp hcap hreplay))

/-- The source's successful replay has a candidate literal that finishes at
exactly the same position after Seq capture. Existence does not yet supply a
static grammar guard selecting that literal before the capture is known. -/
theorem rotated_execution (g h : MGrammar) (x : List Char) (T U : Table)
    (hT : SoundTV g x .callByValuePar T) (E : List (List Char)) (a : MExp) (ha : a.FirstOrder)
    (u : List Char) (p q z : Nat) (hp : p ≤ x.length)
    (hcap : evV g x .callByValuePar T E a p = some (some q))
    (hreplay : evV g x .callByValuePar T [pre x p q] (.seq (.lit u) (.param 0)) p = some (some z)) :
    ∃ v ∈ rotations u, evV h x .callByValueSeq U [pre x p q] (.lit v) q = some (some z) := by
  obtain ⟨v,hv,hr⟩ := actual_capture_rotation g x T hT E a ha u p q z hp hcap hreplay
  have hfirst := (ReplayFusion.success_prefix hT E a ha p q hp hcap).2
  obtain ⟨hz,hsecond⟩ := ReplayFusion.success_prefix hT [pre x p q] (.seq (.lit u) (.param 0))
    ⟨True.intro,True.intro⟩ p z hp hreplay
  have hvalue := WordArguments.value_of_success g x .callByValuePar T [pre x p q]
    (.seq (.lit u) (.param 0)) ⟨True.intro,True.intro⟩ p z hp hreplay
  have hw : pre x p z = u++pre x p q := by
    simpa only [WordArguments.value,List.getElem?_cons_zero,Option.bind_some,Option.map_some,Option.some.injEq] using hvalue.symm
  rw [hw,hr,List.append_assoc] at hsecond
  have hs : sfx x q = v++sfx x z :=
    (List.append_right_inj (pre x p q)).mp (hfirst.symm.trans hsecond)
  refine ⟨v,hv,?_⟩
  simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hs,length_sfx x hz]

def chooseRotations (u : List Char) : MExp :=
  (rotations u).foldr (fun v rest => .alt (.lit v) rest) MExp.failAlways

theorem chooseRotations_firstOrder (u : List Char) : (chooseRotations u).FirstOrder := by
  have go : ∀ vs : List (List Char), (vs.foldr (fun v rest => MExp.alt (.lit v) rest) MExp.failAlways).FirstOrder := by
    intro vs
    induction vs with
    | nil => trivial
    | cons v vs ih => exact ⟨True.intro,ih⟩
  exact go (rotations u)

/-- Even an origin check for u cannot make trying all rotations sound.
The argument captures abac, which is not periodic with block ab. -/
theorem rotation_choice_false_positive :
    let gp : MGrammar := ⟨[⟨1,.seq (.seq (.lit ['a','b']) (.param 0)) (.notP .any)⟩]⟩
    let gs : MGrammar := ⟨[⟨1,.seq (chooseRotations ['a','b']) (.notP .any)⟩]⟩
    let x := "abacab".toList
    let e := MExp.seq (.andP (.lit ['a','b'])) (.call 0 [.lit ['a','b','a','c']])
    evV gp x .callByValuePar (tblV gp x .callByValuePar 1) [] e x.length = some none ∧
      evV gs x .callByValueSeq (tblV gs x .callByValueSeq 1) [] e x.length = some (some 0) ∧
      ¬(['a','b','a','c'] : List Char).IsPrefix (['a','b']++['a','b','a','c']) := by
  decide +kernel

end Shallot.MacroPeg.CBV.OverlapNecessity
