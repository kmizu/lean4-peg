import MacroPeg.CBV.CopyBodyEvaluation

/-! Delimiter boundaries synchronize unbounded repetitions of a fixed,
nonempty retained-word pattern. The iteration count is not supplied to the
parser or bounded by the grammar. -/
namespace Shallot.MacroPeg.CBV.RepeatedWordPattern
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection

def copies (js : List Nat) : Nat → List Nat
  | 0 => []
  | n+1 => js++copies js n

theorem copies_length (js : List Nat) : ∀ n, (copies js n).length=n*js.length
  | 0 => by simp [copies]
  | n+1 => by simp [copies,copies_length js n,Nat.add_mul,Nat.add_comm]

theorem copies_scope (js : List Nat) (arity : Nat) (hs : ∀ i∈js, i<arity) :
    ∀ n i, i∈copies js n → i<arity
  | 0,_,h => by cases h
  | n+1,i,h => by
    rcases List.mem_append.mp h with h|h
    · exact hs i h
    · exact copies_scope js arity hs n i h

theorem matches_append (d : Char) (w : List Char) (i : Nat) :
    ∀ a b x rest, Matches d w i (a++b) x rest ↔
      ∃ mid, Matches d w i a x mid ∧ Matches d w i b mid rest
  | [],b,x,rest => by simp [Matches]
  | j::js,b,x,rest => by
    simp only [List.cons_append,Matches,matches_append d w i js b]
    constructor
    · rintro ⟨h,t,hf,hx,hw,mid,hm,ht⟩
      exact ⟨mid,⟨h,t,hf,hx,hw,hm⟩,ht⟩
    · rintro ⟨mid,⟨h,t,hf,hx,hw,hm⟩,ht⟩
      exact ⟨h,t,hf,hx,hw,mid,hm,ht⟩

/-- Every successful segment crosses exactly one delimiter, including a
segment whose retained word is empty. -/
theorem matches_count (d : Char) (w : List Char) (i : Nat) :
    ∀ js x rest, Matches d w i js x rest → x.count d=js.length+rest.count d
  | [],x,rest,h => by simpa [Matches] using congrArg (List.count d) h
  | j::js,x,rest,h => by
    obtain ⟨a,t,ha,rfl,_,ht⟩ := h
    have hz : a.count d=0 := List.count_eq_zero.mpr ha
    simp [List.count_append,hz,matches_count d w i js t rest ht,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Independent full-input passes must have made the same number of
iterations. No retained word or iteration bound is enumerated. -/
theorem iteration_unique (d : Char) (w v : List Char) (i k : Nat)
    (js : List Nat) (hne : js≠[]) (x : List Char) (n m : Nat)
    (hn : Matches d w i (copies js n) x [])
    (hm : Matches d v k (copies js m) x []) : n=m := by
  have ha := matches_count d w i _ x [] hn
  have hb := matches_count d v k _ x [] hm
  simp only [List.count_nil,Nat.add_zero,copies_length] at ha hb
  exact Nat.eq_of_mul_eq_mul_right (List.length_pos_iff.mpr hne) (ha.symm.trans hb)

def SourceAccept (d : Char) (E : List (List Char)) (js : List Nat) (x : List Char) : Prop :=
  ∃ n, run d E (sourceParts d (copies js n)) x=some []

def ViewAccept (d : Char) (w : List Char) (i : Nat) (js : List Nat) (x : List Char) : Prop :=
  ∃ n, Matches d w i (copies js n) x []

theorem source_iff_views (d : Char) (E : List (List Char)) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (js : List Nat) (hne : js≠[]) (hs : ∀ i∈js, i<E.length) (x : List Char) :
    SourceAccept d E js x ↔ ∀ i, (hi : i<E.length) → ViewAccept d E[i] i js x := by
  constructor
  · rintro ⟨n,hn'⟩ i hi
    exact ⟨n,(DelimitedWordPattern.source_iff_views d E hn hfree _ (copies_scope js E.length hs n) x []).mp hn' i hi⟩
  · intro h
    obtain ⟨n,h0⟩ := h 0 hn
    refine ⟨n,(DelimitedWordPattern.source_iff_views d E hn hfree _ (copies_scope js E.length hs n) x []).mpr ?_⟩
    intro i hi
    obtain ⟨m,hm⟩ := h i hi
    have he := iteration_unique d E[0] E[i] 0 i js hne x n m h0 hm
    simpa [he] using hm

/-- The corresponding projections can start after their actual Seq
argument endpoints; only their first segment is adjusted. -/
def AfterAccept (d : Char) (w : List Char) (i : Nat) (js : List Nat) (tail : List Char) : Prop :=
  ∃ n mid, run d [w] (afterParts d i js) tail=some mid ∧
    Matches d w i (copies js n) mid []

theorem view_nonempty (d : Char) (w : List Char) (hw : Free d w) (i j : Nat)
    (js : List Nat) (tail : List Char) :
    (∃ n, Matches d w i (copies (j::js) (n+1)) (w++tail) []) ↔
      AfterAccept d w i (j::js) tail := by
  simp only [copies,matches_append]
  constructor
  · rintro ⟨n,mid,hm,ht⟩
    exact ⟨n,mid,(after_eq_view d w hw i j js tail).trans ((view_iff d w hw i (j::js) (w++tail) mid).mpr hm),ht⟩
  · rintro ⟨n,mid,hm,ht⟩
    refine ⟨n,mid,?_,ht⟩
    apply (view_iff d w hw i (j::js) (w++tail) mid).mp
    exact (after_eq_view d w hw i j js tail).symm.trans hm

theorem view_iff_empty_or_after (d : Char) (w : List Char) (hw : Free d w)
    (i j : Nat) (js : List Nat) (x tail : List Char) (hp : x=w++tail) :
    ViewAccept d w i (j::js) x ↔ x=[] ∨ AfterAccept d w i (j::js) tail := by
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero => exact Or.inl hn
    | succ n => exact Or.inr ((view_nonempty d w hw i j js tail).mp ⟨n,hp ▸ hn⟩)
  · rintro (he|ha)
    · exact ⟨0,he⟩
    · obtain ⟨n,hn⟩ := (view_nonempty d w hw i j js tail).mpr ha
      exact ⟨n+1,hp ▸ hn⟩

theorem source_iff_after (d : Char) (E tails : List (List Char)) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (ht : tails.length=E.length) (x : List Char)
    (hp : ∀ i, (hi : i<E.length) → x=E[i]++(tails[i]'(by omega)))
    (j : Nat) (js : List Nat) (hs : ∀ i∈j::js, i<E.length) :
    SourceAccept d E (j::js) x ↔ x=[] ∨
      ∀ i, (hi : i<E.length) → AfterAccept d E[i] i (j::js) (tails[i]'(by omega)) := by
  rw [source_iff_views d E hn hfree (j::js) (by simp) hs]
  constructor
  · intro h
    by_cases hx : x=[]
    · exact Or.inl hx
    · exact Or.inr (fun i hi => ((view_iff_empty_or_after d E[i] (hfree i hi) i j js x _ (hp i hi)).mp (h i hi)).resolve_left hx)
  · rintro (hx|h) i hi
    · exact ⟨0,hx⟩
    · exact (view_iff_empty_or_after d E[i] (hfree i hi) i j js x _ (hp i hi)).mpr (Or.inr (h i hi))

end Shallot.MacroPeg.CBV.RepeatedWordPattern
