import MacroPeg.CBV.FutureSpanRepresentatives

/-! One input-dependent table suffices for all future-copy bounds. This table
uses the whole input, including its future suffix; it is not prefix-only
preprocessing for a communication or cell-probe separation. -/
namespace Shallot.MacroPeg.CBV.RightmostCaptureIndex

open FutureSpanRepresentatives (Span Slots probe search locate normalize)
open SequentialSpanRecompute (ValidEnv)

def clip (bound : Nat) (slot : Option Span) : Option Span :=
  slot.bind (fun span => if span.1≤bound then some span else none)

private theorem search_append (x : List Char) (span : Span) (ps qs : List Nat) :
    search x span (ps++qs) = (search x span ps).or (search x span qs) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases hp : probe x span p <;> simp [search,hp,ih,Option.or]

private theorem locate_succ (x : List Char) (span : Span) (bound : Nat) :
    locate x (bound+1) span = (locate x bound span).or
      ((probe x span (bound+1)).map (fun q => (bound+1,q))) := by
  simp only [locate,List.range_succ,search_append]
  cases hp : probe x span (bound+1) <;> simp [search,hp]

/-- The first match in increasing remaining-length order is the rightmost
occurrence. Restricting the bound either retains that occurrence or kills it. -/
theorem locate_clip {x : List Char} {span : Span} (ha : span.1≤x.length) :
    ∀ n, n≤x.length → ∀ bound, bound≤n →
      locate x bound span = clip bound (locate x n span) := by
  intro n
  induction n with
  | zero =>
    intro hn bound hb
    have he : bound=0 := by omega
    subst bound
    cases hl : locate x 0 span with
    | none => rfl
    | some live =>
      have hp := (FutureSpanRepresentatives.locate_some hn ha hl).1
      simp [clip,show live.1=0 by omega]
  | succ n ih =>
    intro hn bound hb
    by_cases hbn : bound≤n
    · rw [ih (by omega) bound hbn,locate_succ]
      cases hl : locate x n span with
      | some live => rfl
      | none =>
        cases hp : probe x span (n+1) <;> simp [clip,Option.or,Nat.not_le.mpr (by omega : bound<n+1)]
    · have he : bound=n+1 := by omega
      subst bound
      cases hl : locate x (n+1) span with
      | none => rfl
      | some live =>
        have hp := (FutureSpanRepresentatives.locate_some hn ha hl).1
        simp [clip,hp]

/-- Runtime lookup uses a rectangular numeric index, with one cell for every
pair of input coordinates; invalid spans may have unused cells. -/
def address (n : Nat) (span : Span) : Nat := span.1*(n+1)+span.2

def table (x : List Char) : Array (Option Span) :=
  Array.ofFn (fun i : Fin ((x.length+1)*(x.length+1)) =>
    locate x x.length (i.val/(x.length+1), i.val%(x.length+1)))

def lookup (n : Nat) (A : Array (Option Span)) (bound : Nat) (span : Span) : Option Span :=
  clip bound (A[address n span]?.join)

theorem table_size (x : List Char) : (table x).size=(x.length+1)*(x.length+1) := by
  simp [table]

theorem address_lt {n : Nat} {span : Span} (ha : span.1≤n) (hb : span.2≤n) :
    address n span < (n+1)*(n+1) := by
  have hmul := Nat.mul_le_mul_right (n+1) ha
  calc
    address n span < span.1*(n+1)+(n+1) := Nat.add_lt_add_left (by omega) _
    _ ≤ n*(n+1)+(n+1) := Nat.add_le_add_right hmul _
    _ = (n+1)*(n+1) := (Nat.succ_mul _ _).symm

theorem table_get {x : List Char} {span : Span} (ha : span.1≤x.length) (hb : span.2≤x.length) :
    (table x)[address x.length span]? = some (locate x x.length span) := by
  have hi := address_lt ha hb
  rw [Array.getElem?_eq_getElem (by simpa only [table_size] using hi)]
  simp only [table,Array.getElem_ofFn]
  have hd : address x.length span / (x.length+1) = span.1 := by
    simp [address,Nat.add_div,Nat.div_eq_of_lt (by omega : span.2<x.length+1)]
    exact Nat.mod_lt _ (by omega)
  have hm : address x.length span % (x.length+1) = span.2 := by
    simp [address,Nat.add_mod,Nat.mod_eq_of_lt (by omega : span.2<x.length+1)]
  rw [hd,hm]

theorem lookup_eq {x : List Char} {span : Span} {bound : Nat}
    (hspan : span.2≤span.1 ∧ span.1≤x.length) (hb : bound≤x.length) :
    lookup x.length (table x) bound span = locate x bound span := by
  simp only [lookup,table_get hspan.2 (Nat.le_trans hspan.1 hspan.2),Option.join_some]
  exact (locate_clip hspan.2 x.length (Nat.le_refl _) bound hb).symm

/-- After the single metadata lookup, both matched spans lie in the current
suffix. If the canonical occurrence has already passed, return failure without
reading the old captured word. -/
def indexedMatch (x : List Char) (A : Array (Option Span)) (span : Span) (p : Nat) : Res :=
  match lookup x.length A p span with
  | none => some none
  | some live => SequentialSpanRecompute.matchSpan x live.1 live.2 p

theorem indexedMatch_sources {x : List Char} {span live : Span} {p : Nat}
    (hspan : span.2≤span.1 ∧ span.1≤x.length) (hp : p≤x.length)
    (h : lookup x.length (table x) p span=some live) :
    live.2≤live.1 ∧ live.1≤p := by
  rw [lookup_eq hspan hp] at h
  have hl := FutureSpanRepresentatives.locate_some hp hspan.2 h
  exact ⟨hl.2.1,hl.1⟩

theorem indexedMatch_eq {x : List Char} {span : Span} {p : Nat}
    (hspan : span.2≤span.1 ∧ span.1≤x.length) (hp : p≤x.length) :
    indexedMatch x (table x) span p = SequentialSpanRecompute.matchSpan x span.1 span.2 p := by
  unfold indexedMatch
  rw [lookup_eq hspan hp]
  cases hl : locate x p span with
  | none =>
    have hd := (FutureSpanRepresentatives.locate_none hspan.2).mp hl p (Nat.le_refl _)
    rw [SequentialSpanRecompute.matchSpan_eq x span.1 span.2 p hspan.2,hd]
    rfl
  | some live =>
    have hw := FutureSpanRepresentatives.locate_some hp hspan.2 hl
    simp only []
    rw [SequentialSpanRecompute.matchSpan_eq x live.1 live.2 p (Nat.le_trans hw.1 hp),
      SequentialSpanRecompute.matchSpan_eq x span.1 span.2 p hspan.2,hw.2.2]

def indexedNormalize (n : Nat) (A : Array (Option Span)) (bound : Nat)
    (E : SequentialSpanRecompute.Env) : Slots := E.map (lookup n A bound)

theorem indexedNormalize_eq {x : List Char} {bound : Nat} (hb : bound≤x.length)
    (E : SequentialSpanRecompute.Env) (hE : ValidEnv x.length E) :
    indexedNormalize x.length (table x) bound E = normalize x bound E := by
  apply List.map_congr_left
  intro span hs
  exact lookup_eq (hE span hs) hb

end Shallot.MacroPeg.CBV.RightmostCaptureIndex
