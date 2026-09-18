import PalPeg.GalilScaffoldChainMirror

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldChainVerifier GalilScaffoldChainVerifyRun

theorem mixed_supply (rs qs : List (Fin 2)) (a : Fin 2) (ls : List (Option (Fin 2))) :
    ∃ q, Reads ⟨⟨some a,ls,rs.map some,qs⟩,false⟩ (pairs (rs ++ qs)) q ∧
      q.head.right = [] ∧ q.head.incoming = [] ∧ q.gap = false := by
  induction rs generalizing a ls with
  | nil => simpa using queue_supply qs a ls []
  | cons b rs ih =>
    obtain ⟨q,hr,hrs,hqs,hgap⟩ := ih b (some a :: ls)
    refine ⟨q,?_,hrs,hqs,hgap⟩
    apply Reads.next _ 2 (Or.inl rfl) rfl
    apply Reads.next _ (GalilScaffoldPlace.letter b)
    · right; left; simp [right]
    · rfl
    · exact hr

/-- A represented input head supplies the actual unread suffix of the
same arrived word, crossing from saved right stack into incoming FIFO. -/
theorem represented_supply (h : Head) (word : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents h word) (hp : h.focus ≠ none) :
    ∃ q, Reads ⟨h,false⟩ (pairs (word.drop h.left.length)) q ∧
      q.head.right = [] ∧ q.head.incoming = [] ∧ q.gap = false := by
  obtain ⟨xs,rs,qs,rfl,rfl⟩ := hh
  cases xs with
  | nil => simp [layout] at hp
  | cons a xs =>
    have hs : ((a :: xs).reverse ++ rs ++ qs).drop
        (layout (a :: xs) (rs.map some) qs).left.length = rs ++ qs := by
      have hl : (layout (a :: xs) (rs.map some) qs).left.length = (a :: xs).reverse.length := by
        simp [layout]
      rw [hl,List.append_assoc,List.drop_left]
    rw [hs]
    exact mixed_supply rs qs a (xs.map some ++ [none])

/-- No movement changes the word represented by this verifier. -/
theorem right_word (p : PlaceHead) (word : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head word) (hp : canRight p) :
    GalilScaffoldInputTrace.Represents (right p).head word := by
  cases hg : p.gap with
  | false => simpa [right,hg] using hh
  | true =>
    have hc : GalilScaffoldInputTrace.canRight p.head := by
      simpa [canRight,hg,GalilScaffoldInputTrace.canRight] using hp
    simpa [right,hg] using GalilScaffoldInputTrace.right_represents hh hc

theorem reads_word {p q : PlaceHead} {xs : List (Fin 3)} (hr : Reads p xs q)
    (word : List (Fin 2)) (hh : GalilScaffoldInputTrace.Represents p.head word) :
    GalilScaffoldInputTrace.Represents q.head word := by
  induction hr with
  | stop p => exact hh
  | next p a hp ha hr ih => exact ih (right_word p word hh hp)

theorem reads_split_at {p q : PlaceHead} {xs : List (Fin 3)} (hr : Reads p xs q) (n : ℕ) :
    ∃ m, Reads p (xs.take n) m ∧ Reads m (xs.drop n) q := by
  induction hr generalizing n with
  | stop p => exact ⟨p,by simpa using Reads.stop p,by simpa using Reads.stop p⟩
  | next p a hp ha hr ih =>
    cases n with
    | zero => exact ⟨p,Reads.stop _,Reads.next p a hp ha hr⟩
    | succ n =>
      obtain ⟨m,hprefix,hsuffix⟩ := ih n
      exact ⟨m,Reads.next p a hp ha hprefix,hsuffix⟩

/-- Actual logical reachability discharges the stack partition premise.
Any finite prefix retains the same arrived word representation. -/
theorem reachable_prefix_supply (h : Head) (word : List (Fin 2))
    (hr : GalilScaffoldInputTrace.Reach h word) (hp : h.focus ≠ none) (n : ℕ) :
    ∃ q, Reads ⟨h,false⟩ ((pairs (word.drop h.left.length)).take n) q ∧
      GalilScaffoldInputTrace.Represents q.head word := by
  have hh := GalilScaffoldInputTrace.reachable_represents hr
  obtain ⟨q,hreads,_,_,_⟩ := represented_supply h word hh hp
  obtain ⟨m,hprefix,_⟩ := reads_split_at hreads n
  exact ⟨m,hprefix,reads_word hprefix word hh⟩

def encoded (raw : List (Fin 2)) : List (Fin 3) := pairs raw ++ [2]

theorem pairs_append (xs ys : List (Fin 2)) : pairs (xs ++ ys) = pairs xs ++ pairs ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairs,ih]

theorem encoded_reverse (raw : List (Fin 2)) :
    (encoded raw).reverse = encoded raw.reverse := by
  induction raw with
  | nil => rfl
  | cons a raw ih =>
    simpa [encoded,pairs,pairs_append,List.reverse_cons,List.append_assoc] using
      congrArg (fun w => w ++ [GalilScaffoldPlace.letter a,2]) ih

theorem pairs_length (raw : List (Fin 2)) : (pairs raw).length = 2 * raw.length := by
  induction raw with
  | nil => rfl
  | cons a raw ih => simp [pairs,ih]; omega

theorem pairs_drop (raw : List (Fin 2)) (n : ℕ) :
    (pairs raw).drop (2*n) = pairs (raw.drop n) := by
  induction n generalizing raw with
  | zero => simp
  | succ n ih =>
    cases raw with
    | nil => simp [pairs]
    | cons a raw =>
      simpa [pairs, Nat.mul_succ, Nat.add_assoc, List.drop_succ_cons] using ih raw

/-- The suffix after a present letter begins at the following gap. -/
theorem encoded_suffix (raw : List (Fin 2)) (n : ℕ) (hn : n ≤ raw.length) :
    (encoded raw).drop (2*n) = pairs (raw.drop n) ++ [2] := by
  rw [encoded,List.drop_append_of_le_length (by rw [pairs_length]; omega),pairs_drop]

theorem rightReads_suffix (word : List (Fin 3)) (center n : ℕ)
    (hn : n ≤ (word.drop (center+1)).length) :
    GalilScaffoldChainMirror.rightReads word center n =
      ((word.drop (center+1)).take n).map some := by
  apply List.ext_getElem
  · simpa [GalilScaffoldChainMirror.rightReads] using hn
  · intro i hi hj
    have hin : i < n := by simpa [GalilScaffoldChainMirror.rightReads] using hi
    have hib : center+1+i < word.length := by
      simp only [List.length_drop] at hn
      omega
    simp [GalilScaffoldChainMirror.rightReads, Nat.add_comm, Nat.add_left_comm]

theorem encoded_rightReads (raw : List (Fin 2)) (L n : ℕ)
    (hL : 0 < L) (hbound : L ≤ raw.length)
    (hn : n ≤ (pairs (raw.drop L)).length) :
    GalilScaffoldChainMirror.rightReads (encoded raw) (2*L-1) n =
      ((pairs (raw.drop L)).take n).map some := by
  have hc : 2*L-1+1 = 2*L := by omega
  have hs : (encoded raw).drop (2*L-1+1) = pairs (raw.drop L) ++ [2] := by
    rw [hc,encoded_suffix raw L hbound]
  rw [rightReads_suffix _ _ _ (by rw [hs]; simp; omega),hs,
    List.take_append_of_le_length hn]

theorem leftReads_prefix (word : List (Fin 3)) (center n : ℕ)
    (hc : center < word.length) (hn : n ≤ center) :
    GalilScaffoldChainMirror.leftReads word center n =
      ((((word.take (center+1)).reverse).drop 1).take n).map some := by
  have hl : (word.take (center+1)).length = center+1 := by simp; omega
  apply List.ext_getElem
  · simp [GalilScaffoldChainMirror.leftReads]; omega
  · intro i hi hj
    have hin : i < n := by simpa [GalilScaffoldChainMirror.leftReads] using hi
    have hb : center-(i+1) < word.length := by omega
    simp only [GalilScaffoldChainMirror.leftReads,List.getElem_map,List.getElem_range,
      List.getElem_take,List.getElem_drop,List.getElem_reverse,hl]
    simp [List.getElem?_eq_getElem hb]
    congr 2; omega

theorem pairs_gaps (xs : List (Fin 2)) : pairs xs = GalilScaffoldPlace.gaps xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairs,GalilScaffoldPlace.gaps,ih]

theorem left_window (a : Fin 2) (xs suffix : List (Fin 2)) :
    ((encoded ((a :: xs).reverse ++ suffix)).take (2*(xs.length+1))).reverse =
      GalilScaffoldPlace.stream ⟨a :: xs,false⟩ ++ [2] := by
  have hl : (pairs (a :: xs).reverse).length = 2*(xs.length+1) := by
    simp [pairs_length]
  have ht : (encoded ((a :: xs).reverse ++ suffix)).take (2*(xs.length+1)) =
      pairs (a :: xs).reverse := by
    rw [encoded,pairs_append,List.append_assoc,← hl,List.take_left]
  rw [ht]
  have he := encoded_reverse (a :: xs).reverse
  simp only [encoded,List.reverse_append,List.reverse_singleton,List.reverse_reverse,
    pairs,List.cons_append,List.nil_append,List.cons.injEq,true_and] at he
  simpa only [GalilScaffoldPlace.stream, Bool.false_eq_true, if_false,
    pairs_gaps,List.cons_append] using he

theorem left_window_reads (a : Fin 2) (xs suffix : List (Fin 2)) (n : ℕ)
    (hn : n ≤ 2*xs.length) :
    GalilScaffoldChainMirror.leftReads (encoded ((a :: xs).reverse ++ suffix))
      (2*(xs.length+1)-1) n =
      (((GalilScaffoldPlace.stream ⟨a :: xs,false⟩).drop 1).take n).map some := by
  have hc : 2*(xs.length+1)-1 < (encoded ((a :: xs).reverse ++ suffix)).length := by
    simp [encoded,pairs_length]; omega
  have hcn : n ≤ 2*(xs.length+1)-1 := by omega
  rw [leftReads_prefix _ _ _ hc hcn]
  have he : 2*(xs.length+1)-1+1 = 2*(xs.length+1) := by omega
  rw [he,left_window]
  have hlen : n ≤ (GalilScaffoldPlace.gaps xs).length := by
    rw [← pairs_gaps,pairs_length]; exact hn
  simp only [GalilScaffoldPlace.stream, Bool.false_eq_true,if_false,List.cons_append,
    List.drop_succ_cons,List.drop_zero]
  rw [List.take_append_of_le_length hlen]

theorem encoded_take (pre suffix : List (Fin 2)) :
    (encoded (pre ++ suffix)).take (2*pre.length+1) = encoded pre := by
  rw [← pairs_length pre]
  simp only [encoded,pairs_append,List.append_assoc,List.take_append]
  cases suffix <;> simp [pairs]

theorem gap_left_window_reads (a : Fin 2) (xs suffix : List (Fin 2)) (n : ℕ)
    (hn : n ≤ 2*xs.length+1) :
    GalilScaffoldChainMirror.leftReads (encoded ((a :: xs).reverse ++ suffix))
      (2*(xs.length+1)) n =
      (((GalilScaffoldPlace.stream ⟨a :: xs,true⟩).drop 1).take n).map some := by
  have hc : 2*(xs.length+1) < (encoded ((a :: xs).reverse ++ suffix)).length := by
    simp [encoded,pairs_length]
  rw [leftReads_prefix _ _ _ hc (by omega)]
  have hl : (a :: xs).reverse.length = xs.length+1 := by simp
  rw [← hl,encoded_take,encoded_reverse,List.reverse_reverse]
  have hlen : n ≤ (GalilScaffoldPlace.letter a :: pairs xs).length := by
    simp [pairs_length]; omega
  simp only [encoded,pairs,List.cons_append,List.drop_succ_cons,
    List.drop_zero,GalilScaffoldPlace.stream,if_true]
  rw [← List.cons_append,List.take_append_of_le_length hlen]
  rw [pairs_gaps]

theorem candidate_window_layout (a : Fin 2) (xs suffix : List (Fin 2))
    (w : List (Fin 3)) (span lower period n : ℕ)
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: xs,false⟩).take span)
    (hc : GalilDpCorrect.Candidate w lower period) (hn : n ≤ 4*period) :
    ((w.drop 1).take n).map some =
      GalilScaffoldChainMirror.leftReads (encoded ((a :: xs).reverse ++ suffix))
        (2*(xs.length+1)-1) n := by
  have hlen := hc.2.1
  have hs : (GalilScaffoldPlace.stream ⟨a :: xs,false⟩).length = 2*xs.length+1 := by
    simp [GalilScaffoldPlace.stream,← pairs_gaps,pairs_length]
  have hwlen : w.length = min span (2*xs.length+1) := by
    rw [hw,List.length_take,hs]
  have hnx : n ≤ 2*xs.length := by omega
  have hnspan : n ≤ span-1 := by omega
  rw [left_window_reads a xs suffix n hnx,hw,List.drop_take,List.take_take,
    Nat.min_eq_left hnspan]

theorem candidate_gap_window_layout (a : Fin 2) (xs suffix : List (Fin 2))
    (w : List (Fin 3)) (span lower period n : ℕ)
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: xs,true⟩).take span)
    (hc : GalilDpCorrect.Candidate w lower period) (hn : n ≤ 4*period) :
    ((w.drop 1).take n).map some =
      GalilScaffoldChainMirror.leftReads (encoded ((a :: xs).reverse ++ suffix))
        (2*(xs.length+1)) n := by
  have hlen := hc.2.1
  have hs : (GalilScaffoldPlace.stream ⟨a :: xs,true⟩).length = 2*xs.length+2 := by
    simp [GalilScaffoldPlace.stream,← pairs_gaps,pairs_length]
  have hwlen : w.length = min span (2*xs.length+2) := by
    rw [hw,List.length_take,hs]
  have hnx : n ≤ 2*xs.length+1 := by omega
  have hnspan : n ≤ span-1 := by omega
  rw [gap_left_window_reads a xs suffix n hnx,hw,List.drop_take,List.take_take,
    Nat.min_eq_left hnspan]

#print axioms candidate_gap_window_layout
#print axioms candidate_window_layout
#print axioms left_window_reads

theorem represented_position (h : Head) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents h raw) (hp : h.focus ≠ none) :
    0 < h.left.length ∧ h.left.length ≤ raw.length := by
  obtain ⟨xs,rs,qs,rfl,rfl⟩ := hh
  cases xs with
  | nil => simp [layout] at hp
  | cons a xs => simp [layout]

theorem reads_present {p q : PlaceHead} {xs : List (Fin 3)}
    (hr : Reads p xs q) (hp : p.head.focus ≠ none) : q.head.focus ≠ none := by
  induction hr with
  | stop p => exact hp
  | next p a hc ha hr ih =>
    apply ih
    intro he
    simp [GalilScaffoldInputHead.read,he] at ha

/-- Reachability supplies both the legal trace and its coordinates in
the same augmented input, with enough input for exactly n reads. -/
theorem reachable_coordinate_supply (h : Head) (raw : List (Fin 2))
    (hr : GalilScaffoldInputTrace.Reach h raw) (hp : h.focus ≠ none) (n : ℕ)
    (hn : n ≤ 2 * (raw.drop h.left.length).length + 1) :
    ∃ actual q, Reads ⟨h,false⟩ actual q ∧ actual.length = n ∧
      actual.map some = GalilScaffoldChainMirror.rightReads
        (encoded raw) (2*h.left.length-1) n ∧
      GalilScaffoldInputTrace.Represents q.head raw := by
  have hh := GalilScaffoldInputTrace.reachable_represents hr
  obtain ⟨hpos,hbound⟩ := represented_position h raw hh hp
  obtain ⟨q,hrq,_,_,hg⟩ := represented_supply h raw hh hp
  have hqp := reads_present hrq hp
  have hgap : read (right q) = some 2 := by
    cases he : q.head.focus with
    | none => exact False.elim (hqp he)
    | some a => simp [GalilScaffoldInputHead.read,right,hg,he]
  have hfinal : Reads q [2] (right q) :=
    Reads.next q 2 (Or.inl hg) hgap (Reads.stop _)
  have hall := reads_append hrq hfinal
  obtain ⟨m,hreads,_⟩ := reads_split_at hall n
  have hlen : n ≤ (pairs (raw.drop h.left.length) ++ [2]).length := by
    simpa [pairs_length] using hn
  have hcoord : 2*h.left.length-1+1 = 2*h.left.length := by omega
  have hs : (encoded raw).drop (2*h.left.length-1+1) =
      pairs (raw.drop h.left.length) ++ [2] := by
    rw [hcoord,encoded_suffix raw h.left.length hbound]
  refine ⟨_,m,hreads,?_,?_,reads_word hreads raw hh⟩
  · simp only [List.length_take, Nat.min_eq_left hlen]
  · rw [rightReads_suffix _ _ _ (by rw [hs]; exact hlen),hs]

theorem rightReads_tail (word : List (Fin 3)) (center n : ℕ) :
    (GalilScaffoldChainMirror.rightReads word center (n+1)).tail =
      GalilScaffoldChainMirror.rightReads word (center+1) n := by
  simp [GalilScaffoldChainMirror.rightReads,List.range_succ_eq_map,List.map_map,
    Nat.add_comm,Nat.add_left_comm]

/-- Remove the first gap read of the letter-start trace. This supplies
gap-centered verification, including the empty trace at the final gap. -/
theorem reachable_gap_supply (h : Head) (raw : List (Fin 2))
    (hr : GalilScaffoldInputTrace.Reach h raw) (hp : h.focus ≠ none) (n : ℕ)
    (hn : n ≤ 2*(raw.drop h.left.length).length) :
    ∃ actual q, Reads ⟨h,true⟩ actual q ∧ actual.length = n ∧
      actual.map some = GalilScaffoldChainMirror.rightReads
        (encoded raw) (2*h.left.length) n ∧
      GalilScaffoldInputTrace.Represents q.head raw := by
  obtain ⟨actual,q,hreads,hlen,hcoord,hq⟩ :=
    reachable_coordinate_supply h raw hr hp (n+1) (by omega)
  have hpos := (represented_position h raw
    (GalilScaffoldInputTrace.reachable_represents hr) hp).1
  cases actual with
  | nil => simp at hlen
  | cons a rest =>
    have he := congrArg List.tail hcoord
    rw [rightReads_tail] at he
    have hc : 2*h.left.length-1+1 = 2*h.left.length := by omega
    rw [hc] at he
    cases hreads with
    | next p a hcan hread hrest =>
      exact ⟨rest,q,by simpa [right] using hrest,
        by simpa using hlen,by simpa using he,hq⟩

#print axioms reachable_gap_supply

/-- The right layout and legal moves are derived from the actual input
head, rather than supplied independently of the palindrome certificate. -/
theorem reachable_mirrored_safe (h : Head) (raw : List (Fin 2)) (gap : Bool)
    (hr : GalilScaffoldInputTrace.Reach h raw) (hp : h.focus ≠ none)
    (w : List (Fin 3)) (radius n lower : ℕ) (c b : Fin 3) (xs : List (Fin 3))
    (hpal : Manacher.PalAt (encoded raw)
      (if gap then 2*h.left.length else 2*h.left.length-1) radius)
    (hn : n ≤ radius)
    (hsize : n ≤ 4*(xs.length+1))
    (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hhead : w.take (xs.length+2) = c :: (xs ++ [b]))
    (hleft : ((w.drop 1).take n).map some =
      GalilScaffoldChainMirror.leftReads (encoded raw)
        (if gap then 2*h.left.length else 2*h.left.length-1) n) :
    ∃ t, GalilScaffoldChainVerifyRun.Run
      ⟨⟨h,gap⟩,GalilScaffoldChainConsume.ready c xs b⟩ n t ∧
      t.control.broken = false ∧
      GalilScaffoldInputTrace.Represents t.verifier.head raw := by
  have hh := GalilScaffoldInputTrace.reachable_represents hr
  obtain ⟨hpos,hbound⟩ := represented_position h raw hh hp
  have hend := hpal.2.1
  have hlength : (encoded raw).length = 2*raw.length+1 := by
    simp [encoded,pairs_length]
  rw [hlength] at hend
  have hsupply : ∃ actual q, Reads ⟨h,gap⟩ actual q ∧ actual.length = n ∧
      actual.map some = GalilScaffoldChainMirror.rightReads (encoded raw)
        (if gap then 2*h.left.length else 2*h.left.length-1) n ∧
      GalilScaffoldInputTrace.Represents q.head raw := by
    cases gap with
    | false =>
      apply reachable_coordinate_supply h raw hr hp n
      simp only [List.length_drop]; simp only [Bool.false_eq_true,if_false] at hend; omega
    | true =>
      apply reachable_gap_supply h raw hr hp n
      simp only [List.length_drop]; simp only [if_true] at hend; omega
  obtain ⟨actual,q,hreads,_,hlayout,hq⟩ := hsupply
  obtain ⟨t,ht,hver,hgood⟩ := GalilScaffoldChainMirror.mirrored_candidate_safe
    (encoded raw) w (if gap then 2*h.left.length else 2*h.left.length-1) radius n lower c b xs actual
    hpal hn hsize hc hhead hleft hlayout ⟨h,gap⟩ q hreads
  exact ⟨t,ht,hgood,by rw [hver]; exact hq⟩

theorem copied_window_head (p : GalilScaffoldPlace.Place) (w : List (Fin 3))
    (span lower period : ℕ) (c b : Fin 3) (xs : List (Fin 3))
    (hw : w = (GalilScaffoldPlace.stream p).take span)
    (hc : GalilDpCorrect.Candidate w lower period)
    (hread : GalilScaffoldPlace.read p = some c)
    (hcopy : xs ++ [b] = ((GalilScaffoldPlace.stream p).drop 1).take period) :
    period = xs.length+1 ∧ w.take (xs.length+2) = c :: (xs ++ [b]) := by
  have hlen := hc.2.1
  have hwlen : w.length = min span (GalilScaffoldPlace.stream p).length := by
    rw [hw,List.length_take]
  have hs : period ≤ ((GalilScaffoldPlace.stream p).drop 1).length := by
    simp only [List.length_drop]; omega
  have hperiod : period = xs.length+1 := by
    have hh := congrArg List.length hcopy
    simp only [List.length_append,List.length_singleton,List.length_take,
      Nat.min_eq_left hs] at hh
    omega
  refine ⟨hperiod,?_⟩
  have ht : xs.length+2 ≤ span := by omega
  rw [hw,List.take_take,Nat.min_eq_left ht]
  rw [GalilScaffoldPlace.read_stream] at hread
  cases he : GalilScaffoldPlace.stream p with
  | nil => simp [he] at hread
  | cons a rest =>
    have ha : a = c := by simpa [he] using hread
    subst a
    simp only [he,List.drop_succ_cons,List.drop_zero,hperiod] at hcopy
    simpa only [List.take_succ_cons] using congrArg (List.cons c) hcopy.symm

/-- A DP window and verifier sharing one represented input layout need
no separately asserted left/right coordinate equalities. -/
theorem window_mirrored_safe (a : Fin 2) (ls rs qs : List (Fin 2)) (gap : Bool)
    (hr : GalilScaffoldInputTrace.Reach (layout (a :: ls) (rs.map some) qs)
      ((a :: ls).reverse ++ rs ++ qs))
    (w : List (Fin 3)) (span radius n lower : ℕ) (c b : Fin 3) (xs : List (Fin 3))
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take span)
    (hpal : Manacher.PalAt (encoded ((a :: ls).reverse ++ rs ++ qs))
      (if gap then 2*(ls.length+1) else 2*(ls.length+1)-1) radius)
    (hn : n ≤ radius) (hsize : n ≤ 4*(xs.length+1))
    (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hhead : w.take (xs.length+2) = c :: (xs ++ [b])) :
    ∃ t, GalilScaffoldChainVerifyRun.Run
      ⟨⟨layout (a :: ls) (rs.map some) qs,gap⟩,
        GalilScaffoldChainConsume.ready c xs b⟩ n t ∧
      t.control.broken = false ∧
      GalilScaffoldInputTrace.Represents t.verifier.head ((a :: ls).reverse ++ rs ++ qs) := by
  apply reachable_mirrored_safe _ _ gap hr (by simp [layout]) w radius n lower c b xs
  · simpa [layout] using hpal
  · exact hn
  · exact hsize
  · exact hc
  · exact hhead
  · cases gap with
    | false => simpa [layout,List.append_assoc] using
        candidate_window_layout a ls (rs ++ qs) w span lower (xs.length+1) n hw hc hsize
    | true => simpa [layout,List.append_assoc] using
        candidate_gap_window_layout a ls (rs ++ qs) w span lower (xs.length+1) n hw hc hsize

open GalilScaffoldChainPeriod in
theorem found_window_safe
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {events : List Bool} {w : List (Fin 3)} {lower span : ℕ}
    (a : Fin 2) (ls rs qs : List (Fin 2)) (gap : Bool)
    (hreach : GalilScaffoldInputTrace.Reach (layout (a :: ls) (rs.map some) qs)
      ((a :: ls).reverse ++ rs ++ qs))
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x events t y)
    (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (radius : ℕ)
    (hpal : Manacher.PalAt (encoded ((a :: ls).reverse ++ rs ++ qs))
      (if gap then 2*(ls.length+1) else 2*(ls.length+1)-1) radius) :
    ∃ h c u q xs b,
      GalilDpCorrect.Candidate w lower h ∧ h = xs.length+1 ∧
      Copy (y.config.tapes 11) GalilScaffoldCounter.reset ⟨a :: ls,gap⟩ (start c)
        h u (GalilScaffoldCounter.ofNat h) q (fill (start c) (xs ++ [b])) ∧
      Back (write (fill (start c) (xs ++ [b])) (.last b)) (h+1)
        (GalilScaffoldChainConsume.ready c xs b).period ∧
      ∀ n, n ≤ radius → n ≤ 4*h →
        ∃ z, GalilScaffoldChainVerifyRun.Run
          ⟨⟨layout (a :: ls) (rs.map some) qs,gap⟩,
            GalilScaffoldChainConsume.ready c xs b⟩ n z ∧
          z.control.broken = false ∧
          GalilScaffoldInputTrace.Represents z.verifier.head ((a :: ls).reverse ++ rs ++ qs) := by
  obtain ⟨h,c,u,q,xs,b,hc,hread,hcopy,_,_,_,hback,hwords,_⟩ :=
    found_start_back ⟨a :: ls,gap⟩ hw hr hs ht hv
  obtain ⟨hperiod,hhead⟩ :=
    copied_window_head ⟨a :: ls,gap⟩ w (span+1) lower h c b xs hw hc hread hwords
  refine ⟨h,c,u,q,xs,b,hc,hperiod,hcopy,hback,?_⟩
  intro n hn hsize
  apply window_mirrored_safe a ls rs qs gap hreach w (span+1) radius n lower c b xs
    hw hpal hn
  · simpa [hperiod] using hsize
  · simpa [hperiod] using hc
  · exact hhead

theorem reverse_prefix_read (word : List (Fin 3)) (center : ℕ)
    (hc : center < word.length) :
    ((word.take (center+1)).reverse)[0]? = word[center]? := by
  have hl : 0+center+1 = (word.take (center+1)).length := by simp; omega
  rw [List.getElem?_reverse' hl]
  simp

theorem layout_read_coordinate (a : Fin 2) (ls rs qs : List (Fin 2)) (gap : Bool) :
    GalilScaffoldInputHead.read ⟨layout (a :: ls) (rs.map some) qs,gap⟩ =
      (encoded ((a :: ls).reverse ++ rs ++ qs))[
        if gap then 2*(ls.length+1) else 2*(ls.length+1)-1]? := by
  have hc : 2*(ls.length+1) < (encoded ((a :: ls).reverse ++ rs ++ qs)).length := by
    simp [encoded,pairs_length]
  cases gap with
  | false =>
    have he := reverse_prefix_read (encoded ((a :: ls).reverse ++ rs ++ qs))
      (2*(ls.length+1)-1) (by omega)
    have hn : 2*(ls.length+1)-1+1 = 2*(ls.length+1) := by omega
    rw [hn,List.append_assoc,left_window] at he
    simpa [GalilScaffoldInputHead.read,layout,GalilScaffoldPlace.stream] using he
  | true =>
    have he := reverse_prefix_read (encoded ((a :: ls).reverse ++ rs ++ qs))
      (2*(ls.length+1)) hc
    have hl : (a :: ls).reverse.length = ls.length+1 := by simp
    rw [List.append_assoc,← hl,encoded_take,encoded_reverse,List.reverse_reverse] at he
    simpa [GalilScaffoldInputHead.read,layout,encoded,pairs] using he

def position (p : PlaceHead) : ℕ :=
  if p.gap then 2*p.head.left.length else 2*p.head.left.length-1

theorem right_position (p : PlaceHead) (hc : canRight p)
    (hl : 0 < p.head.left.length) : position (right p) = position p + 1 := by
  have hr := right_realize p hc
  cases hr with
  | gap h =>
    change 0 < h.left.length at hl
    simp only [position,right,Bool.false_eq_true,if_false,Bool.not_false,if_true]
    omega
  | letter hr =>
    cases hr <;> simp [position,right,headRight,GalilScaffoldInputTrace.moveRight] <;> omega

theorem left_position (p : PlaceHead) (hl : 0 < p.head.left.length) :
    position (GalilScaffoldInputHead.left p) + 1 = position p := by
  rcases p with ⟨⟨f,ls,rs,qs⟩,gap⟩
  cases ls with
  | nil => simp at hl
  | cons a ls =>
    cases gap <;> simp [position,GalilScaffoldInputHead.left,moveLeft] <;> omega

theorem comparison_positions (leftHead rightHead : PlaceHead) (center radius : ℕ)
    (hl : 0 < leftHead.head.left.length) (hr : 0 < rightHead.head.left.length)
    (hc : canRight rightHead) (hb : radius < center)
    (hleft : position leftHead = center-radius)
    (hright : position rightHead = center+radius) :
    position (GalilScaffoldInputHead.left leftHead) = center-(radius+1) ∧
      position (right rightHead) = center+(radius+1) := by
  have hleftStep := left_position leftHead hl
  have hrightStep := right_position rightHead hc hr
  constructor <;> omega

#print axioms comparison_positions

theorem represented_read (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none) :
    GalilScaffoldInputHead.read p = (encoded raw)[position p]? := by
  rcases p with ⟨h,gap⟩
  obtain ⟨xs,rs,qs,rfl,rfl⟩ := hh
  cases xs with
  | nil => simp [layout] at hp
  | cons a ls => simpa [position,layout] using layout_read_coordinate a ls rs qs gap

/-- A successful comparison of represented heads extends the known
palindrome. The caller must establish the post-move endpoint positions. -/
theorem matched_extends (raw : List (Fin 2)) (center radius : ℕ)
    (leftHead rightHead : PlaceHead)
    (hl : GalilScaffoldInputTrace.Represents leftHead.head raw)
    (hr : GalilScaffoldInputTrace.Represents rightHead.head raw)
    (hlp : leftHead.head.focus ≠ none) (hrp : rightHead.head.focus ≠ none)
    (hpal : Manacher.PalAt (encoded raw) center radius)
    (hbound : radius+1 ≤ center)
    (hleft : position leftHead = center-(radius+1))
    (hright : position rightHead = center+(radius+1))
    (hmatch : GalilScaffoldInputHead.read leftHead = GalilScaffoldInputHead.read rightHead) :
    Manacher.PalAt (encoded raw) center (radius+1) := by
  have hpos := represented_position rightHead.head raw hr hrp
  have hend : center+(radius+1) < (encoded raw).length := by
    simp only [encoded,List.length_append,List.length_singleton,pairs_length]
    unfold position at hright
    split at hright <;> omega
  rw [represented_read leftHead raw hl hlp,represented_read rightHead raw hr hrp,
    hleft,hright] at hmatch
  apply Manacher.palAt_succ_iff.mpr
  exact ⟨hpal,by simp [Manacher.matchOK,hbound,hend,hmatch]⟩

theorem right_present (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw)
    (hp : p.head.focus ≠ none) (hc : canRight p) : (right p).head.focus ≠ none := by
  rcases p with ⟨h,gap⟩
  cases gap with
  | false => simpa [right] using hp
  | true =>
    obtain ⟨xs,rs,qs,rfl,rfl⟩ := hh
    cases rs with
    | cons a rs =>
      cases xs <;> simp [right,headRight,GalilScaffoldInputTrace.moveRight,layout]
    | nil =>
      cases qs with
      | nil => cases xs <;> simp [canRight,layout] at hc
      | cons a qs =>
        cases xs <;> simp [right,headRight,GalilScaffoldInputTrace.moveRight,layout]

theorem left_word (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none) :
    GalilScaffoldInputTrace.Represents (GalilScaffoldInputHead.left p).head raw := by
  cases hg : p.gap with
  | false =>
    simpa [GalilScaffoldInputHead.left,hg] using
      (GalilScaffoldInputTrace.left_represents hh hp).2
  | true => simpa [GalilScaffoldInputHead.left,hg] using hh

theorem comparison_extends (raw : List (Fin 2)) (center radius : ℕ)
    (l r : PlaceHead)
    (hl : GalilScaffoldInputTrace.Represents l.head raw)
    (hr : GalilScaffoldInputTrace.Represents r.head raw)
    (hlp : l.head.focus ≠ none) (hrp : r.head.focus ≠ none)
    (hc : canRight r) (hpal : Manacher.PalAt (encoded raw) center radius)
    (hleft : position l = center-radius) (hright : position r = center+radius)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    Manacher.PalAt (encoded raw) center (radius+1) ∧
      GalilScaffoldInputTrace.Represents (GalilScaffoldInputHead.left l).head raw ∧
      GalilScaffoldInputTrace.Represents (right r).head raw := by
  have hll := (represented_position l.head raw hl hlp).1
  have hrl := (represented_position r.head raw hr hrp).1
  have hb : radius < center := by
    unfold position at hleft
    split at hleft <;> omega
  obtain ⟨hls,hrs⟩ := comparison_positions l r center radius hll hrl hc hb hleft hright
  have hlw := left_word l raw hl hlp
  have hrw := right_word r raw hr hc
  have hrpresent := right_present r raw hr hrp hc
  have hlpresent : (GalilScaffoldInputHead.left l).head.focus ≠ none := by
    intro he
    simp only [GalilScaffoldInputHead.read,he,Option.map_none] at hmatch
    cases hf : (right r).head.focus with
    | none => exact hrpresent hf
    | some a => simp [hf] at hmatch
  exact ⟨matched_extends raw center radius _ _ hlw hrw hlpresent hrpresent
    hpal (by omega) hls hrs hmatch,hlw,hrw⟩

#print axioms comparison_extends
#print axioms matched_extends
#print axioms layout_read_coordinate

theorem palAt_append {α : Type} (word suffix : List α) (center radius : ℕ)
    (hp : Manacher.PalAt word center radius) :
    Manacher.PalAt (word ++ suffix) center radius := by
  refine ⟨hp.1,by simp; have := hp.2.1; omega,?_⟩
  intro i hi
  have hl : center-i < word.length := by have := hp.2.1; omega
  have hr : center+i < word.length := by have := hp.2.1; omega
  rw [List.getElem?_append_left hl,List.getElem?_append_left hr]
  exact hp.2.2 i hi

/-- Arrival extends the encoded word after its old terminal gap;
that gap is not replaced or shifted. -/
theorem encoded_arrival (raw : List (Fin 2)) (a : Fin 2) :
    encoded (raw ++ [a]) = encoded raw ++ [GalilScaffoldPlace.letter a,2] := by
  simp [encoded,pairs_append,pairs,List.append_assoc]

theorem palindrome_arrival (h : Head) (raw : List (Fin 2)) (gap : Bool)
    (hr : GalilScaffoldInputTrace.Reach h raw) (radius : ℕ)
    (hp : Manacher.PalAt (encoded raw)
      (if gap then 2*h.left.length else 2*h.left.length-1) radius) (a : Fin 2) :
    GalilScaffoldInputTrace.Reach (GalilScaffoldInputTrace.append h a) (raw ++ [a]) ∧
    Manacher.PalAt (encoded (raw ++ [a]))
      (if gap then 2*(GalilScaffoldInputTrace.append h a).left.length
       else 2*(GalilScaffoldInputTrace.append h a).left.length-1) radius := by
  refine ⟨GalilScaffoldInputTrace.Reach.arrival hr a,?_⟩
  rw [encoded_arrival]
  exact palAt_append _ _ _ _ hp

/-- Fixed-center successful scan projection. Shift, failure recovery,
and scheduling are not transitions of this invariant yet. -/
structure ScanInvariant (raw : List (Fin 2)) (center radius : ℕ)
    (l r : PlaceHead) : Prop where
  leftRep : GalilScaffoldInputTrace.Represents l.head raw
  rightRep : GalilScaffoldInputTrace.Represents r.head raw
  leftPresent : l.head.focus ≠ none
  rightPresent : r.head.focus ≠ none
  leftPos : position l = center-radius
  rightPos : position r = center+radius
  palindrome : Manacher.PalAt (encoded raw) center radius

theorem scan_initial (raw : List (Fin 2)) (p : PlaceHead)
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none) :
    ScanInvariant raw (position p) 0 p p := by
  have hpos := represented_position p.head raw hh hp
  have hb : position p < (encoded raw).length := by
    simp only [encoded,List.length_append,List.length_singleton,pairs_length]
    unfold position
    split <;> omega
  exact ⟨hh,hh,hp,hp,by simp,by simp,Manacher.palAt_zero hb⟩

theorem scan_first (a : Fin 2) :
    let p := right ⟨GalilScaffoldInputTrace.append GalilScaffoldInputTrace.reset a,true⟩
    ScanInvariant [a] 1 0 p p := by
  have hh : GalilScaffoldInputTrace.Represents (layout [a] [] []) [a] :=
    ⟨[a],[],[],rfl,by simp⟩
  have hi := scan_initial [a] ⟨layout [a] [] [],false⟩ hh (by simp [layout])
  simpa [right,headRight,GalilScaffoldInputTrace.append,GalilScaffoldInputTrace.reset,
    GalilScaffoldInputTrace.moveRight,layout,position] using hi

def arrive (p : PlaceHead) (a : Fin 2) : PlaceHead :=
  ⟨GalilScaffoldInputTrace.append p.head a,p.gap⟩

theorem scan_arrival {raw : List (Fin 2)} {center radius : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw center radius l r) (a : Fin 2) :
    ScanInvariant (raw ++ [a]) center radius (arrive l a) (arrive r a) := by
  refine ⟨GalilScaffoldInputTrace.append_represents hi.leftRep a,
    GalilScaffoldInputTrace.append_represents hi.rightRep a,
    hi.leftPresent,hi.rightPresent,hi.leftPos,hi.rightPos,?_⟩
  rw [encoded_arrival]
  exact palAt_append _ _ _ _ hi.palindrome

theorem scan_matched {raw : List (Fin 2)} {center radius : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw center radius l r) (hc : canRight r)
    (hm : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    ScanInvariant raw center (radius+1) (GalilScaffoldInputHead.left l) (right r) := by
  obtain ⟨hpal,hlrep,hrrep⟩ := comparison_extends raw center radius l r
    hi.leftRep hi.rightRep hi.leftPresent hi.rightPresent hc hi.palindrome
    hi.leftPos hi.rightPos hm
  have hrp := right_present r raw hi.rightRep hi.rightPresent hc
  have hlp : (GalilScaffoldInputHead.left l).head.focus ≠ none := by
    intro he
    simp only [GalilScaffoldInputHead.read,he,Option.map_none] at hm
    cases hf : (right r).head.focus with
    | none => exact hrp hf
    | some a => simp [hf] at hm
  have hll := (represented_position l.head raw hi.leftRep hi.leftPresent).1
  have hrl := (represented_position r.head raw hi.rightRep hi.rightPresent).1
  obtain ⟨hlpos,hrpos⟩ := comparison_positions l r center radius hll hrl hc
    (by have := hpal.1; omega) hi.leftPos hi.rightPos
  exact ⟨hlrep,hrrep,hlp,hrp,hlpos,hrpos,hpal⟩

theorem reads_position {p q : PlaceHead} {xs : List (Fin 3)}
    (hr : Reads p xs q) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none) :
    position q = position p + xs.length := by
  induction hr with
  | stop p => simp
  | next p a hc ha hr ih =>
    have hrep := right_word p raw hh hc
    have hpres := right_present p raw hh hp hc
    have hs := right_position p hc (represented_position p.head raw hh hp).1
    have ht := ih hrep hpres
    simp only [List.length_cons]
    omega

theorem reads_index {p q : PlaceHead} {xs : List (Fin 3)}
    (hr : Reads p xs q) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none)
    (i : ℕ) (hi : i < xs.length) :
    xs[i]? = (encoded raw)[position p+(i+1)]? := by
  induction hr generalizing i with
  | stop p => simp at hi
  | next p a hc ha hr ih =>
    have hrep := right_word p raw hh hc
    have hpres := right_present p raw hh hp hc
    have hpos := right_position p hc (represented_position p.head raw hh hp).1
    cases i with
    | zero =>
      have he := ha.symm.trans (represented_read (right p) raw hrep hpres)
      simpa [hpos] using he
    | succ i =>
      have he := ih hrep hpres i (by simpa using hi)
      have hidx : position (right p)+(i+1) = position p+(i+1+1) := by omega
      rw [hidx] at he
      exact he

theorem watch_input_period {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none)
    (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = GalilScaffoldChainConsume.ready center xs b) :
    ∃ n, position t.machine.verifier = position s.machine.verifier+n ∧
      ∀ i, i+2*(xs.length+1) < n →
        (encoded raw)[position s.machine.verifier+(i+1)]? =
          (encoded raw)[position s.machine.verifier+(i+2*(xs.length+1)+1)]? := by
  obtain ⟨actual,ht,hperiod⟩ := GalilScaffoldChainPrediction.watch_period hr center b xs hs
  refine ⟨actual.length,reads_position ht.reads raw hh hp,?_⟩
  intro i hi
  have he := hperiod i hi
  rw [reads_index ht.reads raw hh hp i (by omega),
    reads_index ht.reads raw hh hp (i+2*(xs.length+1)) hi] at he
  exact he

#print axioms watch_input_period

/-- The periodic predictor is tied pointwise to the same successful input
trace, not merely to an abstract word with period 2h. -/
theorem watch_input_cycle {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none)
    (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = GalilScaffoldChainConsume.ready center xs b) :
    ∃ n, position t.machine.verifier = position s.machine.verifier+n ∧
      ∀ i, i < n → (encoded raw)[position s.machine.verifier+(i+1)]? =
        (GalilScaffoldChainSweep.bounce center b xs)[i % (2*(xs.length+1))]? := by
  obtain ⟨actual,ht,he⟩ := GalilScaffoldChainPrediction.watch_cycles hr center b xs hs
  refine ⟨actual.length,reads_position ht.reads raw hh hp,?_⟩
  intro i hi
  have hlen := congrArg List.length he
  simp only [List.length_take] at hlen
  have hb : i < (GalilScaffoldChainPrediction.cycles
      (GalilScaffoldChainSweep.bounce center b xs) actual.length).length := by omega
  have hx := congrArg (fun w : List (Fin 3) => w[i]?) he
  simp only [List.getElem?_take,hi,if_true] at hx
  rw [GalilScaffoldChainPrediction.cycles_index _ _ _ hb] at hx
  have hsize : (GalilScaffoldChainSweep.bounce center b xs).length =
      2*(xs.length+1) := by simp [GalilScaffoldChainSweep.bounce]; omega
  rw [hsize,reads_index ht.reads raw hh hp i hi] at hx
  exact hx.symm

#print axioms watch_input_cycle

theorem watch_previous_window {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none)
    (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (n : ℕ) (hn : position t.machine.verifier = position s.machine.verifier+n)
    (hfull : 2*(xs.length+1) ≤ n) :
    ∀ k, 0 < k → k ≤ 2*(xs.length+1) →
      (GalilScaffoldChainSweep.bounce center b xs)[(n+k-1) % (2*(xs.length+1))]? =
        (encoded raw)[position t.machine.verifier-2*(xs.length+1)+k]? := by
  obtain ⟨m,hm,hcycle⟩ := watch_input_cycle hr raw hh hp center b xs hs
  have hmn : m = n := by omega
  subst m
  intro k hk hkend
  let i := n-2*(xs.length+1)+k-1
  have hi : i < n := by dsimp only [i]; omega
  have he := hcycle i hi
  have hidx : position s.machine.verifier+(i+1) =
      position t.machine.verifier-2*(xs.length+1)+k := by dsimp only [i]; omega
  have hadd : n+k-1 = i+2*(xs.length+1) := by dsimp only [i]; omega
  rw [hadd,Nat.add_mod]
  simp only [Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  rw [hidx] at he
  exact he.symm

#print axioms watch_previous_window

theorem watch_prediction_window {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none)
    (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (n : ℕ) (hn : position t.machine.verifier = position s.machine.verifier+n)
    (hfull : 2*(xs.length+1) ≤ n) :
    GalilScaffoldChainConsume.symbol t.machine.control.period.focus =
      (encoded raw)[position t.machine.verifier-2*(xs.length+1)+1]? := by
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  have hpos := reads_position ht.reads raw hh hp
  have hlen : actual.length = n := by omega
  have hb : (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b)
      actual).broken = false := by
    rw [← hs,← ht.control,ht.broken,hs]
    rfl
  have hpred := GalilScaffoldChainPrediction.successful_prediction center b xs actual hb
  rw [← hs,← ht.control,hlen] at hpred
  have hwindow := watch_previous_window hr raw hh hp center b xs hs n hn hfull
    1 (by omega) (by omega)
  simpa only [Nat.add_sub_cancel] using hpred.trans hwindow

#print axioms watch_prediction_window

/-- The watch distance counter measures the displacement of that same
physical-list verifier, not merely the length of an unrelated word. -/
theorem watch_displacement {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none) :
    (position t.machine.verifier : ℤ) - position s.machine.verifier =
      GalilScaffoldCounter.value t.machine.control.distance -
        GalilScaffoldCounter.value s.machine.control.distance ∧
      GalilScaffoldInputTrace.Represents t.machine.verifier.head raw := by
  obtain ⟨xs,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  have hs := reads_position ht.reads raw hh hp
  have hd := ht.distance
  refine ⟨?_,reads_word ht.reads raw hh⟩
  rw [hs,Nat.cast_add]
  omega

theorem shift_geometry {c c' l l' : PlaceHead} {cs ls : List (Fin 3)}
    (hc : Reads c cs c') (hl : Reads l ls l') (raw : List (Fin 2))
    (hcrep : GalilScaffoldInputTrace.Represents c.head raw)
    (hlrep : GalilScaffoldInputTrace.Represents l.head raw)
    (hcp : c.head.focus ≠ none) (hlp : l.head.focus ≠ none)
    (radius : ℕ) (hleft : position l = position c-radius)
    (hbound : radius ≤ position c) (hsteps : cs.length ≤ radius)
    (hdouble : ls.length = 2*cs.length) :
    position l' = position c'-(radius-cs.length) ∧
      position c'+(radius-cs.length) = position c+radius := by
  have hcs := reads_position hc raw hcrep hcp
  have hls := reads_position hl raw hlrep hlp
  constructor <;> omega

/-- Shift after one failed comparison: the old palindrome need not
extend. Period agreement through the new right endpoint certifies the
new center instead. The period premise must come from Chain prediction. -/
theorem shift_after_prediction (word : List (Fin 3)) (center radius step : ℕ)
    (hpal : Manacher.PalAt word center radius)
    (hstep : 0 < step) (hsmall : step ≤ radius)
    (hend : center+radius+1 < word.length)
    (hperiod : ∀ j, center-radius ≤ j → j+2*step ≤ center+radius+1 →
      word[j]? = word[j+2*step]?) :
    Manacher.PalAt word (center+step) (radius+1-step) := by
  refine ⟨by have := hpal.1; omega,by omega,?_⟩
  intro i hi
  have hlo : center-radius ≤ center+step-i := by omega
  have hhi : center+step-i ≤ center+radius := by omega
  have hm := Manacher.mirror_getElem? hpal hlo hhi
  have he : 2*center-(center+step-i) = center-step+i := by
    have := hpal.1
    omega
  rw [he] at hm
  have hp := hperiod (center-step+i) (by have := hpal.1; omega)
    (by have := hpal.1; omega)
  have hj : center-step+i+2*step = center+step+i := by
    have := hpal.1
    omega
  rw [hj] at hp
  exact hm.trans hp

/-- In the continuation after a shift, reflection supplies every left
comparison before the last one. The last returns to the original failed
comparison. This statement excludes the absent left sentinel; prediction
alignment with the previous right window must still come from the chain. -/
theorem continuation_pair (word : List (Fin 3)) (center radius step k : ℕ)
    (prediction : ℕ → Option (Fin 3))
    (hpal : Manacher.PalAt word center radius)
    (horigin : radius+1 ≤ center) (hsize : 2*step ≤ radius)
    (hk : 0 < k) (hkend : k ≤ 2*step)
    (hprediction : ∀ i, 0 < i → i ≤ 2*step →
      prediction i = word[center+radius+1-2*step+i]?)
    (hfailed : word[center-radius-1]? ≠ word[center+radius+1]?) :
    (word[center-radius-1+2*step-k]? = prediction k ↔ k < 2*step) := by
  rw [hprediction k hk hkend]
  by_cases hend : k = 2*step
  · subst k
    have hl : center-radius-1+2*step-2*step = center-radius-1 := by omega
    have hr : center+radius+1-2*step+2*step = center+radius+1 := by omega
    rw [hl,hr]
    simp [hfailed]
  · have hinside : center-radius ≤ center-radius-1+2*step-k := by omega
    have hupper : center-radius-1+2*step-k ≤ center+radius := by omega
    have hm := Manacher.mirror_getElem? hpal hinside hupper
    have he : 2*center-(center-radius-1+2*step-k) =
        center+radius+1-2*step+k := by omega
    rw [he] at hm
    exact ⟨fun _ => by omega,fun _ => hm⟩

#print axioms continuation_pair

/-- The initial gap at coordinate zero is an absent input-head sentinel,
not the synthetic gap symbol in encoded. Physical-head refinement is separate. -/
def signedRead (word : List (Fin 3)) (i : ℤ) : Option (Fin 3) :=
  if i ≤ 0 then none else word[i.toNat]?

theorem represented_signed_read (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) :
    GalilScaffoldInputHead.read p = signedRead (encoded raw) (position p) := by
  by_cases hp : p.head.focus = none
  · rcases p with ⟨head,gap⟩
    obtain ⟨xs,rs,qs,rfl,rfl⟩ := hh
    cases xs with
    | nil => cases gap <;> simp [GalilScaffoldInputHead.read,layout,position,signedRead]
    | cons a xs => simp [layout] at hp
  · have hl := (represented_position p.head raw hh hp).1
    have hpos : 0 < position p := by
      unfold position
      split <;> omega
    rw [represented_read p raw hh hp]
    simp only [signedRead,if_neg (show ¬ (position p : ℤ) ≤ 0 by omega),Int.toNat_natCast]

theorem left_signed_read (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left p) =
      signedRead (encoded raw) ((position p : ℤ)-1) := by
  have hpos := left_position p (represented_position p.head raw hh hp).1
  have he : (position (GalilScaffoldInputHead.left p) : ℤ) = (position p : ℤ)-1 := by omega
  rw [represented_signed_read _ raw (left_word p raw hh hp),he]

theorem scan_radius_lt {raw : List (Fin 2)} {center radius : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw center radius l r) : radius < center := by
  have hl := (represented_position l.head raw hi.leftRep hi.leftPresent).1
  have hp := hi.leftPos
  unfold position at hp
  split at hp <;> omega

inductive LeftMoves : PlaceHead → ℕ → PlaceHead → Prop
  | stop (p) : LeftMoves p 0 p
  | next (p) {n q} (hp : p.head.focus ≠ none)
      (rest : LeftMoves (GalilScaffoldInputHead.left p) n q) : LeftMoves p (n+1) q

theorem left_moves_position {p q : PlaceHead} {n : ℕ} (hr : LeftMoves p n q)
    (raw : List (Fin 2)) (hh : GalilScaffoldInputTrace.Represents p.head raw) :
    GalilScaffoldInputTrace.Represents q.head raw ∧ position q+n = position p := by
  induction hr with
  | stop p => exact ⟨hh,by simp⟩
  | next p hp rest ih =>
    have ht := ih (left_word p raw hh hp)
    have hm := left_position p (represented_position p.head raw hh hp).1
    exact ⟨ht.1,by omega⟩

theorem left_moves_append {p q r : PlaceHead} {n m : ℕ}
    (h1 : LeftMoves p n q) (h2 : LeftMoves q m r) : LeftMoves p (n+m) r := by
  induction h1 with
  | stop p => simpa using h2
  | next p hp rest ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using LeftMoves.next p hp (ih h2)

theorem bounded_left_moves (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (n : ℕ) (hn : n ≤ position p) :
    ∃ q, LeftMoves p n q := by
  induction n generalizing p with
  | zero => exact ⟨p,.stop _⟩
  | succ n ih =>
    have hp : p.head.focus ≠ none := by
      rcases p with ⟨head,gap⟩
      obtain ⟨xs,rs,qs,rfl,rfl⟩ := hh
      cases xs with
      | nil => cases gap <;> simp [position,layout] at hn
      | cons a xs => simp [layout]
    have hpos := left_position p (represented_position p.head raw hh hp).1
    obtain ⟨q,hq⟩ := ih (GalilScaffoldInputHead.left p) (left_word p raw hh hp) (by omega)
    exact ⟨q,.next p hp hq⟩

theorem left_moves_read {p q : PlaceHead} {n : ℕ} (hr : LeftMoves p n q)
    (raw : List (Fin 2)) (hh : GalilScaffoldInputTrace.Represents p.head raw) :
    GalilScaffoldInputHead.read q = signedRead (encoded raw) ((position p : ℤ)-n) := by
  obtain ⟨hq,hpos⟩ := left_moves_position hr raw hh
  have he : (position q : ℤ) = (position p : ℤ)-n := by omega
  rw [represented_signed_read q raw hq,he]

#print axioms bounded_left_moves
#print axioms left_moves_read

#print axioms left_signed_read
#print axioms represented_signed_read

theorem scan_failed_signed {raw : List (Fin 2)} {center radius : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw center radius l r) (hc : canRight r)
    (hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right r)) :
    signedRead (encoded raw) ((center : ℤ)-radius-1) ≠
      (encoded raw)[center+radius+1]? := by
  have hlt := scan_radius_lt hi
  have hl := hi.leftPos
  have hr := hi.rightPos
  have hm := right_position r hc
    (represented_position r.head raw hi.rightRep hi.rightPresent).1
  rw [left_signed_read l raw hi.leftRep hi.leftPresent,
    represented_read (right r) raw (right_word r raw hi.rightRep hc)
      (right_present r raw hi.rightRep hi.rightPresent hc)] at hne
  have hleft : (position l : ℤ)-1 = (center : ℤ)-radius-1 := by omega
  have hright : position (right r) = center+radius+1 := by omega
  simpa only [hleft,hright] using hne

#print axioms scan_failed_signed

theorem continuation_pair_signed (word : List (Fin 3)) (center radius step k : ℕ)
    (prediction : ℕ → Option (Fin 3)) (hpal : Manacher.PalAt word center radius)
    (hleft : radius < center) (hsize : 2*step ≤ radius)
    (hk : 0 < k) (hkend : k ≤ 2*step)
    (hprediction : ∀ i, 0 < i → i ≤ 2*step →
      prediction i = word[center+radius+1-2*step+i]?)
    (hfailed : signedRead word ((center : ℤ)-radius-1) ≠ word[center+radius+1]?) :
    (signedRead word ((center : ℤ)-radius-1+2*step-k) = prediction k ↔ k < 2*step) := by
  rw [hprediction k hk hkend]
  have hrad := hpal.1
  by_cases hend : k = 2*step
  · subst k
    have hl : (center : ℤ)-radius-1+2*step-(2*step : ℕ) =
        (center : ℤ)-radius-1 := by push_cast; omega
    have hr : center+radius+1-2*step+2*step = center+radius+1 := by omega
    rw [hl,hr]
    simp [hfailed]
  · let j := ((center : ℤ)-radius-1+2*step-k).toNat
    have hj : (j : ℤ) = (center : ℤ)-radius-1+2*step-k := by
      dsimp only [j]
      exact Int.toNat_of_nonneg (by omega)
    have hlo : center-radius ≤ j := by omega
    have hhi : j ≤ center+radius := by omega
    have hm := Manacher.mirror_getElem? hpal hlo hhi
    have he : 2*center-j = center+radius+1-2*step+k := by omega
    rw [he] at hm
    have hn : ¬ ((center : ℤ)-radius-1+2*step-k ≤ 0) := by omega
    simp only [signedRead,if_neg hn]
    exact ⟨fun _ => by omega,fun _ => hm⟩

#print axioms continuation_pair_signed

theorem scan_continuation_pair {raw : List (Fin 2)} {center radius : ℕ}
    {l r : PlaceHead} (hi : ScanInvariant raw center radius l r) (hc : canRight r)
    (hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right r))
    (step k : ℕ) (prediction : ℕ → Option (Fin 3))
    (hsize : 2*step ≤ radius) (hk : 0 < k) (hkend : k ≤ 2*step)
    (hprediction : ∀ i, 0 < i → i ≤ 2*step →
      prediction i = (encoded raw)[center+radius+1-2*step+i]?) :
    (signedRead (encoded raw) ((center : ℤ)-radius-1+2*step-k) = prediction k ↔
      k < 2*step) :=
  continuation_pair_signed (encoded raw) center radius step k prediction hi.palindrome
    (scan_radius_lt hi) hsize hk hkend hprediction (scan_failed_signed hi hc hne)

#print axioms scan_continuation_pair

/-- The short left palindrome stitches the right-periodic trace across
the old center; old PalAt then reflects periodicity over the left half. -/
theorem period_from_right (word : List (Fin 3)) (center radius step : ℕ)
    (hpal : Manacher.PalAt word center radius) (hsize : 2*step ≤ radius)
    (hshort : Manacher.PalAt word (center-step) step)
    (hright : ∀ j, center < j → j+2*step ≤ center+radius+1 →
      word[j]? = word[j+2*step]?) :
    ∀ j, center-radius ≤ j → j+2*step ≤ center+radius+1 →
      word[j]? = word[j+2*step]? := by
  have hrc := hpal.1
  have seam : ∀ j, center-2*step ≤ j → j ≤ center →
      word[j]? = word[j+2*step]? := by
    intro j hjlo hjhi
    have hs := Manacher.mirror_getElem? hshort (by omega) (by omega)
      (p := j)
    have hm := Manacher.mirror_getElem? hpal (by omega) (by omega)
      (p := j+2*step)
    have he : 2*(center-step)-j = 2*center-(j+2*step) := by omega
    rw [he] at hs
    exact hs.trans hm.symm
  have rightClosed : ∀ j, center ≤ j → j+2*step ≤ center+radius+1 →
      word[j]? = word[j+2*step]? := by
    intro j hj hb
    by_cases he : j = center
    · subst j; exact seam center (by omega) (by omega)
    · exact hright j (by omega) hb
  intro j hj hb
  by_cases hr : center ≤ j
  · exact rightClosed j hr hb
  by_cases hc : center ≤ j+2*step
  · exact seam j (by omega) (by omega)
  have hm1 := Manacher.mirror_getElem? hpal hj (by omega)
  have hm2 := Manacher.mirror_getElem? hpal (p := j+2*step) (by omega) (by omega)
  have hp := rightClosed (2*center-(j+2*step)) (by omega) (by omega)
  have he : 2*center-(j+2*step)+2*step = 2*center-j := by omega
  rw [he] at hp
  exact hm1.trans (hp.symm.trans hm2.symm)

theorem shift_from_right (word : List (Fin 3)) (center radius step : ℕ)
    (hpal : Manacher.PalAt word center radius) (hstep : 0 < step)
    (hsize : 2*step ≤ radius) (hshort : Manacher.PalAt word (center-step) step)
    (hend : center+radius+1 < word.length)
    (hright : ∀ j, center < j → j+2*step ≤ center+radius+1 →
      word[j]? = word[j+2*step]?) :
    Manacher.PalAt word (center+step) (radius+1-step) :=
  shift_after_prediction word center radius step hpal hstep (by omega) hend
    (period_from_right word center radius step hpal hsize hshort hright)

/-- After a complete only-cycle the current radius is oldRadius+step.
The short palindrome needed for another shift is inherited from the old
center, so no new DP candidate is required on this branch. -/
theorem reshift_from_right (word : List (Fin 3)) (center radius step : ℕ)
    (hold : Manacher.PalAt word center step)
    (hcurrent : Manacher.PalAt word (center+step) (radius+step))
    (hstep : 0 < step) (hsmall : step ≤ radius)
    (hend : center+step+(radius+step)+1 < word.length)
    (hright : ∀ j, center+step < j →
      j+2*step ≤ center+step+(radius+step)+1 → word[j]? = word[j+2*step]?) :
    Manacher.PalAt word (center+2*step) (radius+1) := by
  have hshort : Manacher.PalAt word center step := hold
  have hshort' : Manacher.PalAt word (center+step-step) step := by
    simpa using hshort
  have h := shift_from_right word (center+step) (radius+step) step hcurrent hstep
    (by omega) hshort' hend hright
  have hc : center+step+step = center+2*step := by omega
  have hr : radius+step+1-step = radius+1 := by omega
  simpa only [hc,hr] using h

#print axioms reshift_from_right

theorem backward_palindrome (word w : List (Fin 3)) (center step : ℕ)
    (hcenter : center < word.length) (hbound : 2*step ≤ center)
    (hlen : 2*step+1 ≤ w.length)
    (hpal : (w.take (2*step+1)).reverse = w.take (2*step+1))
    (hcoords : ∀ i, i ≤ 2*step → w[i]? = word[center-i]?) :
    Manacher.PalAt word (center-step) step := by
  refine ⟨by omega,by omega,?_⟩
  intro i hi
  have hl : (w.take (2*step+1)).length = 2*step+1 := by
    simp [List.length_take,Nat.min_eq_left hlen]
  have he := congrArg (fun v : List (Fin 3) => v[step+i]?) hpal
  rw [List.getElem?_reverse' (show step+i+(step-i)+1 =
    (w.take (2*step+1)).length by rw [hl]; omega)] at he
  have hi1 : step-i < 2*step+1 := by omega
  have hi2 : step+i < 2*step+1 := by omega
  simp only [List.getElem?_take,hi1,hi2,if_true] at he
  rw [hcoords (step-i) (by omega),hcoords (step+i) (by omega)] at he
  have h1 : center-(step+i) = center-step-i := by omega
  have h2 : center-(step-i) = center-step+i := by omega
  rw [h1,h2] at he
  exact he.symm

theorem candidate_short_palindrome (a : Fin 2) (ls suffix : List (Fin 2)) (gap : Bool)
    (w : List (Fin 3)) (span lower step : ℕ)
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take span)
    (hc : GalilDpCorrect.Candidate w lower step) :
    let center := if gap then 2*(ls.length+1) else 2*(ls.length+1)-1
    Manacher.PalAt (encoded ((a :: ls).reverse ++ suffix)) (center-step) step := by
  let center := if gap then 2*(ls.length+1) else 2*(ls.length+1)-1
  let stream := GalilScaffoldPlace.stream ⟨a :: ls,gap⟩
  let word := encoded ((a :: ls).reverse ++ suffix)
  have hslen : stream.length = center := by
    cases gap <;> simp [stream,center,GalilScaffoldPlace.stream,← pairs_gaps,pairs_length] <;> omega
  have hwlen : w.length = min span center := by rw [hw,List.length_take]; exact congrArg (min span) hslen
  have hlen := hc.2.1
  have hb : 2*step ≤ center := by omega
  have hcenter : center < word.length := by
    cases gap <;> simp [center,word,encoded,pairs_length] <;> omega
  have hrev : (word.take (center+1)).reverse = stream ++ [2] := by
    cases gap with
    | false =>
      have he : 2*(ls.length+1)-1+1 = 2*(ls.length+1) := by omega
      simpa only [word,center,Bool.false_eq_true,if_false,he,stream] using left_window a ls suffix
    | true =>
      have hl : (a :: ls).reverse.length = ls.length+1 := by simp
      dsimp only [word,center]
      rw [if_pos rfl,← hl,encoded_take,encoded_reverse,List.reverse_reverse]
      simp [stream,encoded,pairs,pairs_gaps,GalilScaffoldPlace.stream]
  apply backward_palindrome word w center step hcenter hb (by omega) hc.2.2.1
  intro i hi
  have his : i < stream.length := by rw [hslen]; omega
  have hin : i < span := by omega
  have hplen : (word.take (center+1)).length = center+1 := by simp; omega
  have he := congrArg (fun v : List (Fin 3) => v[i]?) hrev
  rw [List.getElem?_reverse' (show i+(center-i)+1 = (word.take (center+1)).length by
    rw [hplen]; omega),List.getElem?_append_left his] at he
  simp only [List.getElem?_take,show center-i < center+1 by omega,if_true] at he
  rw [hw]
  simp only [List.getElem?_take,hin,if_true]
  exact he.symm

theorem watch_progress {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) :
    GalilScaffoldCounter.value t.machine.control.distance + GalilScaffoldCounter.value t.lag =
      GalilScaffoldCounter.value s.machine.control.distance + GalilScaffoldCounter.value s.lag +
        (bs.count true : ℤ) := by
  have hb := GalilScaffoldChainWatch.run_balance hr
  have hm := GalilScaffoldChainPrediction.margin_exact hr
  unfold GalilScaffoldChainWatch.balance at hb
  omega

theorem caught_position {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none) (initialRadius : ℕ)
    (hd : GalilScaffoldCounter.value s.machine.control.distance = 0)
    (hl : GalilScaffoldCounter.value s.lag = initialRadius)
    (hz : GalilScaffoldCounter.value t.lag = 0) :
    position t.machine.verifier = position s.machine.verifier + initialRadius + bs.count true := by
  have he := (watch_displacement hr raw hh hp).1
  have hc := watch_progress hr
  omega

theorem prepared_caught_position {s t : GalilScaffoldChainWatch.State} {events : List Bool}
    (hr : GalilScaffoldChainWatch.Run s events t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none)
    (radius : GalilScaffoldCounter.Counter) (initialRadius : ℕ)
    (hv : GalilScaffoldCounter.value radius = initialRadius)
    (sm dm : Bool) (copyMatches backMatches : List Bool)
    (hprepared : s.lag = (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius)
      (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches)).lag)
    (hd : GalilScaffoldCounter.value s.machine.control.distance = 0)
    (hz : GalilScaffoldCounter.value t.lag = 0) :
    position t.machine.verifier = position s.machine.verifier + initialRadius +
      (sm :: (copyMatches ++ dm :: backMatches) ++ events).count true := by
  have hprep := (GalilScaffoldChainCredits.prep_value radius sm dm copyMatches backMatches).2
  have hl : GalilScaffoldCounter.value s.lag =
      (initialRadius + (sm :: (copyMatches ++ dm :: backMatches)).count true : ℕ) := by
    rw [hprepared,hprep,hv,Nat.cast_add]
  have he := caught_position hr raw hh hp
    (initialRadius + (sm :: (copyMatches ++ dm :: backMatches)).count true) hd hl hz
  have hc : (sm :: (copyMatches ++ dm :: backMatches) ++ events).count true =
      (sm :: (copyMatches ++ dm :: backMatches)).count true + events.count true := by
    exact List.count_append
  rw [hc]
  omega

/-- Radius projection of an uninterrupted accepted-comparison interval:
true increments, false pauses. A failed non-shift comparison exits this
projection; identifying these guards in Galil remains a refinement task. -/
def acceptedRadius : GalilScaffoldCounter.Counter → List Bool → GalilScaffoldCounter.Counter
  | radius, [] => radius
  | radius, b :: bs => acceptedRadius (if b then GalilScaffoldCounter.inc radius else radius) bs

theorem acceptedRadius_value (radius : GalilScaffoldCounter.Counter) (bs : List Bool) :
    GalilScaffoldCounter.value (acceptedRadius radius bs) =
      GalilScaffoldCounter.value radius + (bs.count true : ℤ) := by
  induction bs generalizing radius with
  | nil => simp [acceptedRadius]
  | cons b bs ih =>
    cases b <;> simp [acceptedRadius,ih,GalilScaffoldCounter.inc_value] <;> omega

theorem acceptedRadius_canonical (radius : GalilScaffoldCounter.Counter) (bs : List Bool)
    (hc : GalilScaffoldCounter.Canonical radius) :
    GalilScaffoldCounter.Canonical (acceptedRadius radius bs) := by
  induction bs generalizing radius with
  | nil => exact hc
  | cons b bs ih =>
    apply ih
    cases b
    · exact hc
    · exact GalilScaffoldCounter.inc_canonical radius hc

theorem prepared_radius_alignment {s t : GalilScaffoldChainWatch.State} {events : List Bool}
    (hr : GalilScaffoldChainWatch.Run s events t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none)
    (radius : GalilScaffoldCounter.Counter) (sm dm : Bool) (copyMatches backMatches : List Bool)
    (hprepared : s.lag = (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius)
      (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches)).lag)
    (hd : GalilScaffoldCounter.value s.machine.control.distance = 0)
    (hz : GalilScaffoldCounter.value t.lag = 0) :
    (position t.machine.verifier : ℤ) = position s.machine.verifier +
      GalilScaffoldCounter.value (acceptedRadius radius
        ((sm :: (copyMatches ++ dm :: backMatches)) ++ events)) := by
  have hprep := (GalilScaffoldChainCredits.prep_value radius sm dm copyMatches backMatches).2
  have hprogress := watch_progress hr
  have hposition := (watch_displacement hr raw hh hp).1
  rw [hprepared,hprep] at hprogress
  rw [acceptedRadius_value,List.count_append,Nat.cast_add]
  omega

theorem position_bound (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none) :
    position p < (encoded raw).length := by
  have hb := represented_position p.head raw hh hp
  simp only [encoded,List.length_append,List.length_singleton,pairs_length]
  unfold position
  split <;> omega

theorem canRight_of_bound (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none)
    (hb : position p+1 < (encoded raw).length) : canRight p := by
  rcases p with ⟨h,gap⟩
  cases gap with
  | false => exact Or.inl rfl
  | true =>
    obtain ⟨xs,rs,qs,rfl,rfl⟩ := hh
    cases xs with
    | nil => simp [layout] at hp
    | cons a xs =>
      cases rs with
      | cons b rs => simp [canRight,layout]
      | nil =>
        cases qs with
        | cons b qs => simp [canRight,layout]
        | nil => simp [position,layout,encoded,pairs_length] at hb

theorem bounded_right_moves (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none)
    (n : ℕ) (hb : position p+n < (encoded raw).length) :
    ∃ actual q, Reads p actual q ∧ actual.length = n ∧
      position q = position p+n ∧ GalilScaffoldInputTrace.Represents q.head raw ∧
      q.head.focus ≠ none := by
  induction n generalizing p with
  | zero => exact ⟨[],p,.stop _,rfl,by simp,hh,hp⟩
  | succ n ih =>
    have hc := canRight_of_bound p raw hh hp (by omega)
    have hr := right_word p raw hh hc
    have hpr := right_present p raw hh hp hc
    have hpos := right_position p hc (represented_position p.head raw hh hp).1
    obtain ⟨actual,q,hreads,hlen,hqpos,hqrep,hqp⟩ := ih (right p) hr hpr (by omega)
    have hread : ∃ a, GalilScaffoldInputHead.read (right p) = some a := by
      cases he : (right p).head.focus with
      | none => exact False.elim (hpr he)
      | some a => exact ⟨if (right p).gap then 2 else GalilScaffoldPlace.letter a,
          by simp [GalilScaffoldInputHead.read,he]⟩
    obtain ⟨a,ha⟩ := hread
    exact ⟨a :: actual,q,.next p a hc ha hreads,by simp [hlen],by omega,hqrep,hqp⟩

theorem left_return_legal (p : PlaceHead) (hl : 0 < p.head.left.length) :
    canRight (GalilScaffoldInputHead.left p) ∧
      right (GalilScaffoldInputHead.left p) = p := by
  constructor
  · rcases p with ⟨⟨f,ls,rs,qs⟩,gap⟩
    cases ls with
    | nil => simp at hl
    | cons a ls => cases gap <;> simp [canRight,GalilScaffoldInputHead.left,moveLeft]
  · apply right_left p
    intro _ he
    simp [he] at hl

/-- After the comparison's left step, the first shift-right returns to
the original head, even when the comparison reached the absent sentinel. -/
theorem shifted_left_moves (p : PlaceHead) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none)
    (n : ℕ) (hb : position p+n < (encoded raw).length) :
    ∃ actual q, Reads (GalilScaffoldInputHead.left p) actual q ∧ actual.length = n+1 ∧
      position q = position p+n ∧ GalilScaffoldInputTrace.Represents q.head raw ∧
      q.head.focus ≠ none := by
  obtain ⟨hc,he⟩ := left_return_legal p (represented_position p.head raw hh hp).1
  obtain ⟨actual,q,hr,hlen,hpos,hrep,hpres⟩ := bounded_right_moves p raw hh hp n hb
  have hread : ∃ a, GalilScaffoldInputHead.read p = some a := by
    cases hf : p.head.focus with
    | none => exact False.elim (hp hf)
    | some a => exact ⟨if p.gap then 2 else GalilScaffoldPlace.letter a,
        by simp [GalilScaffoldInputHead.read,hf]⟩
  obtain ⟨a,ha⟩ := hread
  refine ⟨a :: actual,q,?_,by simp [hlen],hpos,hrep,hpres⟩
  apply Reads.next _ a hc (by rw [he]; exact ha)
  simpa only [he] using hr

/-- The head projection of one shift tick: one center move followed by two
left-head moves. Counter and chain updates are not part of this relation. -/
inductive ShiftHeads : PlaceHead → PlaceHead → ℕ → PlaceHead → PlaceHead → Prop
  | stop (c l) : ShiftHeads c l 0 c l
  | next (c l) {n ce le} (hc : canRight c) (hl : canRight l)
      (hl' : canRight (right l))
      (rest : ShiftHeads (right c) (right (right l)) n ce le) :
      ShiftHeads c l (n+1) ce le

theorem reads_shift_heads {c l ce le : PlaceHead} {cw lw : List (Fin 3)}
    (hc : Reads c cw ce) (hl : Reads l lw le) (hlen : lw.length = 2*cw.length) :
    ShiftHeads c l cw.length ce le := by
  induction hc generalizing l lw with
  | stop c =>
    have he : lw = [] := by
      cases lw with
      | nil => rfl
      | cons a rest => simp at hlen
    subst lw
    cases hl
    exact .stop _ _
  | next c a hcan ha hr ih =>
    cases hl with
    | stop l => simp at hlen
    | next l b hlcan hb hlrest =>
      cases hlrest with
      | stop l' => simp at hlen; omega
      | next l' d hlcan' hd htail =>
        apply ShiftHeads.next c l hcan hlcan hlcan'
        apply ih htail
        simp only [List.length_cons] at hlen
        omega

#print axioms reads_shift_heads

/-- The outer shift counters, updated on exactly the same head ticks.
The chain's private counters and mode still require a separate refinement. -/
structure ShiftState where
  center : PlaceHead
  left : PlaceHead
  remaining : GalilScaffoldCounter.Counter
  radius : GalilScaffoldCounter.Counter
  length : GalilScaffoldCounter.Counter

def shiftTick (s : ShiftState) : ShiftState :=
  ⟨right s.center, right (right s.left), GalilScaffoldCounter.dec s.remaining,
    GalilScaffoldCounter.dec s.radius,
    GalilScaffoldCounter.dec (GalilScaffoldCounter.dec s.length)⟩

inductive ShiftRun : ShiftState → ℕ → ShiftState → Prop
  | stop (s) : ShiftRun s 0 s
  | next (s) {n t} (enabled : GalilScaffoldCounter.positive s.remaining = true)
      (hc : canRight s.center) (hl : canRight s.left)
      (hl' : canRight (right s.left)) (rest : ShiftRun (shiftTick s) n t) :
      ShiftRun s (n+1) t

def ShiftCanonical (s : ShiftState) : Prop :=
  GalilScaffoldCounter.Canonical s.remaining ∧
  GalilScaffoldCounter.Canonical s.radius ∧ GalilScaffoldCounter.Canonical s.length

theorem shift_run_center {s t : ShiftState} {n : ℕ} (hr : ShiftRun s n t)
    (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.center.head raw)
    (hp : s.center.head.focus ≠ none) :
    GalilScaffoldInputTrace.Represents t.center.head raw ∧ t.center.head.focus ≠ none ∧
      position t.center = position s.center+n := by
  induction hr with
  | stop s => exact ⟨hh,hp,by simp⟩
  | next s he hc hl hl' rest ih =>
    have hrep := right_word s.center raw hh hc
    have hpres := right_present s.center raw hh hp hc
    have hpos := right_position s.center hc (represented_position s.center.head raw hh hp).1
    obtain ⟨htrep,htpres,htpos⟩ := ih hrep hpres
    simp only [shiftTick] at htpos
    exact ⟨htrep,htpres,by omega⟩

#print axioms shift_run_center

/-- Scala Chain.shiftOne on the existing watch state; the verifier and
period tape do not move during a center shift. -/
def chainShiftOne (s : GalilScaffoldChainWatch.State) : GalilScaffoldChainWatch.State :=
  { s with machine := { s.machine with control := { s.machine.control with distance := GalilScaffoldCounter.dec s.machine.control.distance, boundary := GalilScaffoldCounter.dec s.machine.control.boundary, last := GalilScaffoldCounter.dec s.machine.control.last } }, margin := GalilScaffoldCounter.dec s.margin }

inductive ChainShiftRun : ShiftState → GalilScaffoldChainWatch.State →
    GalilScaffoldCounter.Counter → ℕ → ShiftState → GalilScaffoldChainWatch.State →
    GalilScaffoldCounter.Counter → Prop
  | stop (s w cycle) : ChainShiftRun s w cycle 0 s w cycle
  | next (s w cycle) {n t v finish}
      (enabled : GalilScaffoldCounter.positive s.remaining = true)
      (hc : canRight s.center) (hl : canRight s.left) (hl' : canRight (right s.left))
      (rest : ChainShiftRun (shiftTick s) (chainShiftOne w)
        (GalilScaffoldCounter.inc (GalilScaffoldCounter.inc cycle)) n t v finish) :
      ChainShiftRun s w cycle (n+1) t v finish

theorem shift_run_chain {s t : ShiftState} {n : ℕ} (hr : ShiftRun s n t)
    (w : GalilScaffoldChainWatch.State) (cycle : GalilScaffoldCounter.Counter) :
    ∃ v finish, ChainShiftRun s w cycle n t v finish := by
  induction hr generalizing w cycle with
  | stop s => exact ⟨w,cycle,.stop _ _ _⟩
  | next s he hc hl hl' rest ih =>
    obtain ⟨v,finish,hv⟩ := ih (chainShiftOne w)
      (GalilScaffoldCounter.inc (GalilScaffoldCounter.inc cycle))
    exact ⟨v,finish,.next s w cycle he hc hl hl' hv⟩

theorem chain_shift_values {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish) :
    GalilScaffoldCounter.value v.machine.control.distance =
      GalilScaffoldCounter.value w.machine.control.distance - n ∧
    GalilScaffoldCounter.value v.machine.control.boundary =
      GalilScaffoldCounter.value w.machine.control.boundary - n ∧
    GalilScaffoldCounter.value v.machine.control.last =
      GalilScaffoldCounter.value w.machine.control.last - n ∧
    GalilScaffoldCounter.value v.margin = GalilScaffoldCounter.value w.margin - n ∧
    GalilScaffoldCounter.value finish = GalilScaffoldCounter.value cycle + 2*n ∧
    v.machine.verifier = w.machine.verifier ∧
    v.machine.control.period = w.machine.control.period ∧ v.lag = w.lag := by
  induction hr with
  | stop s w cycle => simp
  | next s w cycle he hc hl hl' rest ih =>
    simp only [chainShiftOne,GalilScaffoldCounter.dec_value,
      GalilScaffoldCounter.inc_value] at ih
    simp only [Nat.cast_add,Nat.cast_one]
    exact ⟨by omega,by omega,by omega,by omega,by omega,ih.2.2.2.2.2⟩

#print axioms shift_run_chain
#print axioms chain_shift_values

theorem chain_shift_prediction {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish) :
    GalilScaffoldChainPrediction.SamePrediction v.machine.control w.machine.control := by
  induction hr with
  | stop s w cycle => exact ⟨rfl,rfl⟩
  | next s w cycle he hc hl hl' rest ih => exact ih

theorem chain_shift_future_prediction {s t : ShiftState}
    {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish) (word : List (Fin 3)) :
    GalilScaffoldChainConsume.symbol
      (GalilScaffoldChainSweep.run v.machine.control word).period.focus =
    GalilScaffoldChainConsume.symbol
      (GalilScaffoldChainSweep.run w.machine.control word).period.focus := by
  have he := (GalilScaffoldChainPrediction.run_same_prediction
    (chain_shift_prediction hr) word).1
  rw [he]

#print axioms chain_shift_future_prediction

theorem chain_shift_broken {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish) :
    v.machine.control.broken = w.machine.control.broken := by
  induction hr with
  | stop s w cycle => rfl
  | next s w cycle he hc hl hl' rest ih => exact ih

theorem chain_shift_future_success {s t : ShiftState}
    {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish) (word : List (Fin 3))
    (hs : (GalilScaffoldChainSweep.run w.machine.control word).broken = false) :
    (GalilScaffoldChainSweep.run v.machine.control word).broken = false := by
  rw [GalilScaffoldChainPrediction.run_same_broken
    (chain_shift_prediction hr) (chain_shift_broken hr) word]
  exact hs

theorem chain_shift_continued_prediction {s t : ShiftState}
    {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish)
    (center b : Fin 3) (xs pre extra : List (Fin 3))
    (hw : w.machine.control = GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready center xs b) pre)
    (hs : (GalilScaffoldChainSweep.run v.machine.control extra).broken = false) :
    GalilScaffoldChainConsume.symbol
      (GalilScaffoldChainSweep.run v.machine.control extra).period.focus =
      (GalilScaffoldChainSweep.bounce center b xs)[(pre.length+extra.length) % (2*(xs.length+1))]? := by
  have hp := chain_shift_prediction hr
  have hb := chain_shift_broken hr
  rw [hw] at hp hb
  exact GalilScaffoldChainPrediction.continued_prediction center b xs pre extra
    v.machine.control hp hb hs

#print axioms chain_shift_continued_prediction

theorem shifted_prediction_window {start w v : GalilScaffoldChainWatch.State}
    {bs : List Bool} {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hw : GalilScaffoldChainWatch.Run start bs w)
    (hr : ChainShiftRun s w cycle n t v finish)
    (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents start.machine.verifier.head raw)
    (hp : start.machine.verifier.head.focus ≠ none)
    (center b : Fin 3) (xs extra : List (Fin 3))
    (hstart : start.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (hfull : position start.machine.verifier+2*(xs.length+1) ≤ position w.machine.verifier)
    (hextra : extra.length < 2*(xs.length+1))
    (hsuccess : (GalilScaffoldChainSweep.run v.machine.control extra).broken = false) :
    GalilScaffoldChainConsume.symbol
      (GalilScaffoldChainSweep.run v.machine.control extra).period.focus =
      (encoded raw)[position w.machine.verifier-2*(xs.length+1)+(extra.length+1)]? := by
  obtain ⟨pre,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hw
  have hpos := reads_position ht.reads raw hh hp
  have hcontrol := ht.control
  rw [hstart] at hcontrol
  have hpred := chain_shift_continued_prediction hr center b xs pre extra hcontrol hsuccess
  have hwindow := watch_previous_window hw raw hh hp center b xs hstart pre.length hpos
    (by omega) (extra.length+1) (by omega) (by omega)
  have he : pre.length+(extra.length+1)-1 = pre.length+extra.length := by omega
  rw [he] at hwindow
  exact hpred.trans hwindow

#print axioms shifted_prediction_window

/-- The actual left read versus actual period token in a successful
continuation. Timing/left-coordinate hypotheses remain explicit. -/
theorem shifted_check_pair {start w v : GalilScaffoldChainWatch.State}
    {bs : List Bool} {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hw : GalilScaffoldChainWatch.Run start bs w)
    (hr : ChainShiftRun s w cycle n t v finish)
    (raw : List (Fin 2)) (c radius : ℕ) (l r resumeLeft currentLeft : PlaceHead)
    (hi : ScanInvariant raw c radius l r) (hcan : canRight r)
    (hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right r))
    (hh : GalilScaffoldInputTrace.Represents start.machine.verifier.head raw)
    (hp : start.machine.verifier.head.focus ≠ none)
    (center b : Fin 3) (xs extra : List (Fin 3))
    (hstart : start.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (hstartPos : position start.machine.verifier = c)
    (hend : position w.machine.verifier = c+radius+1)
    (hsize : 2*(xs.length+1) ≤ radius) (hextra : extra.length < 2*(xs.length+1))
    (hsuccess : (GalilScaffoldChainSweep.run v.machine.control extra).broken = false)
    (hresume : ScanInvariant raw (c+(xs.length+1)) (radius+1-(xs.length+1))
      resumeLeft (right r))
    (hmoves : LeftMoves resumeLeft (extra.length+1) currentLeft) :
    (GalilScaffoldInputHead.read currentLeft = GalilScaffoldChainConsume.symbol
      (GalilScaffoldChainSweep.run v.machine.control extra).period.focus ↔
      extra.length+1 < 2*(xs.length+1)) := by
  have hpred := shifted_prediction_window hw hr raw hh hp center b xs extra hstart
    (by omega) hextra hsuccess
  obtain ⟨hlrep,hmpos⟩ := left_moves_position hmoves raw hresume.leftRep
  have hrespos := hresume.leftPos
  have hlt := scan_radius_lt hi
  have hlpos : (position currentLeft : ℤ) =
      (c : ℤ)-radius-1+2*(xs.length+1)-(extra.length+1) := by omega
  rw [hend] at hpred
  rw [represented_signed_read currentLeft raw hlrep,hlpos,hpred]
  exact scan_continuation_pair hi hcan hne (xs.length+1) (extra.length+1)
    (fun i => (encoded raw)[c+radius+1-2*(xs.length+1)+i]?)
    hsize (by omega) (by omega) (by intros; rfl)

#print axioms shifted_check_pair

#print axioms chain_shift_future_success

theorem chain_shift_order {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish)
    (ho : GalilScaffoldChainRestart.Ordered w.machine.control) :
    GalilScaffoldChainRestart.Ordered v.machine.control := by
  obtain ⟨hd,hb,hl,_⟩ := chain_shift_values hr
  unfold GalilScaffoldChainRestart.Ordered at *
  omega

theorem chain_shift_control_canonical {s t : ShiftState}
    {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish)
    (hl : GalilScaffoldCounter.Canonical w.machine.control.last)
    (hb : GalilScaffoldCounter.Canonical w.machine.control.boundary)
    (hd : GalilScaffoldCounter.Canonical w.machine.control.distance) :
    GalilScaffoldCounter.Canonical v.machine.control.last ∧
      GalilScaffoldCounter.Canonical v.machine.control.boundary ∧
      GalilScaffoldCounter.Canonical v.machine.control.distance := by
  induction hr with
  | stop s w cycle => exact ⟨hl,hb,hd⟩
  | next s w cycle he h1 h2 h3 rest ih =>
    exact ih (GalilScaffoldCounter.dec_canonical _ hl)
      (GalilScaffoldCounter.dec_canonical _ hb) (GalilScaffoldCounter.dec_canonical _ hd)

/-- A positive last boundary surviving the shift remains positive under
every subsequent consume, including the terminal failing consume. -/
theorem chain_shift_future_last {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish)
    (ho : GalilScaffoldChainRestart.Ordered w.machine.control)
    (hl : GalilScaffoldCounter.Canonical w.machine.control.last)
    (hb : GalilScaffoldCounter.Canonical w.machine.control.boundary)
    (hd : GalilScaffoldCounter.Canonical w.machine.control.distance)
    (hpos : (n : ℤ) < GalilScaffoldCounter.value w.machine.control.last)
    (extra : List (Fin 3)) :
    GalilScaffoldCounter.positive
      (GalilScaffoldChainSweep.run v.machine.control extra).last = true := by
  have hlast := (chain_shift_values hr).2.2.1
  have horder := GalilScaffoldChainRestart.run_order v.machine.control extra (chain_shift_order hr ho)
  obtain ⟨hl',hb',hd'⟩ := chain_shift_control_canonical hr hl hb hd
  have hcanon := GalilScaffoldChainRestart.run_canonical v.machine.control extra hl' hb' hd'
  apply (GalilScaffoldCounter.positive_iff _ hcanon.1).2
  omega

#print axioms chain_shift_future_last

theorem watch_last_lower {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (hd : 4*(xs.length+1) ≤ GalilScaffoldCounter.value t.machine.control.distance) :
    3*(xs.length+1) ≤ GalilScaffoldCounter.value t.machine.control.last := by
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  let initial := GalilScaffoldChainConsume.ready center xs b
  let word := GalilScaffoldChainSweep.bounce center b xs
  let expected := word ++ word
  have hf := GalilScaffoldChainSweep.four_boundaries center b xs
  have he : (GalilScaffoldChainSweep.run initial expected).broken = false := hf.2.2.2.2.2.2
  have ha : (GalilScaffoldChainSweep.run initial actual).broken = false := by
    change (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) actual).broken = false
    rw [← hs,← ht.control,ht.broken,hs]
    rfl
  have hv := ht.distance
  rw [hs] at hv
  have hz : GalilScaffoldCounter.value (GalilScaffoldChainConsume.ready center xs b).distance = 0 := rfl
  rw [hz,zero_add] at hv
  have hlen : expected.length ≤ actual.length := by
    have hl : expected.length = 4*(xs.length+1) := by
      simp [expected,word,GalilScaffoldChainSweep.bounce]; omega
    rw [hl]
    omega
  have hp := GalilScaffoldChainPrediction.successful_prefix expected actual initial he ha hlen
  have hsplit : actual = expected ++ actual.drop expected.length := by
    have heq := List.take_append_drop expected.length actual
    rw [hp] at heq
    exact heq.symm
  have ho : GalilScaffoldChainRestart.Ordered initial := by
    simp [GalilScaffoldChainRestart.Ordered,initial,GalilScaffoldChainConsume.ready,
      GalilScaffoldCounter.reset,GalilScaffoldCounter.value]
  have hm := GalilScaffoldChainRestart.run_order initial expected ho
  have hl := GalilScaffoldChainRestart.run_order (GalilScaffoldChainSweep.run initial expected)
    (actual.drop expected.length) hm.1
  have hlast : GalilScaffoldCounter.value (GalilScaffoldChainSweep.run initial expected).last =
      3*(xs.length+1) := hf.2.2.2.1
  rw [ht.control,hs,hsplit,GalilScaffoldChainSweep.run_append]
  exact hlast ▸ hl.2

#print axioms watch_last_lower

theorem watch_shift_last_positive {start w v : GalilScaffoldChainWatch.State}
    {bs : List Bool} {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter}
    (center b : Fin 3) (xs extra : List (Fin 3))
    (hw : GalilScaffoldChainWatch.Run start bs w)
    (hr : ChainShiftRun s w cycle (xs.length+1) t v finish)
    (hs : start.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (hd : 4*(xs.length+1) ≤ GalilScaffoldCounter.value w.machine.control.distance) :
    GalilScaffoldCounter.positive
      (GalilScaffoldChainSweep.run v.machine.control extra).last = true := by
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hw
  have hinit : GalilScaffoldChainRestart.Ordered (GalilScaffoldChainConsume.ready center xs b) := by
    simp [GalilScaffoldChainRestart.Ordered,GalilScaffoldChainConsume.ready,
      GalilScaffoldCounter.reset,GalilScaffoldCounter.value]
  have ho := GalilScaffoldChainRestart.run_order
    (GalilScaffoldChainConsume.ready center xs b) actual hinit
  have hc := GalilScaffoldChainRestart.run_canonical
    (GalilScaffoldChainConsume.ready center xs b) actual (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  rw [← hs,← ht.control] at ho hc
  have hl := watch_last_lower hw center b xs hs hd
  exact chain_shift_future_last hr ho.1 hc.1 hc.2.1 hc.2.2 (by omega) extra

#print axioms watch_shift_last_positive

theorem history_terminal_last {start w v current : GalilScaffoldChainWatch.State}
    {bs : List Bool} {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter}
    (center b : Fin 3) (xs extra : List (Fin 3))
    (hw : GalilScaffoldChainWatch.Run start bs w)
    (hr : ChainShiftRun s w cycle (xs.length+1) t v finish)
    (hs : start.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (hd : 4*(xs.length+1) ≤ GalilScaffoldCounter.value w.machine.control.distance)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra current.machine) :
    GalilScaffoldCounter.positive (consume current.machine).control.last = true := by
  cases ha : GalilScaffoldInputHead.read (right current.machine.verifier) with
  | none =>
    have hl := watch_shift_last_positive center b xs extra hw hr hs hd
    rw [← ht.control] at hl
    cases htoken : GalilScaffoldChainConsume.symbol current.machine.control.period.focus <;>
      simpa [consume,ha,GalilScaffoldChainConsume.consume,htoken] using hl
  | some a =>
    have hl := watch_shift_last_positive center b xs (extra ++ [a]) hw hr hs hd
    rw [GalilScaffoldChainSweep.run_append,← ht.control] at hl
    simpa [consume,ha,GalilScaffoldChainSweep.run] using hl

#print axioms history_terminal_last

theorem history_terminal_canonical {start w v current : GalilScaffoldChainWatch.State}
    {bs : List Bool} {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (center b : Fin 3) (xs extra : List (Fin 3))
    (hw : GalilScaffoldChainWatch.Run start bs w)
    (hr : ChainShiftRun s w cycle n t v finish)
    (hs : start.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra current.machine) :
    GalilScaffoldCounter.Canonical (consume current.machine).control.last := by
  obtain ⟨actual,htrace,_⟩ := GalilScaffoldChainWatchTrace.run_trace hw
  have hc := GalilScaffoldChainRestart.run_canonical
    (GalilScaffoldChainConsume.ready center xs b) actual
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  rw [← hs,← htrace.control] at hc
  have hv := chain_shift_control_canonical hr hc.1 hc.2.1 hc.2.2
  have hcurrent := GalilScaffoldChainRestart.run_canonical v.machine.control extra
    hv.1 hv.2.1 hv.2.2
  rw [← ht.control] at hcurrent
  exact (GalilScaffoldChainRestart.consume_canonical current.machine.control _
    hcurrent.1 hcurrent.2.1 hcurrent.2.2).1

#print axioms history_terminal_canonical

theorem chain_shift_supplied_run {s t : ShiftState}
    {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish) (word : List (Fin 3)) (q : PlaceHead)
    (hreads : Reads w.machine.verifier word q)
    (hs : (GalilScaffoldChainSweep.run w.machine.control word).broken = false) :
    ∃ out, GalilScaffoldChainVerifyRun.Run v.machine word.length out ∧
      out.verifier = q ∧ out.control.broken = false := by
  have hv := (chain_shift_values hr).2.2.2.2.2.1
  have hreads' : Reads v.machine.verifier word q := by simpa only [hv] using hreads
  refine ⟨⟨q,GalilScaffoldChainSweep.run v.machine.control word⟩,?_,rfl,
    chain_shift_future_success hr word hs⟩
  exact GalilScaffoldChainVerifyRun.realize hreads' v.machine.control

#print axioms chain_shift_supplied_run

theorem chain_shift_cycle_canonical {s t : ShiftState}
    {w v : GalilScaffoldChainWatch.State} {cycle finish : GalilScaffoldCounter.Counter}
    {n : ℕ} (hr : ChainShiftRun s w cycle n t v finish)
    (hc : GalilScaffoldCounter.Canonical cycle) : GalilScaffoldCounter.Canonical finish := by
  induction hr with
  | stop s w cycle => exact hc
  | next s w cycle he h1 h2 h3 rest ih =>
    exact ih (GalilScaffoldCounter.inc_canonical _ (GalilScaffoldCounter.inc_canonical _ hc))

/-- beginShift resets cycle before the h shift ticks. At scan resumption
it is positive but not yet the one-cell dispatch condition. -/
theorem chain_shift_reset_cycle {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w GalilScaffoldCounter.reset n t v finish) (hn : 0 < n) :
    GalilScaffoldCounter.value finish = 2*n ∧
    GalilScaffoldCounter.positive finish = true ∧
    GalilScaffoldCounter.singlePositive finish = false := by
  have hc := chain_shift_cycle_canonical hr (Or.inl rfl)
  have hv := (chain_shift_values hr).2.2.2.2.1
  have he : GalilScaffoldCounter.value finish = 2*n := by
    simpa [GalilScaffoldCounter.value,GalilScaffoldCounter.reset] using hv
  refine ⟨he,(GalilScaffoldCounter.positive_iff _ hc).2 (by omega),?_⟩
  cases hf : GalilScaffoldCounter.singlePositive finish with
  | false => rfl
  | true =>
    have hval := (GalilScaffoldCounter.singlePositive_iff _ hc).1 hf
    omega

#print axioms chain_shift_reset_cycle

theorem shift_tick_canonical {s : ShiftState} (h : ShiftCanonical s) :
    ShiftCanonical (shiftTick s) :=
  ⟨GalilScaffoldCounter.dec_canonical _ h.1,
    GalilScaffoldCounter.dec_canonical _ h.2.1,
    GalilScaffoldCounter.dec_canonical _ (GalilScaffoldCounter.dec_canonical _ h.2.2)⟩

theorem shift_run_canonical {s t : ShiftState} {n : ℕ} (hr : ShiftRun s n t)
    (hc : ShiftCanonical s) : ShiftCanonical t := by
  induction hr with
  | stop s => exact hc
  | next s he h1 h2 h3 rest ih => exact ih (shift_tick_canonical hc)

theorem shift_run_values {s t : ShiftState} {n : ℕ} (hr : ShiftRun s n t) :
    GalilScaffoldCounter.value t.remaining = GalilScaffoldCounter.value s.remaining - n ∧
    GalilScaffoldCounter.value t.radius = GalilScaffoldCounter.value s.radius - n ∧
    GalilScaffoldCounter.value t.length = GalilScaffoldCounter.value s.length - 2*n := by
  induction hr with
  | stop s => simp
  | next s he h1 h2 h3 rest ih =>
    simp only [shiftTick,GalilScaffoldCounter.dec_value] at ih
    simp only [Nat.cast_add,Nat.cast_one]
    omega

/-- Completion is independent of a chosen unary representation of the
initial counters: canonical values suffice to justify the exit guard. -/
theorem shift_run_exit {s t : ShiftState} {n : ℕ} (hr : ShiftRun s n t)
    (hc : ShiftCanonical s) (hn : GalilScaffoldCounter.value s.remaining = n) :
    ShiftCanonical t ∧ GalilScaffoldCounter.zero t.remaining = true ∧
      GalilScaffoldCounter.positive t.remaining = false := by
  have ht := shift_run_canonical hr hc
  have hv := (shift_run_values hr).1
  have hz : GalilScaffoldCounter.value t.remaining = 0 := by omega
  have hzero := (GalilScaffoldCounter.zero_iff _ ht.1).2 hz
  refine ⟨ht,hzero,?_⟩
  cases hp : GalilScaffoldCounter.positive t.remaining with
  | false => rfl
  | true =>
    have hpos := (GalilScaffoldCounter.positive_iff _ ht.1).1 hp
    omega

#print axioms shift_run_exit
#print axioms shift_run_values

theorem shift_search_guards {s t : ShiftState} {n : ℕ} (hr : ShiftRun s n t)
    (raw : List (Fin 2)) (hh : GalilScaffoldInputTrace.Represents s.center.head raw)
    (hp : s.center.head.focus ≠ none) (hc : ShiftCanonical s)
    (hn : (n : ℤ) ≤ GalilScaffoldCounter.value s.radius) :
    GalilScaffoldInputHead.read t.center ≠ none ∧
      GalilScaffoldCounter.negative t.radius = false := by
  obtain ⟨_,hfocus,_⟩ := shift_run_center hr raw hh hp
  have hcanon := (shift_run_canonical hr hc).2.1
  have hvalue := (shift_run_values hr).2.1
  constructor
  · cases hf : t.center.head.focus with
    | none => exact False.elim (hfocus hf)
    | some a => simp [GalilScaffoldInputHead.read,hf]
  · cases he : GalilScaffoldCounter.negative t.radius with
    | false => rfl
    | true =>
      have hneg := (GalilScaffoldCounter.negative_iff _ hcanon).1 he
      omega

#print axioms shift_search_guards

theorem shift_heads_counters {c l ce le : PlaceHead} {n : ℕ}
    (hr : ShiftHeads c l n ce le) (r len : GalilScaffoldCounter.Counter) :
    ∃ t, ShiftRun ⟨c,l,GalilScaffoldCounter.ofNat n,r,len⟩ n t ∧
      t.center = ce ∧ t.left = le ∧
      t.remaining = GalilScaffoldCounter.ofNat 0 ∧
      GalilScaffoldCounter.value t.radius = GalilScaffoldCounter.value r - n ∧
      GalilScaffoldCounter.value t.length = GalilScaffoldCounter.value len - 2*n := by
  induction hr generalizing r len with
  | stop c l => exact ⟨_,.stop _,rfl,rfl,rfl,by simp,by simp⟩
  | @next c l n ce le hc hl hl' rest ih =>
    obtain ⟨t,ht,hc',hl'',hz,hr',hlen⟩ := ih (GalilScaffoldCounter.dec r)
      (GalilScaffoldCounter.dec (GalilScaffoldCounter.dec len))
    refine ⟨t,?_,hc',hl'',hz,?_,?_⟩
    · apply ShiftRun.next
      · apply (GalilScaffoldCounter.positive_iff _
          (GalilScaffoldCounter.ofNat_canonical _)).2
        rw [GalilScaffoldCounter.ofNat_value]
        omega
      · exact hc
      · exact hl
      · exact hl'
      · simpa only [shiftTick,GalilScaffoldCounter.dec_ofNat_succ] using ht
    · rw [GalilScaffoldCounter.dec_value] at hr'
      simp only [Nat.cast_add,Nat.cast_one]
      omega
    · simp only [GalilScaffoldCounter.dec_value] at hlen
      simp only [Nat.cast_add,Nat.cast_one]
      omega

#print axioms shift_heads_counters

theorem shift_scan_resume (raw : List (Fin 2)) (centerHead l outer : PlaceHead)
    (radius step : ℕ)
    (hc : GalilScaffoldInputTrace.Represents centerHead.head raw)
    (hcp : centerHead.head.focus ≠ none)
    (hi : ScanInvariant raw (position centerHead) radius l outer)
    (hstep : 0 < step) (hsmall : step ≤ radius) (hcan : canRight outer)
    (hnew : Manacher.PalAt (encoded raw) (position centerHead+step) (radius+1-step)) :
    ∃ centerWord leftWord centerEnd leftEnd,
      Reads centerHead centerWord centerEnd ∧ centerWord.length = step ∧
      Reads (GalilScaffoldInputHead.left l) leftWord leftEnd ∧ leftWord.length = 2*step ∧
      ShiftHeads centerHead (GalilScaffoldInputHead.left l) step centerEnd leftEnd ∧
      GalilScaffoldInputTrace.Represents centerEnd.head raw ∧ centerEnd.head.focus ≠ none ∧
      ScanInvariant raw (position centerEnd) (radius+1-step) leftEnd (right outer) := by
  have hbound := hi.palindrome.2.1
  have hrad := hi.palindrome.1
  have hleft := hi.leftPos
  have hright := hi.rightPos
  obtain ⟨cw,ce,hcr,hcl,hcpos,hcrep,hcpres⟩ :=
    bounded_right_moves centerHead raw hc hcp step (by omega)
  obtain ⟨lw,le,hlr,hll,hlpos,hlrep,hlpres⟩ :=
    shifted_left_moves l raw hi.leftRep hi.leftPresent (2*step-1) (by omega)
  have hrrep := right_word outer raw hi.rightRep hcan
  have hrpres := right_present outer raw hi.rightRep hi.rightPresent hcan
  have hrpos := right_position outer hcan
    (represented_position outer.head raw hi.rightRep hi.rightPresent).1
  have hsync := reads_shift_heads hcr hlr (by omega)
  rw [hcl] at hsync
  refine ⟨cw,lw,ce,le,hcr,hcl,hlr,by omega,hsync,hcrep,hcpres,?_⟩
  refine ⟨hlrep,hrrep,hlpres,hrpres,by omega,by omega,?_⟩
  simpa only [hcpos] using hnew

#print axioms shift_scan_resume

theorem shift_scan_counters (raw : List (Fin 2)) (centerHead l outer : PlaceHead)
    (radius step : ℕ) (r len : GalilScaffoldCounter.Counter)
    (hr : GalilScaffoldCounter.value r = (radius : ℤ)+1)
    (hc : GalilScaffoldInputTrace.Represents centerHead.head raw)
    (hcp : centerHead.head.focus ≠ none)
    (hi : ScanInvariant raw (position centerHead) radius l outer)
    (hstep : 0 < step) (hsmall : step ≤ radius) (hcan : canRight outer)
    (hnew : Manacher.PalAt (encoded raw) (position centerHead+step) (radius+1-step)) :
    ∃ t, ShiftRun ⟨centerHead,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat step,r,len⟩ step t ∧
      GalilScaffoldCounter.zero t.remaining = true ∧
      GalilScaffoldCounter.value t.radius = ((radius+1-step : ℕ) : ℤ) ∧
      GalilScaffoldCounter.value t.length = GalilScaffoldCounter.value len - 2*step ∧
      ScanInvariant raw (position t.center) (radius+1-step) t.left (right outer) := by
  obtain ⟨cw,lw,ce,le,_,_,_,_,hs,_,_,hinv⟩ :=
    shift_scan_resume raw centerHead l outer radius step hc hcp hi hstep hsmall hcan hnew
  obtain ⟨t,ht,hce,hle,hzero,hrad,hlen⟩ := shift_heads_counters hs r len
  refine ⟨t,ht,?_,?_,hlen,?_⟩
  · rw [hzero]
    rfl
  · rw [hrad,hr]
    rw [Nat.cast_sub (by omega : step ≤ radius+1)]
    simp
  · simpa only [hce,hle] using hinv

#print axioms shift_scan_counters
#print axioms shifted_left_moves
#print axioms bounded_right_moves

theorem aligned_prediction_good (s : GalilScaffoldChainWatch.State) (outer : PlaceHead)
    (raw : List (Fin 2))
    (hv : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (ho : GalilScaffoldInputTrace.Represents outer.head raw)
    (hvp : s.machine.verifier.head.focus ≠ none) (hop : outer.head.focus ≠ none)
    (hc : canRight outer) (halign : position s.machine.verifier = position outer)
    (a : Fin 3) (hprediction : GalilScaffoldChainConsume.symbol s.machine.control.period.focus = some a)
    (hread : GalilScaffoldInputHead.read (right outer) = some a) :
    GalilScaffoldChainWatch.Good s := by
  have hor := right_word outer raw ho hc
  have hopr := right_present outer raw ho hop hc
  have hoPos := right_position outer hc (represented_position outer.head raw ho hop).1
  have hb := position_bound (right outer) raw hor hopr
  have hvc : canRight s.machine.verifier := canRight_of_bound _ raw hv hvp (by omega)
  have hvr := right_word s.machine.verifier raw hv hvc
  have hvpr := right_present s.machine.verifier raw hv hvp hvc
  have hvPos := right_position s.machine.verifier hvc
    (represented_position s.machine.verifier.head raw hv hvp).1
  refine ⟨hvc,a,hprediction,?_⟩
  rw [represented_read _ raw hvr hvpr,hvPos,halign,← hoPos,
    ← represented_read _ raw hor hopr]
  exact hread

/-- checkPair's predicted left symbol and the actual outer match justify
the next consume. No independent prediction-validity or Good premise. -/
theorem matched_left_prediction (s : GalilScaffoldChainWatch.State)
    (outer comparedLeft : PlaceHead) (raw : List (Fin 2))
    (hv : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (ho : GalilScaffoldInputTrace.Represents outer.head raw)
    (hvp : s.machine.verifier.head.focus ≠ none) (hop : outer.head.focus ≠ none)
    (hc : canRight outer) (halign : position s.machine.verifier = position outer)
    (hleft : GalilScaffoldInputHead.read comparedLeft =
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus)
    (hmatch : GalilScaffoldInputHead.read comparedLeft =
      GalilScaffoldInputHead.read (right outer)) :
    GalilScaffoldChainWatch.Good s ∧
      GalilScaffoldChainVerifyRun.Run s.machine 1 (consume s.machine) ∧
      (consume s.machine).control.broken = s.machine.control.broken := by
  have hpres := right_present outer raw ho hop hc
  have hsome : ∃ a, GalilScaffoldInputHead.read (right outer) = some a := by
    cases hf : (right outer).head.focus with
    | none => exact False.elim (hpres hf)
    | some a => exact ⟨if (right outer).gap then 2 else GalilScaffoldPlace.letter a,
        by simp [GalilScaffoldInputHead.read,hf]⟩
  obtain ⟨a,ha⟩ := hsome
  have hpred : GalilScaffoldChainConsume.symbol s.machine.control.period.focus = some a :=
    hleft.symm.trans (hmatch.trans ha)
  have hg := aligned_prediction_good s outer raw hv ho hvp hop hc halign a hpred ha
  obtain ⟨hcan,b,hb,hread⟩ := hg
  exact ⟨⟨hcan,b,hb,hread⟩,.next _ hcan (.stop _),(consume_agrees s.machine b hb hread).2⟩

#print axioms matched_left_prediction

/-- Scan and caught verifier describe one input and one right endpoint.
The only-mode cycle countdown is not included here. -/
structure CaughtScan (raw : List (Fin 2)) (center radius : ℕ)
    (l r : PlaceHead) (s : GalilScaffoldChainWatch.State) : Prop where
  scan : ScanInvariant raw center radius l r
  verifierRep : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw
  verifierPresent : s.machine.verifier.head.focus ≠ none
  aligned : position s.machine.verifier = position r
  lagZero : GalilScaffoldCounter.zero s.lag = true
  unbroken : s.machine.control.broken = false

theorem caught_scan_matched {raw : List (Fin 2)} {center radius : ℕ}
    {l r : PlaceHead} {s : GalilScaffoldChainWatch.State}
    (hi : CaughtScan raw center radius l r s) (hc : canRight r)
    (hprediction : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    GalilScaffoldChainWatch.Good s ∧
      CaughtScan raw center (radius+1) (GalilScaffoldInputHead.left l) (right r)
        (GalilScaffoldChainWatch.immediate s) := by
  obtain ⟨hg,_,hb⟩ := matched_left_prediction s r (GalilScaffoldInputHead.left l) raw
    hi.verifierRep hi.scan.rightRep hi.verifierPresent hi.scan.rightPresent hc hi.aligned
    hprediction hmatch
  have hvpos := right_position s.machine.verifier hg.1
    (represented_position s.machine.verifier.head raw hi.verifierRep hi.verifierPresent).1
  have hrpos := right_position r hc
    (represented_position r.head raw hi.scan.rightRep hi.scan.rightPresent).1
  refine ⟨hg,scan_matched hi.scan hc hmatch,
    right_word _ raw hi.verifierRep hg.1,
    right_present _ raw hi.verifierRep hi.verifierPresent hg.1,?_,hi.lagZero,?_⟩
  · change position (right s.machine.verifier) = position (right r)
    rw [hvpos,hrpos,hi.aligned]
  · exact hb.trans hi.unbroken

#print axioms caught_scan_matched

/-- At the last only comparison the left symbol differs from prediction.
An outer match still grows the palindrome, but breaks the chain. -/
theorem caught_scan_terminal_match {raw : List (Fin 2)} {center radius : ℕ}
    {l r : PlaceHead} {s : GalilScaffoldChainWatch.State}
    (hi : CaughtScan raw center radius l r s) (hc : canRight r)
    (hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    ScanInvariant raw center (radius+1) (GalilScaffoldInputHead.left l) (right r) ∧
      GalilScaffoldChainVerifyRun.Run s.machine 1 (consume s.machine) ∧
      (consume s.machine).control.broken = true := by
  have hrrep := right_word r raw hi.scan.rightRep hc
  have hrpres := right_present r raw hi.scan.rightRep hi.scan.rightPresent hc
  have hrpos := right_position r hc
    (represented_position r.head raw hi.scan.rightRep hi.scan.rightPresent).1
  have hbound := position_bound (right r) raw hrrep hrpres
  have hvc := canRight_of_bound s.machine.verifier raw hi.verifierRep hi.verifierPresent
    (by rw [hi.aligned]; omega)
  have hvrep := right_word _ raw hi.verifierRep hvc
  have hvpres := right_present _ raw hi.verifierRep hi.verifierPresent hvc
  have hvpos := right_position s.machine.verifier hvc
    (represented_position s.machine.verifier.head raw hi.verifierRep hi.verifierPresent).1
  have hread : GalilScaffoldInputHead.read (right s.machine.verifier) =
      GalilScaffoldInputHead.read (right r) := by
    rw [represented_read _ raw hvrep hvpres,represented_read _ raw hrrep hrpres,
      hvpos,hrpos,hi.aligned]
  have hbad : GalilScaffoldInputHead.read (right s.machine.verifier) ≠
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus := by
    rw [hread,← hmatch]
    exact hne
  refine ⟨scan_matched hi.scan hc hmatch,.next _ hvc (.stop _),?_⟩
  cases ht : GalilScaffoldChainConsume.symbol s.machine.control.period.focus with
  | none => simp [consume,GalilScaffoldChainConsume.consume,ht]
  | some a =>
    rw [ht] at hbad
    rw [consume_mismatch s.machine a ht hbad]

#print axioms caught_scan_terminal_match

/-- Projection of an only-mode scan interval, before its next comparison.
The mode flag and event scheduling still require controller refinement. -/
structure OnlyScan (raw : List (Fin 2)) (center radius period used : ℕ)
    (l r : PlaceHead) (s : GalilScaffoldChainWatch.State)
    (cycle : GalilScaffoldCounter.Counter) : Prop where
  caught : CaughtScan raw center radius l r s
  canonical : GalilScaffoldCounter.Canonical cycle
  count : GalilScaffoldCounter.value cycle = (period : ℤ)-used
  available : used < period

def OnlyCredit (s : GalilScaffoldChainWatch.State) (cycle : GalilScaffoldCounter.Counter) : Prop :=
  GalilScaffoldCounter.Canonical s.margin ∧
    0 ≤ GalilScaffoldCounter.value s.margin + GalilScaffoldCounter.value cycle

theorem chain_shift_margin_canonical {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish)
    (hc : GalilScaffoldCounter.Canonical w.margin) : GalilScaffoldCounter.Canonical v.margin := by
  induction hr with
  | stop s w cycle => exact hc
  | next s w cycle he h1 h2 h3 rest ih =>
    exact ih (GalilScaffoldCounter.dec_canonical _ hc)

theorem shift_only_credit {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w GalilScaffoldCounter.reset n t v finish)
    (hc : GalilScaffoldCounter.Canonical w.margin)
    (hm : 0 ≤ GalilScaffoldCounter.value w.margin) : OnlyCredit v finish := by
  have hcanon := chain_shift_margin_canonical hr hc
  obtain ⟨_,_,_,hmargin,hcycle,_⟩ := chain_shift_values hr
  have hreset : GalilScaffoldCounter.value GalilScaffoldCounter.reset = 0 := rfl
  rw [hreset] at hcycle
  exact ⟨hcanon,by omega⟩

theorem only_credit_step {s : GalilScaffoldChainWatch.State}
    {cycle : GalilScaffoldCounter.Counter} (h : OnlyCredit s cycle) :
    OnlyCredit (GalilScaffoldChainWatch.immediate s) (GalilScaffoldCounter.dec cycle) := by
  refine ⟨GalilScaffoldCounter.inc_canonical _ h.1,?_⟩
  change 0 ≤ GalilScaffoldCounter.value (GalilScaffoldCounter.inc s.margin) + _
  rw [GalilScaffoldCounter.inc_value,GalilScaffoldCounter.dec_value]
  have := h.2
  omega

theorem only_credit_terminal {s : GalilScaffoldChainWatch.State}
    {cycle : GalilScaffoldCounter.Counter} (h : OnlyCredit s cycle)
    (hc : GalilScaffoldCounter.Canonical cycle)
    (he : GalilScaffoldCounter.singlePositive cycle = true) :
    GalilScaffoldCounter.negative (GalilScaffoldChainWatch.immediate s).margin = false := by
  have hv := (GalilScaffoldCounter.singlePositive_iff cycle hc).1 he
  have hm := h.2
  have hcanon := GalilScaffoldCounter.inc_canonical s.margin h.1
  change GalilScaffoldCounter.negative (GalilScaffoldCounter.inc s.margin) = false
  cases hn : GalilScaffoldCounter.negative (GalilScaffoldCounter.inc s.margin) with
  | false => rfl
  | true =>
    have hneg := (GalilScaffoldCounter.negative_iff _ hcanon).1 hn
    rw [GalilScaffoldCounter.inc_value] at hneg
    omega

#print axioms only_credit_terminal
#print axioms shift_only_credit

/-- Repeated shifts need no fresh nonnegative-margin premise. At cycleEnd
the preceding matched() increment pays the possible remaining unit of debt,
then beginShift resets cycle before the same shift microsteps. -/
theorem reshift_only_credit {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (h : OnlyCredit w cycle) (hc : GalilScaffoldCounter.Canonical cycle)
    (hend : GalilScaffoldCounter.singlePositive cycle = true)
    (hr : ChainShiftRun s (GalilScaffoldChainWatch.immediate w)
      GalilScaffoldCounter.reset n t v finish) : OnlyCredit v finish := by
  have hv := (GalilScaffoldCounter.singlePositive_iff cycle hc).1 hend
  have hm := h.2
  have hnonneg : 0 ≤ GalilScaffoldCounter.value
      (GalilScaffoldChainWatch.immediate w).margin := by
    change 0 ≤ GalilScaffoldCounter.value (GalilScaffoldCounter.inc w.margin)
    rw [GalilScaffoldCounter.inc_value]
    omega
  exact shift_only_credit hr (GalilScaffoldCounter.inc_canonical _ h.1) hnonneg

#print axioms reshift_only_credit

theorem only_scan_dispatch {raw : List (Fin 2)} {center radius period used : ℕ}
    {l r : PlaceHead} {s : GalilScaffoldChainWatch.State} {cycle : GalilScaffoldCounter.Counter}
    (hi : OnlyScan raw center radius period used l r s cycle) :
    GalilScaffoldCounter.positive cycle = true ∧
      (GalilScaffoldCounter.singlePositive cycle = true ↔ used+1 = period) := by
  refine ⟨(GalilScaffoldCounter.positive_iff _ hi.canonical).2 ?_,?_⟩
  · have hv := hi.count
    have ha := hi.available
    omega
  · rw [GalilScaffoldCounter.singlePositive_iff _ hi.canonical,hi.count]
    omega

theorem only_scan_matched {raw : List (Fin 2)} {center radius period used : ℕ}
    {l r : PlaceHead} {s : GalilScaffoldChainWatch.State} {cycle : GalilScaffoldCounter.Counter}
    (hi : OnlyScan raw center radius period used l r s cycle)
    (hremain : used+1 < period) (hc : canRight r)
    (hprediction : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    GalilScaffoldChainWatch.Good s ∧
      OnlyScan raw center (radius+1) period (used+1)
        (GalilScaffoldInputHead.left l) (right r) (GalilScaffoldChainWatch.immediate s)
        (GalilScaffoldCounter.dec cycle) := by
  obtain ⟨hg,ht⟩ := caught_scan_matched hi.caught hc hprediction hmatch
  refine ⟨hg,ht,GalilScaffoldCounter.dec_canonical _ hi.canonical,?_,hremain⟩
  rw [GalilScaffoldCounter.dec_value,hi.count]
  push_cast
  omega

#print axioms only_scan_dispatch
#print axioms only_scan_matched

theorem only_scan_terminal_match {raw : List (Fin 2)} {center radius period used : ℕ}
    {l r : PlaceHead} {s : GalilScaffoldChainWatch.State} {cycle : GalilScaffoldCounter.Counter}
    (hi : OnlyScan raw center radius period used l r s cycle)
    (hcredit : OnlyCredit s cycle)
    (hend : GalilScaffoldCounter.singlePositive cycle = true) (hc : canRight r)
    (hcheck : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus ↔
      GalilScaffoldCounter.singlePositive cycle = false)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    ScanInvariant raw center (radius+1) (GalilScaffoldInputHead.left l) (right r) ∧
      (GalilScaffoldChainWatch.immediate s).machine.control.broken = true ∧
      GalilScaffoldCounter.zero (GalilScaffoldChainWatch.immediate s).lag = true ∧
      GalilScaffoldCounter.zero (GalilScaffoldCounter.dec cycle) = true ∧
      GalilScaffoldCounter.negative (GalilScaffoldChainWatch.immediate s).margin = false ∧
      GalilScaffoldCounter.value (GalilScaffoldChainWatch.immediate s).margin =
        GalilScaffoldCounter.value s.margin+1 := by
  have hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus := by
    intro he
    have := hcheck.mp he
    simp [hend] at this
  obtain ⟨hscan,_,hbroken⟩ := caught_scan_terminal_match hi.caught hc hne hmatch
  have hv := (GalilScaffoldCounter.singlePositive_iff cycle hi.canonical).1 hend
  have hz : GalilScaffoldCounter.zero (GalilScaffoldCounter.dec cycle) = true := by
    apply (GalilScaffoldCounter.zero_iff _
      (GalilScaffoldCounter.dec_canonical _ hi.canonical)).2
    rw [GalilScaffoldCounter.dec_value,hv]
    rfl
  exact ⟨hscan,hbroken,hi.caught.lagZero,hz,only_credit_terminal hcredit hi.canonical hend,
    GalilScaffoldCounter.inc_value _⟩

#print axioms only_scan_terminal_match

theorem only_terminal_restart_conditions {start w v current : GalilScaffoldChainWatch.State}
    {bs : List Bool} {s t : ShiftState} {cycle finish currentCycle : GalilScaffoldCounter.Counter}
    (center b : Fin 3) (xs extra : List (Fin 3))
    (hw : GalilScaffoldChainWatch.Run start bs w)
    (hr : ChainShiftRun s w cycle (xs.length+1) t v finish)
    (hs : start.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (hd : 4*(xs.length+1) ≤ GalilScaffoldCounter.value w.machine.control.distance)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra current.machine)
    {raw : List (Fin 2)} {c radius : ℕ} {l r : PlaceHead}
    (hi : OnlyScan raw c radius (2*(xs.length+1)) extra.length l r current currentCycle)
    (hcredit : OnlyCredit current currentCycle)
    (hend : GalilScaffoldCounter.singlePositive currentCycle = true) (hc : canRight r)
    (hcheck : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldChainConsume.symbol current.machine.control.period.focus ↔
      GalilScaffoldCounter.singlePositive currentCycle = false)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    ScanInvariant raw c (radius+1) (GalilScaffoldInputHead.left l) (right r) ∧
      (GalilScaffoldChainWatch.immediate current).machine.control.broken = true ∧
      GalilScaffoldCounter.negative (GalilScaffoldChainWatch.immediate current).margin = false ∧
      GalilScaffoldCounter.positive
        (GalilScaffoldChainWatch.immediate current).machine.control.last = true ∧
      GalilScaffoldCounter.zero (GalilScaffoldChainWatch.immediate current).lag = true ∧
      ∀ searchRadius, (GalilScaffoldSearchFinish.begin
        (GalilScaffoldChainWatch.immediate current).machine.control.last searchRadius).work =
        (GalilScaffoldChainWatch.immediate current).machine.control.last := by
  obtain ⟨hscan,hbroken,hzero,_,hmargin,_⟩ :=
    only_scan_terminal_match hi hcredit hend hc hcheck hmatch
  have hlast := history_terminal_last center b xs extra hw hr hs hd ht
  refine ⟨hscan,hbroken,hmargin,hlast,hzero,?_⟩
  intro searchRadius
  exact (GalilScaffoldSearchFinish.begin_positive _ searchRadius hlast).2.1

#print axioms only_terminal_restart_conditions

def RadiusRep (counter : GalilScaffoldCounter.Counter) (radius : ℕ) : Prop :=
  GalilScaffoldCounter.Canonical counter ∧ GalilScaffoldCounter.value counter = radius

theorem radius_rep_inc {counter : GalilScaffoldCounter.Counter} {radius : ℕ}
    (h : RadiusRep counter radius) : RadiusRep (GalilScaffoldCounter.inc counter) (radius+1) := by
  refine ⟨GalilScaffoldCounter.inc_canonical _ h.1,?_⟩
  rw [GalilScaffoldCounter.inc_value,h.2]
  simp

theorem shift_radius_rep {s t : ShiftState} {n radius : ℕ} (hr : ShiftRun s n t)
    (hc : ShiftCanonical s) (hv : GalilScaffoldCounter.value s.radius = radius)
    (hn : n ≤ radius) : RadiusRep t.radius (radius-n) := by
  refine ⟨(shift_run_canonical hr hc).2.1,?_⟩
  rw [(shift_run_values hr).2.1,hv,Nat.cast_sub hn]

#print axioms shift_radius_rep

theorem radius_rep_nonnegative {counter : GalilScaffoldCounter.Counter} {radius : ℕ}
    (h : RadiusRep counter radius) : GalilScaffoldCounter.negative counter = false := by
  cases hn : GalilScaffoldCounter.negative counter with
  | false => rfl
  | true =>
    have hv := (GalilScaffoldCounter.negative_iff _ h.1).1 hn
    rw [h.2] at hv
    omega

theorem only_terminal_radius {raw : List (Fin 2)} {center radius period used : ℕ}
    {l r : PlaceHead} {s : GalilScaffoldChainWatch.State}
    {cycle radiusCounter : GalilScaffoldCounter.Counter}
    (hi : OnlyScan raw center radius period used l r s cycle)
    (hcredit : OnlyCredit s cycle) (hrad : RadiusRep radiusCounter radius)
    (hend : GalilScaffoldCounter.singlePositive cycle = true) (hc : canRight r)
    (hcheck : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus ↔
      GalilScaffoldCounter.singlePositive cycle = false)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    ScanInvariant raw center (radius+1) (GalilScaffoldInputHead.left l) (right r) ∧
      (GalilScaffoldChainWatch.immediate s).machine.control.broken = true ∧
      GalilScaffoldCounter.negative (GalilScaffoldChainWatch.immediate s).margin = false ∧
      RadiusRep (GalilScaffoldCounter.inc radiusCounter) (radius+1) ∧
      GalilScaffoldCounter.negative (GalilScaffoldCounter.inc radiusCounter) = false := by
  obtain ⟨hscan,hbroken,_,_,hmargin,_⟩ :=
    only_scan_terminal_match hi hcredit hend hc hcheck hmatch
  have hr := radius_rep_inc hrad
  exact ⟨hscan,hbroken,hmargin,hr,radius_rep_nonnegative hr⟩

#print axioms only_terminal_radius

theorem only_history_matched {raw : List (Fin 2)} {center radius period : ℕ}
    {initialLeft l r : PlaceHead} {base : GalilScaffoldChainVerifier.State}
    {s : GalilScaffoldChainWatch.State} {cycle : GalilScaffoldCounter.Counter}
    (extra : List (Fin 3))
    (hi : OnlyScan raw center radius period extra.length l r s cycle)
    (hcredit : OnlyCredit s cycle)
    (radiusCounter : GalilScaffoldCounter.Counter) (hrad : RadiusRep radiusCounter radius)
    (ht : GalilScaffoldChainWatchTrace.Trace base extra s.machine)
    (hl : LeftMoves initialLeft extra.length l)
    (hc : canRight r) (hcontinue : GalilScaffoldCounter.singlePositive cycle = false)
    (hcheck : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus ↔
      GalilScaffoldCounter.singlePositive cycle = false)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
      GalilScaffoldInputHead.read (right r)) :
    ∃ a, GalilScaffoldChainWatchTrace.Trace base (extra ++ [a])
        (GalilScaffoldChainWatch.immediate s).machine ∧
      LeftMoves initialLeft (extra ++ [a]).length (GalilScaffoldInputHead.left l) ∧
      OnlyScan raw center (radius+1) period (extra ++ [a]).length
        (GalilScaffoldInputHead.left l) (right r) (GalilScaffoldChainWatch.immediate s)
        (GalilScaffoldCounter.dec cycle) ∧
      OnlyCredit (GalilScaffoldChainWatch.immediate s) (GalilScaffoldCounter.dec cycle) ∧
      RadiusRep (GalilScaffoldCounter.inc radiusCounter) (radius+1) := by
  have hprediction := hcheck.mpr hcontinue
  have hd := (only_scan_dispatch hi).2
  have havail := hi.available
  have hremain : extra.length+1 < period := by
    have hn : extra.length+1 ≠ period := by
      intro he
      have := hd.mpr he
      simp [hcontinue] at this
    omega
  obtain ⟨hg,hi'⟩ := only_scan_matched hi hremain hc hprediction hmatch
  obtain ⟨a,ha⟩ := GalilScaffoldChainWatchTrace.one hg
  have hl' := left_moves_append hl (LeftMoves.next l hi.caught.scan.leftPresent (.stop _))
  refine ⟨a,GalilScaffoldChainWatchTrace.append ht ha,?_,?_⟩
  · simpa using hl'
  · exact ⟨by simpa using hi',only_credit_step hcredit,radius_rep_inc hrad⟩

#print axioms only_history_matched

/-- Decoded outer state during a nonterminal only-mode comparison interval. -/
structure OnlyCompareState where
  center : PlaceHead
  left : PlaceHead
  right : PlaceHead
  watch : GalilScaffoldChainWatch.State
  cycle : GalilScaffoldCounter.Counter
  radius : GalilScaffoldCounter.Counter

def onlyCompareNext (s : OnlyCompareState) : OnlyCompareState :=
  ⟨s.center, GalilScaffoldInputHead.left s.left, right s.right,
    GalilScaffoldChainWatch.immediate s.watch, GalilScaffoldCounter.dec s.cycle,
    GalilScaffoldCounter.inc s.radius⟩

/-- Guards are operational premises; their supply by the enclosing controller
is not asserted by this interval relation. -/
inductive OnlyCompareRun : OnlyCompareState → ℕ → OnlyCompareState → Prop
  | stop (s) : OnlyCompareRun s 0 s
  | next (s) {n t}
      (available : canRight s.right)
      (continuing : GalilScaffoldCounter.singlePositive s.cycle = false)
      (checkPair : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
        GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus ↔
        GalilScaffoldCounter.singlePositive s.cycle = false)
      (matched : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
        GalilScaffoldInputHead.read (right s.right))
      (rest : OnlyCompareRun (onlyCompareNext s) n t) : OnlyCompareRun s (n+1) t

theorem only_compare_history {s t : OnlyCompareState} {n : ℕ}
    (run : OnlyCompareRun s n t) {raw : List (Fin 2)} {center radius period : ℕ}
    {initialLeft : PlaceHead} {base : GalilScaffoldChainVerifier.State}
    (extra : List (Fin 3))
    (hi : OnlyScan raw center radius period extra.length s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle) (hrad : RadiusRep s.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace base extra s.watch.machine)
    (hl : LeftMoves initialLeft extra.length s.left) :
    t.center = s.center ∧ ∃ finalExtra,
      finalExtra.length = extra.length+n ∧
      GalilScaffoldChainWatchTrace.Trace base finalExtra t.watch.machine ∧
      LeftMoves initialLeft finalExtra.length t.left ∧
      OnlyScan raw center (radius+n) period finalExtra.length t.left t.right t.watch t.cycle ∧
      OnlyCredit t.watch t.cycle ∧ RadiusRep t.radius (radius+n) := by
  induction run generalizing radius extra with
  | stop s => exact ⟨rfl,extra,by omega,ht,hl,hi,hcredit,hrad⟩
  | next s available continuing checkPair matched rest ih =>
    obtain ⟨a,ht',hl',hi',hcredit',hrad'⟩ :=
      only_history_matched extra hi hcredit s.radius hrad ht hl
        available continuing checkPair matched
    obtain ⟨hcenter,finalExtra,hlen,htrace,hleft,hscan,hcr,hra⟩ :=
      ih (extra ++ [a]) hi' hcredit' hrad' ht' hl'
    refine ⟨hcenter,finalExtra,?_,htrace,hleft,?_,hcr,?_⟩
    · simp only [List.length_append,List.length_singleton] at hlen
      omega
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hscan
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hra

#print axioms only_compare_history

/-- The final matching comparison after an accepted interval supplies the
numeric and head guards for restart, from the same original watch/shift run. -/
theorem only_compare_restart {s t : OnlyCompareState} {n : ℕ}
    (run : OnlyCompareRun s n t)
    {start w v : GalilScaffoldChainWatch.State} {bs : List Bool}
    {shiftStart shiftEnd : ShiftState} {cycle finish : GalilScaffoldCounter.Counter}
    (token b : Fin 3) (xs extra : List (Fin 3))
    (hw : GalilScaffoldChainWatch.Run start bs w)
    (hr : ChainShiftRun shiftStart w cycle (xs.length+1) shiftEnd v finish)
    (hs : start.machine.control = GalilScaffoldChainConsume.ready token xs b)
    (hd : 4*(xs.length+1) ≤ GalilScaffoldCounter.value w.machine.control.distance)
    {raw : List (Fin 2)} {center radius : ℕ} {initialLeft : PlaceHead}
    (hi : OnlyScan raw center radius (2*(xs.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle) (hrad : RadiusRep s.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra s.watch.machine)
    (hl : LeftMoves initialLeft extra.length s.left)
    (hcenter : GalilScaffoldInputHead.read s.center ≠ none)
    (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
    (hcheck : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left) =
      GalilScaffoldChainConsume.symbol t.watch.machine.control.period.focus ↔
      GalilScaffoldCounter.singlePositive t.cycle = false)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left) =
      GalilScaffoldInputHead.read (right t.right)) :
    let endState := onlyCompareNext t
    ScanInvariant raw center (radius+n+1) endState.left endState.right ∧
      endState.watch.machine.control.broken = true ∧
      GalilScaffoldCounter.negative endState.watch.margin = false ∧
      GalilScaffoldCounter.positive endState.watch.machine.control.last = true ∧
      GalilScaffoldCounter.zero endState.watch.lag = true ∧
      GalilScaffoldInputHead.read endState.center ≠ none ∧
      RadiusRep endState.radius (radius+n+1) ∧
      GalilScaffoldCounter.negative endState.radius = false ∧
      (GalilScaffoldSearchFinish.begin endState.watch.machine.control.last
        endState.radius).work = endState.watch.machine.control.last ∧
      GalilScaffoldCounter.Canonical endState.watch.machine.control.last := by
  obtain ⟨heq,actual,_,htrace,_,hscan,hcr,hra⟩ :=
    only_compare_history run extra hi hcredit hrad ht hl
  obtain ⟨hscan',hbroken,hmargin,hrad',hnonneg⟩ :=
    only_terminal_radius hscan hcr hra hend hc hcheck hmatch
  have hlast := history_terminal_last token b xs actual hw hr hs hd htrace
  have hz := hscan.caught.lagZero
  have hread : GalilScaffoldInputHead.read t.center ≠ none := by
    rw [heq]
    exact hcenter
  exact ⟨hscan',hbroken,hmargin,hlast,hz,hread,hrad',hnonneg,
    (GalilScaffoldSearchFinish.begin_positive _ _ hlast).2.1,
    history_terminal_canonical token b xs actual hw hr hs htrace⟩

#print axioms only_compare_restart

theorem only_history_check_pair {start w v current : GalilScaffoldChainWatch.State}
    {bs : List Bool} {s t : ShiftState} {cycle finish currentCycle : GalilScaffoldCounter.Counter}
    {n : ℕ} (hw : GalilScaffoldChainWatch.Run start bs w)
    (hr : ChainShiftRun s w cycle n t v finish)
    (raw : List (Fin 2)) (c radius currentCenter currentRadius : ℕ)
    (l r resumeLeft currentLeft currentRight : PlaceHead)
    (hi : ScanInvariant raw c radius l r) (hcan : canRight r)
    (hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right r))
    (hh : GalilScaffoldInputTrace.Represents start.machine.verifier.head raw)
    (hp : start.machine.verifier.head.focus ≠ none)
    (center b : Fin 3) (xs extra : List (Fin 3))
    (hstart : start.machine.control = GalilScaffoldChainConsume.ready center xs b)
    (hstartPos : position start.machine.verifier = c)
    (hend : position w.machine.verifier = c+radius+1) (hsize : 2*(xs.length+1) ≤ radius)
    (hresume : ScanInvariant raw (c+(xs.length+1)) (radius+1-(xs.length+1))
      resumeLeft (right r))
    (hcurrent : OnlyScan raw currentCenter currentRadius (2*(xs.length+1)) extra.length
      currentLeft currentRight current currentCycle)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra current.machine)
    (hl : LeftMoves resumeLeft extra.length currentLeft) :
    GalilScaffoldCounter.positive currentCycle = true ∧
      (GalilScaffoldInputHead.read (GalilScaffoldInputHead.left currentLeft) =
        GalilScaffoldChainConsume.symbol current.machine.control.period.focus ↔
        GalilScaffoldCounter.singlePositive currentCycle = false) := by
  have hsuccess : (GalilScaffoldChainSweep.run v.machine.control extra).broken = false := by
    rw [← ht.control]
    exact hcurrent.caught.unbroken
  have hmoves := left_moves_append hl
    (LeftMoves.next currentLeft hcurrent.caught.scan.leftPresent (.stop _))
  have hpair := shifted_check_pair hw hr raw c radius l r resumeLeft
    (GalilScaffoldInputHead.left currentLeft) hi hcan hne hh hp center b xs extra
    hstart hstartPos hend hsize hcurrent.available hsuccess hresume hmoves
  rw [← ht.control] at hpair
  obtain ⟨hpositive,hdispatch⟩ := only_scan_dispatch hcurrent
  refine ⟨hpositive,hpair.trans ?_⟩
  have havail := hcurrent.available
  cases hc : GalilScaffoldCounter.singlePositive currentCycle with
  | false =>
    have hn : extra.length+1 ≠ 2*(xs.length+1) := by
      intro he
      have := hdispatch.mpr he
      simp [hc] at this
    simp only [Bool.false_eq_true,iff_true]
    omega
  | true =>
    have he := hdispatch.mp hc
    simp only [Bool.true_eq_false,iff_false]
    omega

#print axioms only_history_check_pair

/-- A fixed successful shift origin. These are entry conditions, not per-step
assertions about the comparisons which follow. -/
structure OnlyOrigin (raw : List (Fin 2)) where
  start : GalilScaffoldChainWatch.State
  watched : GalilScaffoldChainWatch.State
  shifted : GalilScaffoldChainWatch.State
  ticks : List Bool
  shiftStart : ShiftState
  shiftEnd : ShiftState
  cycle : GalilScaffoldCounter.Counter
  finish : GalilScaffoldCounter.Counter
  steps : ℕ
  center : ℕ
  radius : ℕ
  left : PlaceHead
  rightHead : PlaceHead
  resumeLeft : PlaceHead
  token : Fin 3
  boundary : Fin 3
  interior : List (Fin 3)
  watchRun : GalilScaffoldChainWatch.Run start ticks watched
  shiftRun : ChainShiftRun shiftStart watched cycle steps shiftEnd shifted finish
  scan : ScanInvariant raw center radius left rightHead
  available : canRight rightHead
  mismatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left left) ≠
    GalilScaffoldInputHead.read (right rightHead)
  represents : GalilScaffoldInputTrace.Represents start.machine.verifier.head raw
  present : start.machine.verifier.head.focus ≠ none
  ready : start.machine.control = GalilScaffoldChainConsume.ready token interior boundary
  startPosition : position start.machine.verifier = center
  endPosition : position watched.machine.verifier = center+radius+1
  size : 2*(interior.length+1) ≤ radius
  resumed : ScanInvariant raw (center+(interior.length+1))
    (radius+1-(interior.length+1)) resumeLeft (right rightHead)

theorem OnlyOrigin.check_pair {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {c radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw c radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus ↔
      GalilScaffoldCounter.singlePositive s.cycle = false := by
  exact (only_history_check_pair o.watchRun o.shiftRun raw o.center o.radius c radius
    o.left o.rightHead o.resumeLeft s.left s.right o.scan o.available o.mismatch
    o.represents o.present o.token o.boundary o.interior extra o.ready
    o.startPosition o.endPosition o.size o.resumed hi ht hl).2

/-- Rejoin the actual verifier reads across a shift, while interpreting the
prediction at its original ready origin. Shifted distance counters need not
equal the original counters, only period/direction and failure status do. -/
theorem OnlyOrigin.joined_reads {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {current : GalilScaffoldChainVerifier.State} (extra : List (Fin 3))
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra current)
    (hb : current.control.broken = false) :
    ∃ pre, Reads o.start.machine.verifier (pre ++ extra) current.verifier ∧
      (GalilScaffoldChainSweep.run
        (GalilScaffoldChainConsume.ready o.token o.interior o.boundary)
        (pre ++ extra)).broken = false := by
  obtain ⟨pre,hpre,_⟩ := GalilScaffoldChainWatchTrace.run_trace o.watchRun
  have hver := (chain_shift_values o.shiftRun).2.2.2.2.2.1
  have hreads : Reads o.watched.machine.verifier extra current.verifier := by
    simpa only [hver] using ht.reads
  have hs : (GalilScaffoldChainSweep.run o.shifted.machine.control extra).broken = false := by
    rw [← ht.control]
    exact hb
  rw [GalilScaffoldChainPrediction.run_same_broken
    (chain_shift_prediction o.shiftRun) (chain_shift_broken o.shiftRun) extra] at hs
  refine ⟨pre,GalilScaffoldChainVerifyRun.reads_append hpre.reads hreads,?_⟩
  rw [GalilScaffoldChainSweep.run_append,← o.ready,← hpre.control]
  exact hs

#print axioms OnlyOrigin.joined_reads

theorem OnlyOrigin.joined_input_period {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {current : GalilScaffoldChainVerifier.State} (extra : List (Fin 3))
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra current)
    (hb : current.control.broken = false) :
    ∀ j, o.center < j → j+2*(o.interior.length+1) ≤ position current.verifier →
      (encoded raw)[j]? = (encoded raw)[j+2*(o.interior.length+1)]? := by
  obtain ⟨pre,hreads,hsuccess⟩ := o.joined_reads extra ht hb
  have he := GalilScaffoldChainPrediction.successful_cycles
    o.token o.boundary o.interior (pre ++ extra) hsuccess
  have hp := hasPeriod_take (k := (pre ++ extra).length)
    (GalilScaffoldChainPrediction.cycles_period
      (GalilScaffoldChainSweep.bounce o.token o.boundary o.interior) (pre ++ extra).length)
  rw [he] at hp
  have hlen : (GalilScaffoldChainSweep.bounce o.token o.boundary o.interior).length =
      2*(o.interior.length+1) := by simp [GalilScaffoldChainSweep.bounce]; omega
  rw [hlen] at hp
  have hpos := reads_position hreads raw o.represents o.present
  rw [o.startPosition] at hpos
  intro j hj hbound
  let i := j-o.center-1
  have hi : i+2*(o.interior.length+1) < (pre ++ extra).length := by dsimp [i]; omega
  have hperiod := hp i hi
  rw [reads_index hreads raw o.represents o.present i (by omega),
    reads_index hreads raw o.represents o.present (i+2*(o.interior.length+1)) hi,
    o.startPosition] at hperiod
  have h1 : o.center+(i+1) = j := by dsimp [i]; omega
  have h2 : o.center+(i+2*(o.interior.length+1)+1) = j+2*(o.interior.length+1) := by
    dsimp [i]; omega
  simpa only [h1,h2] using hperiod

#print axioms OnlyOrigin.joined_input_period

theorem OnlyOrigin.reshift_compare {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {center radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hprediction : GalilScaffoldInputHead.read (right s.right) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) ≠
      GalilScaffoldInputHead.read (right s.right) ∧
    GalilScaffoldChainWatch.Good s.watch ∧
    GalilScaffoldChainVerifyRun.Run s.watch.machine 1 (consume s.watch.machine) ∧
    (consume s.watch.machine).control.broken = false ∧
    ∃ a, (extra ++ [a]).length = 2*(o.interior.length+1) ∧
      GalilScaffoldChainWatchTrace.Trace o.shifted.machine (extra ++ [a])
        (consume s.watch.machine) ∧
      LeftMoves o.resumeLeft (extra ++ [a]).length
        (GalilScaffoldInputHead.left s.left) := by
  have hcheck := o.check_pair extra hi ht hl
  have hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) ≠
      GalilScaffoldInputHead.read (right s.right) := by
    intro he
    have hf := hcheck.mp (he.trans hprediction)
    simp [hend] at hf
  obtain ⟨hg,hr,hb⟩ := matched_left_prediction s.watch s.right (right s.right) raw
    hi.caught.verifierRep hi.caught.scan.rightRep hi.caught.verifierPresent
    hi.caught.scan.rightPresent hc hi.caught.aligned hprediction rfl
  obtain ⟨a,ha⟩ := GalilScaffoldChainWatchTrace.one hg
  have hlength := (only_scan_dispatch hi).2.mp hend
  have hleft := left_moves_append hl
    (LeftMoves.next s.left hi.caught.scan.leftPresent (.stop _))
  refine ⟨hne,hg,hr,hb.trans hi.caught.unbroken,a,?_,
    GalilScaffoldChainWatchTrace.append ht ha,?_⟩
  · simpa only [List.length_append,List.length_singleton] using hlength
  · simpa only [List.length_append,List.length_singleton] using hleft

#print axioms OnlyOrigin.reshift_compare

theorem OnlyOrigin.reshift_palindrome {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw (o.center+(o.interior.length+1)) (o.radius+(o.interior.length+1))
      (2*(o.interior.length+1)) extra.length s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hprediction : GalilScaffoldInputHead.read (right s.right) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus) :
    Manacher.PalAt (encoded raw) (o.center+2*(o.interior.length+1)) (o.radius+1) := by
  obtain ⟨_,hg,_,hb,a,_,htrace,_⟩ := o.reshift_compare extra hi ht hl hend hc hprediction
  have hperiod := o.joined_input_period (extra ++ [a]) htrace hb
  have hvpos := right_position s.watch.machine.verifier hg.1
    (represented_position _ raw hi.caught.verifierRep hi.caught.verifierPresent).1
  have hrpos := right_position s.right hc
    (represented_position _ raw hi.caught.scan.rightRep hi.caught.scan.rightPresent).1
  have hpos : position (consume s.watch.machine).verifier =
      o.center+(o.interior.length+1)+(o.radius+(o.interior.length+1))+1 := by
    change position (right s.watch.machine.verifier) = _
    rw [hvpos,hi.caught.aligned,hi.caught.scan.rightPos]
  have hbound := position_bound (right s.right) raw
    (right_word s.right raw hi.caught.scan.rightRep hc)
    (right_present s.right raw hi.caught.scan.rightRep hi.caught.scan.rightPresent hc)
  rw [hrpos,hi.caught.scan.rightPos] at hbound
  apply reshift_from_right (encoded raw) o.center o.radius (o.interior.length+1)
    ⟨by have := o.scan.palindrome.1; have := o.size; omega,
      by have := o.scan.palindrome.2.1; have := o.size; omega,
      fun i hi => o.scan.palindrome.2.2 i (by have := o.size; omega)⟩
      hi.caught.scan.palindrome (by omega) (by have := o.size; omega) hbound
  intro j hj hj'
  apply hperiod j (by omega)
  rw [hpos]
  exact hj'

#print axioms OnlyOrigin.reshift_palindrome

/-- Observed matching comparisons, without assuming checkPair succeeds. -/
inductive OnlyMatchedRun : OnlyCompareState → ℕ → OnlyCompareState → Prop
  | stop (s) : OnlyMatchedRun s 0 s
  | next (s) {n t} (available : canRight s.right)
      (continuing : GalilScaffoldCounter.singlePositive s.cycle = false)
      (matched : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
        GalilScaffoldInputHead.read (right s.right))
      (rest : OnlyMatchedRun (onlyCompareNext s) n t) : OnlyMatchedRun s (n+1) t

theorem only_matched_checked {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {s t : OnlyCompareState} {n : ℕ} (run : OnlyMatchedRun s n t)
    {center radius : ℕ} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle) (hrad : RadiusRep s.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left) : OnlyCompareRun s n t := by
  induction run generalizing radius extra with
  | stop s => exact .stop s
  | next s available continuing matched rest ih =>
    have hcheck := o.check_pair extra hi ht hl
    obtain ⟨a,ht',hl',hi',hcredit',hrad'⟩ :=
      only_history_matched extra hi hcredit s.radius hrad ht hl
        available continuing hcheck matched
    exact .next s available continuing hcheck matched
      (ih (extra ++ [a]) hi' hcredit' hrad' ht' hl')

#print axioms only_matched_checked

theorem OnlyOrigin.reshift_after_matches {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {s t : OnlyCompareState} {n : ℕ} (run : OnlyMatchedRun s n t)
    (hi : OnlyScan raw (o.center+(o.interior.length+1))
      (o.radius+1-(o.interior.length+1)) (2*(o.interior.length+1)) 0
      s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle)
    (hrad : RadiusRep s.radius (o.radius+1-(o.interior.length+1)))
    (hmachine : s.watch.machine = o.shifted.machine) (hleft : s.left = o.resumeLeft)
    (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
    (hprediction : GalilScaffoldInputHead.read (right t.right) =
      GalilScaffoldChainConsume.symbol t.watch.machine.control.period.focus) :
    n+1 = 2*(o.interior.length+1) ∧
      RadiusRep t.radius (o.radius+(o.interior.length+1)) ∧
      OnlyCredit t.watch t.cycle ∧
      Manacher.PalAt (encoded raw) (o.center+2*(o.interior.length+1)) (o.radius+1) := by
  have ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine [] s.watch.machine := by
    rw [hmachine]
    exact GalilScaffoldChainWatchTrace.empty _
  have hl : LeftMoves o.resumeLeft 0 s.left := by rw [hleft]; exact .stop _
  have checked := only_matched_checked o run [] hi hcredit hrad ht hl
  obtain ⟨_,actual,hlen,htrace,hleft',hscan,hcredit',hrad'⟩ :=
    only_compare_history checked [] hi hcredit hrad ht hl
  have hcount := (only_scan_dispatch hscan).2.mp hend
  have hn : n+1 = 2*(o.interior.length+1) := by simp only [List.length_nil] at hlen; omega
  have hr : o.radius+1-(o.interior.length+1)+n = o.radius+(o.interior.length+1) := by
    have := o.size
    omega
  rw [hr] at hscan hrad'
  exact ⟨hn,hrad',hcredit',o.reshift_palindrome actual hscan htrace hleft' hend hc hprediction⟩

#print axioms OnlyOrigin.reshift_after_matches

theorem only_matched_restart {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {s t : OnlyCompareState} {n : ℕ} (run : OnlyMatchedRun s n t)
    (hsteps : o.steps = o.interior.length+1)
    (hd : 4*(o.interior.length+1) ≤
      GalilScaffoldCounter.value o.watched.machine.control.distance)
    {center radius : ℕ} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle) (hrad : RadiusRep s.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hcenter : GalilScaffoldInputHead.read s.center ≠ none)
    (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left) =
      GalilScaffoldInputHead.read (right t.right)) :
    let endState := onlyCompareNext t
    ScanInvariant raw center (radius+n+1) endState.left endState.right ∧
      endState.watch.machine.control.broken = true ∧
      GalilScaffoldCounter.negative endState.watch.margin = false ∧
      GalilScaffoldCounter.positive endState.watch.machine.control.last = true ∧
      GalilScaffoldCounter.zero endState.watch.lag = true ∧
      GalilScaffoldInputHead.read endState.center ≠ none ∧
      RadiusRep endState.radius (radius+n+1) ∧
      GalilScaffoldCounter.negative endState.radius = false ∧
      (GalilScaffoldSearchFinish.begin endState.watch.machine.control.last
        endState.radius).work = endState.watch.machine.control.last ∧
      GalilScaffoldCounter.Canonical endState.watch.machine.control.last := by
  have checked := only_matched_checked o run extra hi hcredit hrad ht hl
  obtain ⟨_,actual,_,htrace,hleft,hscan,_,_⟩ :=
    only_compare_history checked extra hi hcredit hrad ht hl
  have hcheck := o.check_pair actual hscan htrace hleft
  have hshift : ChainShiftRun o.shiftStart o.watched o.cycle
      (o.interior.length+1) o.shiftEnd o.shifted o.finish := by
    simpa only [hsteps] using o.shiftRun
  exact only_compare_restart checked o.token o.boundary o.interior extra
    o.watchRun hshift o.ready hd hi hcredit hrad ht hl hcenter hend hc hcheck hmatch

#print axioms only_matched_restart

theorem shift_caught_scan {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish)
    (raw : List (Fin 2)) (center radius : ℕ) (l r : PlaceHead)
    (hi : ScanInvariant raw center radius l r)
    (hv : GalilScaffoldInputTrace.Represents w.machine.verifier.head raw)
    (hp : w.machine.verifier.head.focus ≠ none)
    (halign : position w.machine.verifier = position r)
    (hzero : GalilScaffoldCounter.zero w.lag = true)
    (hb : w.machine.control.broken = false) : CaughtScan raw center radius l r v := by
  obtain ⟨_,_,_,_,_,hver,_,hlag⟩ := chain_shift_values hr
  refine ⟨hi,?_,?_,?_,?_,(chain_shift_broken hr).trans hb⟩
  · simpa only [hver] using hv
  · simpa only [hver] using hp
  · simpa only [hver] using halign
  · simpa only [hlag] using hzero

#print axioms shift_caught_scan

/-- The same shift endpoint supplies the initial only-mode interval.
Its cycle is the one reset by beginShift and updated on these n ticks. -/
theorem shift_only_scan {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w GalilScaffoldCounter.reset n t v finish) (hn : 0 < n)
    (raw : List (Fin 2)) (radius : ℕ) (r : PlaceHead)
    (hi : ScanInvariant raw (position t.center) radius t.left r)
    (hv : GalilScaffoldInputTrace.Represents w.machine.verifier.head raw)
    (hp : w.machine.verifier.head.focus ≠ none)
    (halign : position w.machine.verifier = position r)
    (hzero : GalilScaffoldCounter.zero w.lag = true)
    (hb : w.machine.control.broken = false) :
    OnlyScan raw (position t.center) radius (2*n) 0 t.left r v finish := by
  have hcaught := shift_caught_scan hr raw (position t.center) radius t.left r hi hv hp
    halign hzero hb
  have hcycle := chain_shift_reset_cycle hr hn
  refine ⟨hcaught,chain_shift_cycle_canonical hr (Or.inl rfl),?_,by omega⟩
  simpa using hcycle.1

#print axioms shift_only_scan

/-- All comparison-history invariants start at the same physical-head and
counter endpoint of a fresh shift. -/
theorem shift_only_entry {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {finish : GalilScaffoldCounter.Counter} {n radius : ℕ}
    (run : ShiftRun s n t)
    (chain : ChainShiftRun s w GalilScaffoldCounter.reset n t v finish)
    (hn : 0 < n) (hsmall : n ≤ radius)
    (hcanon : ShiftCanonical s) (hrad : GalilScaffoldCounter.value s.radius = radius)
    (raw : List (Fin 2)) (r : PlaceHead)
    (hcenter : GalilScaffoldInputTrace.Represents s.center.head raw)
    (hcenterPresent : s.center.head.focus ≠ none)
    (hi : ScanInvariant raw (position t.center) (radius-n) t.left r)
    (hv : GalilScaffoldInputTrace.Represents w.machine.verifier.head raw)
    (hp : w.machine.verifier.head.focus ≠ none)
    (halign : position w.machine.verifier = position r)
    (hzero : GalilScaffoldCounter.zero w.lag = true)
    (hb : w.machine.control.broken = false)
    (hmargin : GalilScaffoldCounter.Canonical w.margin)
    (hmarginValue : 0 ≤ GalilScaffoldCounter.value w.margin) :
    let entry : OnlyCompareState := ⟨t.center,t.left,r,v,finish,t.radius⟩
    OnlyScan raw (position entry.center) (radius-n) (2*n) 0
      entry.left entry.right entry.watch entry.cycle ∧
      OnlyCredit entry.watch entry.cycle ∧ RadiusRep entry.radius (radius-n) ∧
      GalilScaffoldChainWatchTrace.Trace v.machine [] entry.watch.machine ∧
      LeftMoves t.left 0 entry.left ∧
      GalilScaffoldInputHead.read entry.center ≠ none := by
  have hbound : (n : ℤ) ≤ GalilScaffoldCounter.value s.radius := by
    rw [hrad]
    exact_mod_cast hsmall
  exact ⟨shift_only_scan chain hn raw (radius-n) r hi hv hp halign hzero hb,
    shift_only_credit chain hmargin hmarginValue,
    shift_radius_rep run hcanon hrad hsmall,
    GalilScaffoldChainWatchTrace.empty _,.stop _,
    (shift_search_guards run raw hcenter hcenterPresent hcanon hbound).1⟩

#print axioms shift_only_entry

theorem shift_to_only (raw : List (Fin 2)) (centerHead l outer : PlaceHead)
    (radius step : ℕ) (r len : GalilScaffoldCounter.Counter)
    (w : GalilScaffoldChainWatch.State)
    (hrad : GalilScaffoldCounter.value r = (radius : ℤ)+1)
    (hc : GalilScaffoldInputTrace.Represents centerHead.head raw)
    (hcp : centerHead.head.focus ≠ none)
    (hi : ScanInvariant raw (position centerHead) radius l outer)
    (hstep : 0 < step) (hsmall : step ≤ radius) (hcan : canRight outer)
    (hnew : Manacher.PalAt (encoded raw) (position centerHead+step) (radius+1-step))
    (hv : GalilScaffoldInputTrace.Represents w.machine.verifier.head raw)
    (hp : w.machine.verifier.head.focus ≠ none)
    (halign : position w.machine.verifier = position (right outer))
    (hzero : GalilScaffoldCounter.zero w.lag = true)
    (hb : w.machine.control.broken = false) :
    ∃ t v finish,
      ShiftRun ⟨centerHead,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat step,r,len⟩ step t ∧
      ChainShiftRun ⟨centerHead,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat step,r,len⟩ w GalilScaffoldCounter.reset step t v finish ∧
      GalilScaffoldCounter.zero t.remaining = true ∧
      GalilScaffoldCounter.value t.radius = ((radius+1-step : ℕ) : ℤ) ∧
      GalilScaffoldCounter.value t.length = GalilScaffoldCounter.value len-2*step ∧
      OnlyScan raw (position t.center) (radius+1-step) (2*step) 0
        t.left (right outer) v finish := by
  obtain ⟨t,ht,hz,hr,hl,hinv⟩ := shift_scan_counters raw centerHead l outer radius step r len
    hrad hc hcp hi hstep hsmall hcan hnew
  obtain ⟨v,finish,hchain⟩ := shift_run_chain ht w GalilScaffoldCounter.reset
  exact ⟨t,v,finish,ht,hchain,hz,hr,hl,
    shift_only_scan hchain hstep raw (radius+1-step) (right outer) hinv hv hp halign hzero hb⟩

#print axioms shift_to_only

theorem shift_to_only_initialized (raw : List (Fin 2)) (centerHead l outer : PlaceHead)
    (radius step : ℕ) (r len : GalilScaffoldCounter.Counter)
    (w : GalilScaffoldChainWatch.State)
    (hrad : GalilScaffoldCounter.value r = (radius : ℤ)+1)
    (hrcanon : GalilScaffoldCounter.Canonical r)
    (hlcanon : GalilScaffoldCounter.Canonical len)
    (hmargin : GalilScaffoldCounter.Canonical w.margin)
    (hmarginValue : 0 ≤ GalilScaffoldCounter.value w.margin)
    (hc : GalilScaffoldInputTrace.Represents centerHead.head raw)
    (hcp : centerHead.head.focus ≠ none)
    (hi : ScanInvariant raw (position centerHead) radius l outer)
    (hstep : 0 < step) (hsmall : step ≤ radius) (hcan : canRight outer)
    (hnew : Manacher.PalAt (encoded raw) (position centerHead+step) (radius+1-step))
    (hv : GalilScaffoldInputTrace.Represents w.machine.verifier.head raw)
    (hp : w.machine.verifier.head.focus ≠ none)
    (halign : position w.machine.verifier = position (right outer))
    (hzero : GalilScaffoldCounter.zero w.lag = true)
    (hb : w.machine.control.broken = false) :
    ∃ t v finish,
      ShiftRun ⟨centerHead,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat step,r,len⟩ step t ∧
      ChainShiftRun ⟨centerHead,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat step,r,len⟩ w GalilScaffoldCounter.reset step t v finish ∧
      GalilScaffoldCounter.zero t.remaining = true ∧
      (let entry : OnlyCompareState := ⟨t.center,t.left,right outer,v,finish,t.radius⟩
       OnlyScan raw (position entry.center) (radius+1-step) (2*step) 0
         entry.left entry.right entry.watch entry.cycle ∧
       OnlyCredit entry.watch entry.cycle ∧ RadiusRep entry.radius (radius+1-step) ∧
       GalilScaffoldChainWatchTrace.Trace v.machine [] entry.watch.machine ∧
       LeftMoves t.left 0 entry.left ∧
       GalilScaffoldInputHead.read entry.center ≠ none) := by
  obtain ⟨t,v,finish,run,chain,hz,_,_,hscan⟩ :=
    shift_to_only raw centerHead l outer radius step r len w hrad hc hcp hi
      hstep hsmall hcan hnew hv hp halign hzero hb
  have hcanon : ShiftCanonical
      ⟨centerHead,GalilScaffoldInputHead.left l,GalilScaffoldCounter.ofNat step,r,len⟩ :=
    ⟨GalilScaffoldCounter.ofNat_canonical step,hrcanon,hlcanon⟩
  have hv' : GalilScaffoldCounter.value r = ((radius+1 : ℕ) : ℤ) := by
    simpa using hrad
  exact ⟨t,v,finish,run,chain,hz,
    shift_only_entry run chain hstep (by omega) hcanon hv' raw (right outer)
      hc hcp hscan.caught.scan hv hp halign hzero hb hmargin hmarginValue⟩

#print axioms shift_to_only_initialized

theorem OnlyOrigin.reshift_initialized {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw (o.center+(o.interior.length+1)) (o.radius+(o.interior.length+1))
      (2*(o.interior.length+1)) extra.length s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hprediction : GalilScaffoldInputHead.read (right s.right) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus)
    (hcredit : OnlyCredit s.watch s.cycle)
    (hrad : RadiusRep s.radius (o.radius+(o.interior.length+1)))
    (hcenter : GalilScaffoldInputTrace.Represents s.center.head raw)
    (hpcenter : s.center.head.focus ≠ none)
    (hpos : position s.center = o.center+(o.interior.length+1))
    (lengthCounter : GalilScaffoldCounter.Counter)
    (hlen : GalilScaffoldCounter.Canonical lengthCounter) :
    ∃ t v cycle,
      ShiftRun ⟨s.center,GalilScaffoldInputHead.left s.left,
        GalilScaffoldCounter.ofNat (o.interior.length+1),
        GalilScaffoldCounter.inc s.radius,lengthCounter⟩ (o.interior.length+1) t ∧
      ChainShiftRun ⟨s.center,GalilScaffoldInputHead.left s.left,
        GalilScaffoldCounter.ofNat (o.interior.length+1),
        GalilScaffoldCounter.inc s.radius,lengthCounter⟩
        (GalilScaffoldChainWatch.immediate s.watch) GalilScaffoldCounter.reset
        (o.interior.length+1) t v cycle ∧
      OnlyScan raw (position t.center) (o.radius+1) (2*(o.interior.length+1)) 0
        t.left (right s.right) v cycle ∧ OnlyCredit v cycle ∧ RadiusRep t.radius (o.radius+1) := by
  have hpal := o.reshift_palindrome extra hi ht hl hend hc hprediction
  obtain ⟨_,hg,_,hb,_⟩ := o.reshift_compare extra hi ht hl hend hc hprediction
  have hv := right_word s.watch.machine.verifier raw hi.caught.verifierRep hg.1
  have hp := right_present s.watch.machine.verifier raw hi.caught.verifierRep
    hi.caught.verifierPresent hg.1
  have hvpos := right_position s.watch.machine.verifier hg.1
    (represented_position _ raw hi.caught.verifierRep hi.caught.verifierPresent).1
  have hrpos := right_position s.right hc
    (represented_position _ raw hi.caught.scan.rightRep hi.caught.scan.rightPresent).1
  have halign : position (consume s.watch.machine).verifier = position (right s.right) := by
    change position (right s.watch.machine.verifier) = _
    rw [hvpos,hrpos,hi.caught.aligned]
  have hcounter : GalilScaffoldCounter.value (GalilScaffoldCounter.inc s.radius) =
      ((o.radius+(o.interior.length+1) : ℕ) : ℤ)+1 := by
    rw [GalilScaffoldCounter.inc_value,hrad.2]
  have hcycle := (GalilScaffoldCounter.singlePositive_iff s.cycle hi.canonical).1 hend
  have hm : 0 ≤ GalilScaffoldCounter.value (GalilScaffoldChainWatch.immediate s.watch).margin := by
    change 0 ≤ GalilScaffoldCounter.value (GalilScaffoldCounter.inc s.watch.margin)
    rw [GalilScaffoldCounter.inc_value]
    have := hcredit.2
    omega
  have hscan : ScanInvariant raw (position s.center) (o.radius+(o.interior.length+1))
      s.left s.right := by simpa only [hpos] using hi.caught.scan
  have hnew : Manacher.PalAt (encoded raw) (position s.center+(o.interior.length+1))
      (o.radius+(o.interior.length+1)+1-(o.interior.length+1)) := by
    have he : o.radius+(o.interior.length+1)+1-(o.interior.length+1) = o.radius+1 := by omega
    have hc : position s.center+(o.interior.length+1) = o.center+2*(o.interior.length+1) := by
      rw [hpos]; omega
    rw [he,hc]
    exact hpal
  obtain ⟨t,v,cycle,hrun,hchain,_,hs,hcr,hra,_⟩ :=
    shift_to_only_initialized raw s.center s.left s.right (o.radius+(o.interior.length+1))
      (o.interior.length+1) (GalilScaffoldCounter.inc s.radius) lengthCounter
      (GalilScaffoldChainWatch.immediate s.watch) hcounter
      (GalilScaffoldCounter.inc_canonical _ hrad.1) hlen
      (GalilScaffoldCounter.inc_canonical _ hcredit.1) hm hcenter hpcenter hscan
      (by omega) (by omega) hc hnew hv hp halign hi.caught.lagZero hb
  have he : o.radius+(o.interior.length+1)+1-(o.interior.length+1) = o.radius+1 := by omega
  exact ⟨t,v,cycle,hrun,hchain,he ▸ hs,hcr,he ▸ hra⟩

#print axioms OnlyOrigin.reshift_initialized

theorem append_caught_tick {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (hz : GalilScaffoldCounter.zero t.lag = true) (hg : GalilScaffoldChainWatch.Good t) :
    GalilScaffoldChainWatch.Run s (bs ++ [true]) (GalilScaffoldChainWatch.immediate t) := by
  have hpos : GalilScaffoldCounter.positive t.lag = false := by
    simp only [GalilScaffoldCounter.zero,Bool.and_eq_true] at hz
    simp [GalilScaffoldCounter.positive,hz.1]
  have ht : GalilScaffoldChainWatch.Tick t true (GalilScaffoldChainWatch.immediate t) :=
    .step (.idle t hpos) (.immediate t hz hg)
  induction hr with
  | stop => exact .next ht (.stop _)
  | next hstep hrest ih => exact .next hstep (ih hz hg hpos ht)

theorem caught_scan_prediction {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head raw)
    (hp : s.machine.verifier.head.focus ≠ none) (l outer : PlaceHead) (radius initialRadius : ℕ)
    (hi : ScanInvariant raw (position s.machine.verifier) radius l outer)
    (hd : GalilScaffoldCounter.value s.machine.control.distance = 0)
    (hl : GalilScaffoldCounter.value s.lag = initialRadius)
    (hz : GalilScaffoldCounter.zero t.lag = true)
    (hcount : initialRadius+bs.count true = radius)
    (hc : canRight outer) (a : Fin 3)
    (hprediction : GalilScaffoldChainConsume.symbol t.machine.control.period.focus = some a)
    (hread : GalilScaffoldInputHead.read (right outer) = some a) :
    position t.machine.verifier = position outer ∧
      GalilScaffoldChainWatch.Good t ∧
      GalilScaffoldChainWatch.Run s (bs ++ [true]) (GalilScaffoldChainWatch.immediate t) := by
  have hzero : GalilScaffoldCounter.value t.lag = 0 := by
    simp only [GalilScaffoldCounter.zero,Bool.and_eq_true,List.isEmpty_iff] at hz
    simp [GalilScaffoldCounter.value,hz.1,hz.2]
  have hpos := caught_position hr raw hh hp initialRadius hd hl hzero
  have halign : position t.machine.verifier = position outer := by
    have ho := hi.rightPos
    omega
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  have hrep := reads_word ht.reads raw hh
  have hpres := reads_present ht.reads hp
  have hg := aligned_prediction_good t outer raw hrep hi.rightRep hpres hi.rightPresent
    hc halign a hprediction hread
  exact ⟨halign,hg,append_caught_tick hr hz hg⟩

#print axioms caught_scan_prediction
#print axioms append_caught_tick
#print axioms aligned_prediction_good
#print axioms prepared_radius_alignment
#print axioms acceptedRadius_canonical
#print axioms prepared_caught_position

theorem watch_shift_palindrome {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (a : Fin 2) (ls suffix : List (Fin 2)) (gap : Bool)
    (w : List (Fin 3)) (span lower radius : ℕ) (c b : Fin 3) (xs : List (Fin 3))
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take span)
    (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head ((a :: ls).reverse ++ suffix))
    (hp : s.machine.verifier.head.focus ≠ none)
    (hs : s.machine.control = GalilScaffoldChainConsume.ready c xs b)
    (hstart : position s.machine.verifier =
      if gap then 2*(ls.length+1) else 2*(ls.length+1)-1)
    (hpal : Manacher.PalAt (encoded ((a :: ls).reverse ++ suffix))
      (position s.machine.verifier) radius)
    (hsize : 2*(xs.length+1) ≤ radius)
    (initialRadius : ℕ) (hlag : GalilScaffoldCounter.value s.lag = initialRadius)
    (hzero : GalilScaffoldCounter.value t.lag = 0)
    (hcount : initialRadius+bs.count true = radius+1) :
    Manacher.PalAt (encoded ((a :: ls).reverse ++ suffix))
      (position s.machine.verifier+(xs.length+1)) (radius+1-(xs.length+1)) := by
  let raw := (a :: ls).reverse ++ suffix
  have hcaught := caught_position hr raw hh hp initialRadius
    (by rw [hs]; rfl) hlag hzero
  have hend : position s.machine.verifier+radius+1 ≤ position t.machine.verifier := by omega
  obtain ⟨n,hpos,hperiod⟩ := watch_input_period hr raw hh hp c b xs hs
  obtain ⟨actual,htrace,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  have hrep := reads_word htrace.reads raw hh
  have hpres := reads_present htrace.reads hp
  have hbounds := represented_position t.machine.verifier.head raw hrep hpres
  have hlast : position t.machine.verifier < (encoded raw).length := by
    simp only [encoded,List.length_append,List.length_singleton,pairs_length]
    unfold position
    split <;> omega
  have hshort := candidate_short_palindrome a ls suffix gap w span lower (xs.length+1) hw hc
  rw [← hstart] at hshort
  apply shift_from_right (encoded raw) (position s.machine.verifier) radius (xs.length+1)
    hpal (by omega) hsize hshort (by omega)
  intro j hj hb
  let i := j-position s.machine.verifier-1
  have hi : i+2*(xs.length+1) < n := by dsimp only [i]; omega
  have he := hperiod i hi
  have h1 : position s.machine.verifier+(i+1) = j := by dsimp only [i]; omega
  have h2 : position s.machine.verifier+(i+2*(xs.length+1)+1) = j+2*(xs.length+1) := by
    dsimp only [i]; omega
  simpa only [h1,h2] using he

/-- Restart guards and preserved scan, not the reset/idle/clock transition. -/
def OnlyRestartReady (raw : List (Fin 2)) (center radius : ℕ)
    (s : OnlyCompareState) : Prop :=
  ScanInvariant raw center radius s.left s.right ∧
    s.watch.machine.control.broken = true ∧
    GalilScaffoldCounter.negative s.watch.margin = false ∧
    GalilScaffoldCounter.positive s.watch.machine.control.last = true ∧
    GalilScaffoldCounter.zero s.watch.lag = true ∧
    GalilScaffoldInputHead.read s.center ≠ none ∧
    RadiusRep s.radius radius ∧ GalilScaffoldCounter.negative s.radius = false ∧
    (GalilScaffoldSearchFinish.begin s.watch.machine.control.last s.radius).work =
      s.watch.machine.control.last ∧
    GalilScaffoldCounter.Canonical s.watch.machine.control.last

theorem OnlyRestartReady.start_search {raw : List (Fin 2)} {center radius : ℕ}
    {s : OnlyCompareState} (h : OnlyRestartReady raw center radius s)
    {n slots : ℕ} (entry : ℕ) (search : GalilScaffoldSearchFinish.SearchState n slots) :
    GalilScaffoldCounter.negative s.watch.machine.control.last = false ∧
    GalilScaffoldCounter.negative s.radius = false ∧
    GalilScaffoldInputHead.read s.center ≠ none ∧
    (let out := GalilScaffoldSearchFinish.startSearch entry
       s.watch.machine.control.last s.radius search
     GalilScaffoldRawTick.Represents out.program
       ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
     out.program.config.heap = search.program.config.heap ∧
     out.lower = s.watch.machine.control.last ∧ out.scheduler.mode = .grow ∧
     out.scheduler.work = out.lower ∧ out.scheduler.span = GalilScaffoldCounter.reset ∧
     GalilScaffoldCounter.value out.scheduler.debt + GalilScaffoldCounter.value s.radius = 0 ∧
     out.scheduler.finalStage = false ∧ out.scheduler.quarter = 0) := by
  obtain ⟨_,_,_,hp,_,hcenter,_,hrad,_,hc⟩ := h
  have hv := (GalilScaffoldCounter.positive_iff _ hc).1 hp
  have hn : GalilScaffoldCounter.negative s.watch.machine.control.last = false := by
    cases he : GalilScaffoldCounter.negative s.watch.machine.control.last with
    | false => rfl
    | true =>
      have := (GalilScaffoldCounter.negative_iff _ hc).1 he
      omega
  exact ⟨hn,hrad,hcenter,GalilScaffoldSearchFinish.startSearch_positive
    entry _ s.radius search hp⟩

#print axioms OnlyRestartReady.start_search

inductive ChainMode
  | idle | copy | back | watch | broken
  deriving DecidableEq

/-- Projection of the fields touched by background's broken-chain restart.
It does not model the rest of the outer controller. -/
structure RestartState (n slots : ℕ) where
  scan : OnlyCompareState
  search : GalilScaffoldSearchFinish.SearchState n slots
  chainMode : ChainMode
  periodOnly : Bool
  restarts : ℕ
  clock : ℕ

def restart {n slots : ℕ} (entry delay : ℕ) (s : RestartState n slots) :
    Option (RestartState n slots) :=
  if s.chainMode = .broken ∧
      GalilScaffoldCounter.negative s.scan.watch.margin = false ∧
      GalilScaffoldCounter.positive s.scan.watch.machine.control.last = true ∧
      GalilScaffoldCounter.zero s.scan.watch.lag = true ∧
      GalilScaffoldCounter.negative s.scan.watch.machine.control.last = false ∧
      GalilScaffoldCounter.negative s.scan.radius = false ∧
      GalilScaffoldInputHead.read s.scan.center ≠ none then
    some {s with search := GalilScaffoldSearchFinish.startSearch entry s.scan.watch.machine.control.last s.scan.radius s.search, chainMode := .idle, restarts := s.restarts+1, clock := delay}
  else none

theorem restart_ready {raw : List (Fin 2)} {center radius n slots : ℕ}
    (s : RestartState n slots) (h : OnlyRestartReady raw center radius s.scan)
    (hm : s.chainMode = .broken) (entry delay : ℕ) :
    ∃ t, restart entry delay s = some t ∧ t.scan = s.scan ∧
      t.chainMode = .idle ∧ t.restarts = s.restarts+1 ∧ t.clock = delay ∧
      GalilScaffoldRawTick.Represents t.search.program
        ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
      t.search.program.config.heap = s.search.program.config.heap ∧
      t.search.lower = s.scan.watch.machine.control.last ∧
      t.search.scheduler.mode = .grow ∧ t.search.scheduler.work = t.search.lower := by
  obtain ⟨hl,hr,hc,hprogram,hheap,hlower,hgrow,hwork,_⟩ := h.start_search entry s.search
  obtain ⟨_,_,hmargin,hpositive,hlag,_⟩ := h
  refine ⟨{s with search := GalilScaffoldSearchFinish.startSearch entry s.scan.watch.machine.control.last s.scan.radius s.search, chainMode := .idle, restarts := s.restarts+1, clock := delay},?_,
    rfl,rfl,rfl,rfl,hprogram,hheap,hlower,hgrow,hwork⟩
  simp [restart,hm,hmargin,hpositive,hlag,hl,hr,hc]

#print axioms restart_ready

/-- Enabled caught only-mode matched branch: the outer heads/counter have
advanced and consume publishes its failure to the chain mode, as in Scala.
Caller legality is supplied by the comparison proofs, not checked here. -/
def matchedRestartState {n slots : ℕ} (s : RestartState n slots) : RestartState n slots :=
  let next := onlyCompareNext s.scan
  {s with scan := next, chainMode := if next.watch.machine.control.broken then .broken else .watch}

/-- Only the caught, only-mode matching branch. None means this branch is
not applicable, not that the entire controller rejects the input. -/
def dispatchOnlyMatch {n slots : ℕ} (s : RestartState n slots) :
    Option (RestartState n slots) := by
  letI : Decidable (canRight s.scan.right) := by unfold canRight; infer_instance
  exact if s.chainMode = .watch ∧ s.periodOnly = true ∧
      GalilScaffoldCounter.zero s.scan.watch.lag = true ∧ canRight s.scan.right ∧
      GalilScaffoldCounter.positive s.scan.cycle = true ∧
      (GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.scan.left) =
        GalilScaffoldChainConsume.symbol s.scan.watch.machine.control.period.focus ↔
        GalilScaffoldCounter.singlePositive s.scan.cycle = false) ∧
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.scan.left) =
        GalilScaffoldInputHead.read (right s.scan.right) then
    some (matchedRestartState s)
  else none

theorem dispatch_only_match {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {center radius n slots : ℕ} (s : RestartState n slots) (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.scan.left s.scan.right s.scan.watch s.scan.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.scan.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.scan.left)
    (hm : s.chainMode = .watch) (ho : s.periodOnly = true) (hc : canRight s.scan.right)
    (he : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.scan.left) =
      GalilScaffoldInputHead.read (right s.scan.right)) :
    dispatchOnlyMatch s = some (matchedRestartState s) := by
  have hp := (only_scan_dispatch hi).1
  have hcheck := o.check_pair extra hi ht hl
  have hz := hi.caught.lagZero
  unfold dispatchOnlyMatch
  exact if_pos ⟨hm,ho,hz,hc,hp,hcheck,he⟩

#print axioms dispatch_only_match

theorem restart_after_match {raw : List (Fin 2)} {center radius n slots : ℕ}
    (s : RestartState n slots)
    (h : OnlyRestartReady raw center radius (onlyCompareNext s.scan))
    (entry delay : ℕ) :
    ∃ t, restart entry delay (matchedRestartState s) = some t ∧
      t.scan = onlyCompareNext s.scan ∧ t.chainMode = .idle ∧
      t.restarts = s.restarts+1 ∧ t.clock = delay ∧
      GalilScaffoldRawTick.Represents t.search.program
        ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
      t.search.program.config.heap = s.search.program.config.heap ∧
      t.search.lower = (onlyCompareNext s.scan).watch.machine.control.last ∧
      t.search.scheduler.mode = .grow ∧ t.search.scheduler.work = t.search.lower := by
  have hm : (matchedRestartState s).chainMode = .broken := by
    simp only [matchedRestartState,h.2.1,ite_true]
  exact restart_ready (matchedRestartState s) h hm entry delay

#print axioms restart_after_match

/-- Arrival updates every input head carried by this projection, including
the verifier; counters and the private period tape are unchanged. -/
def compareArrival (s : OnlyCompareState) (a : Fin 2) : OnlyCompareState :=
  {s with center := arrive s.center a, left := arrive s.left a, right := arrive s.right a, watch := {s.watch with machine := {s.watch.machine with verifier := arrive s.watch.machine.verifier a}}}

theorem OnlyRestartReady.arrival {raw : List (Fin 2)} {center radius : ℕ}
    {s : OnlyCompareState} (h : OnlyRestartReady raw center radius s) (a : Fin 2) :
    OnlyRestartReady (raw ++ [a]) center radius (compareArrival s a) := by
  obtain ⟨hscan,hb,hm,hl,hz,hc,hr,hn,hw,hcanon⟩ := h
  exact ⟨scan_arrival hscan a,hb,hm,hl,hz,hc,hr,hn,hw,hcanon⟩

def restartArrival {n slots : ℕ} (s : RestartState n slots) (a : Fin 2) : RestartState n slots :=
  {s with scan := compareArrival s.scan a}

theorem restart_after_arrival {raw : List (Fin 2)} {center radius n slots : ℕ}
    (s : RestartState n slots) (h : OnlyRestartReady raw center radius s.scan)
    (hm : s.chainMode = .broken) (a : Fin 2) (entry delay : ℕ) :
    ∃ t, restart entry delay (restartArrival s a) = some t ∧
      ScanInvariant (raw ++ [a]) center radius t.scan.left t.scan.right ∧
      t.chainMode = .idle ∧ t.restarts = s.restarts+1 ∧ t.clock = delay ∧
      GalilScaffoldRawTick.Represents t.search.program
        ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
      t.search.program.config.heap = s.search.program.config.heap := by
  have ha := h.arrival a
  obtain ⟨t,hr,hs,hm',hn,hclock,hprogram,hheap,_⟩ :=
    restart_ready (restartArrival s a) ha hm entry delay
  refine ⟨t,hr,?_,hm',hn,hclock,hprogram,hheap⟩
  simpa only [hs,restartArrival] using ha.1

#print axioms OnlyRestartReady.arrival
#print axioms restart_after_arrival

/-- The scan-clock phase immediately following a broken-chain background
restart. Requires delay>1 to exclude a new comparison on this very tick. -/
def restartScanTick {n slots : ℕ} (entry delay : ℕ) (available : Bool)
    (s : RestartState n slots) : Option (RestartState n slots) :=
  (restart entry delay s).map (fun t =>
    {t with clock := (GalilScaffoldMatchClock.run delay t.clock [available]).1})

theorem restart_scan_tick {raw : List (Fin 2)} {center radius n slots : ℕ}
    (s : RestartState n slots) (h : OnlyRestartReady raw center radius s.scan)
    (hm : s.chainMode = .broken) (entry delay : ℕ) (hd : 1 < delay) (available : Bool) :
    ∃ t, restartScanTick entry delay available s = some t ∧ t.scan = s.scan ∧
      t.chainMode = .idle ∧ t.restarts = s.restarts+1 ∧
      t.clock = (if available then delay-1 else delay) ∧
      (GalilScaffoldMatchClock.run delay delay [available]).2 = 0 ∧
      GalilScaffoldRawTick.Represents t.search.program
        ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
      t.search.scheduler.mode = .grow := by
  obtain ⟨t,hr,hs,hmode,hcount,hclock,hprogram,_,_,hgrow,_⟩ :=
    restart_ready s h hm entry delay
  have he : delay ≠ 1 := by omega
  have hclockRun : GalilScaffoldMatchClock.run delay delay [available] =
      (if available then delay-1 else delay,0) := by
    cases available <;> simp [GalilScaffoldMatchClock.run,he]
  refine ⟨{t with clock := (GalilScaffoldMatchClock.run delay t.clock [available]).1},
    ?_,hs,hmode,hcount,?_,?_,hprogram,hgrow⟩
  · simp only [restartScanTick,hr,Option.map_some]
  · rw [hclock,hclockRun]
  · rw [hclockRun]

#print axioms restart_scan_tick

def scanAvailable (replaying advanceTrailingGap : Bool) (r : PlaceHead) : Bool :=
  replaying || (if advanceTrailingGap then
    !r.gap || !r.head.right.isEmpty || !r.head.incoming.isEmpty
    else !r.head.right.isEmpty || !r.head.incoming.isEmpty)

def receiveRestart {n slots : ℕ} (s : RestartState n slots) (input : Option (Fin 2)) :
    RestartState n slots :=
  match input with
  | none => s
  | some a => restartArrival s a

/-- The broken-chain branch of a scan tick, with arrival preceding background
restart and availability computed from the resulting head. delay>1 is required. -/
def restartInputTick {n slots : ℕ} (entry delay : ℕ) (replaying trailing : Bool)
    (input : Option (Fin 2)) (s : RestartState n slots) : Option (RestartState n slots) :=
  let arrived := receiveRestart s input
  restartScanTick entry delay (scanAvailable replaying trailing arrived.scan.right) arrived

theorem restart_input_tick {raw : List (Fin 2)} {center radius n slots : ℕ}
    (s : RestartState n slots) (h : OnlyRestartReady raw center radius s.scan)
    (hm : s.chainMode = .broken) (entry delay : ℕ) (hd : 1 < delay)
    (replaying trailing : Bool) (input : Option (Fin 2)) :
    ∃ t, restartInputTick entry delay replaying trailing input s = some t ∧
      ScanInvariant (raw ++ input.toList) center radius t.scan.left t.scan.right ∧
      t.chainMode = .idle ∧ t.restarts = s.restarts+1 ∧
      t.clock = (if scanAvailable replaying trailing (receiveRestart s input).scan.right
        then delay-1 else delay) ∧
      GalilScaffoldRawTick.Represents t.search.program
        ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
      t.search.scheduler.mode = .grow := by
  have ha : OnlyRestartReady (raw ++ input.toList) center radius
      (receiveRestart s input).scan := by
    cases input with
    | none => simpa [receiveRestart] using h
    | some a => exact h.arrival a
  have hmode : (receiveRestart s input).chainMode = .broken := by
    cases input <;> exact hm
  obtain ⟨t,hr,hs,hmode',hcount,hclock,_,hprogram,hgrow⟩ :=
    restart_scan_tick (receiveRestart s input) ha hmode entry delay hd
      (scanAvailable replaying trailing (receiveRestart s input).scan.right)
  refine ⟨t,hr,?_,hmode',?_,hclock,hprogram,hgrow⟩
  · simpa only [hs] using ha.1
  · cases input <;> exact hcount

#print axioms restart_input_tick

/-- Terminal matching dispatch followed by the next broken-chain scan tick,
including its input arrival and post-restart clock decrement. -/
theorem terminal_dispatch_next_tick {raw : List (Fin 2)} (o : OnlyOrigin raw)
    {center radius n slots : ℕ} (s : RestartState n slots) (extra : List (Fin 3))
    (hsteps : o.steps = o.interior.length+1)
    (hphase : o.watched.machine.control.phase = 4)
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.scan.left s.scan.right s.scan.watch s.scan.cycle)
    (hcredit : OnlyCredit s.scan.watch s.scan.cycle) (hrad : RadiusRep s.scan.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.scan.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.scan.left)
    (hcenter : GalilScaffoldInputHead.read s.scan.center ≠ none)
    (hm : s.chainMode = .watch) (ho : s.periodOnly = true)
    (hend : GalilScaffoldCounter.singlePositive s.scan.cycle = true)
    (hc : canRight s.scan.right)
    (he : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.scan.left) =
      GalilScaffoldInputHead.read (right s.scan.right)) (entry delay : ℕ)
    (hdelay : 1 < delay) (replaying trailing : Bool) (input : Option (Fin 2)) :
    ∃ t, (dispatchOnlyMatch s).bind (restartInputTick entry delay replaying trailing input) = some t ∧
      ScanInvariant (raw ++ input.toList) center (radius+1) t.scan.left t.scan.right ∧
      t.chainMode = .idle ∧ t.restarts = s.restarts+1 ∧
      t.clock = (if scanAvailable replaying trailing
        (receiveRestart (matchedRestartState s) input).scan.right then delay-1 else delay) ∧
      GalilScaffoldRawTick.Represents t.search.program
        ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
      t.search.scheduler.mode = .grow := by
  have hd := GalilScaffoldChainPrediction.watch_phase_distance o.watchRun
    o.token o.boundary o.interior o.ready hphase
  have hready : OnlyRestartReady raw center (radius+1) (onlyCompareNext s.scan) :=
    only_matched_restart o (.stop s.scan) hsteps hd extra hi hcredit hrad ht hl
      hcenter hend hc he
  have hdispatch := dispatch_only_match o s extra hi ht hl hm ho hc he
  have hbroken : (matchedRestartState s).chainMode = .broken := by
    simp only [matchedRestartState,hready.2.1,ite_true]
  obtain ⟨t,hrestart,hscan,hmode,hcount,hclock,hprogram,hgrow⟩ :=
    restart_input_tick (matchedRestartState s) hready hbroken entry delay hdelay
      replaying trailing input
  refine ⟨t,?_,hscan,hmode,hcount,hclock,hprogram,hgrow⟩
  simpa only [hdispatch,Option.bind_some] using hrestart

#print axioms terminal_dispatch_next_tick

theorem scan_prediction_shift {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (a : Fin 2) (ls suffix : List (Fin 2)) (gap : Bool)
    (w : List (Fin 3)) (span lower radius : ℕ) (c b : Fin 3) (xs : List (Fin 3))
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take span)
    (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head ((a :: ls).reverse ++ suffix))
    (hp : s.machine.verifier.head.focus ≠ none)
    (hs : s.machine.control = GalilScaffoldChainConsume.ready c xs b)
    (hstart : position s.machine.verifier =
      if gap then 2*(ls.length+1) else 2*(ls.length+1)-1)
    (l outer : PlaceHead)
    (hi : ScanInvariant ((a :: ls).reverse ++ suffix) (position s.machine.verifier) radius l outer)
    (hphase : t.machine.control.phase = 4)
    (initialRadius : ℕ) (hlag : GalilScaffoldCounter.value s.lag = initialRadius)
    (hzero : GalilScaffoldCounter.zero t.lag = true)
    (hcount : initialRadius+bs.count true = radius)
    (hcan : canRight outer) (predicted : Fin 3)
    (hpred : GalilScaffoldChainConsume.symbol t.machine.control.period.focus = some predicted)
    (hread : GalilScaffoldInputHead.read (right outer) = some predicted)
    (radiusCounter lengthCounter : GalilScaffoldCounter.Counter)
    (hcounter : GalilScaffoldCounter.value radiusCounter = (radius : ℤ)+1)
    (hrcanon : GalilScaffoldCounter.Canonical radiusCounter)
    (hlcanon : GalilScaffoldCounter.Canonical lengthCounter)
    (prepRadius : GalilScaffoldCounter.Counter)
    (hprepCanonical : GalilScaffoldCounter.Canonical prepRadius)
    (startMatch doneMatch : Bool) (copyMatches backMatches : List Bool)
    (hcopyLength : copyMatches.length = xs.length+1)
    (hprepLag : s.lag = (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start prepRadius)
      (GalilScaffoldChainCredits.prepEvents startMatch doneMatch copyMatches backMatches)).lag)
    (hprepMargin : s.margin = (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start prepRadius)
      (GalilScaffoldChainCredits.prepEvents startMatch doneMatch copyMatches backMatches)).margin)
    (hmismatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right outer)) :
    Manacher.PalAt (encoded ((a :: ls).reverse ++ suffix))
      (position s.machine.verifier+(xs.length+1)) (radius+1-(xs.length+1)) ∧
    ∃ endpoint watchEnd cycleEnd,
      ShiftRun ⟨s.machine.verifier,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat (xs.length+1),radiusCounter,lengthCounter⟩ (xs.length+1) endpoint ∧
      ChainShiftRun ⟨s.machine.verifier,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat (xs.length+1),radiusCounter,lengthCounter⟩
        (GalilScaffoldChainWatch.immediate t) GalilScaffoldCounter.reset (xs.length+1)
        endpoint watchEnd cycleEnd ∧
      GalilScaffoldCounter.zero endpoint.remaining = true ∧
      GalilScaffoldCounter.value endpoint.radius = ((radius+1-(xs.length+1) : ℕ) : ℤ) ∧
      GalilScaffoldCounter.value endpoint.length =
        GalilScaffoldCounter.value lengthCounter-2*(xs.length+1) ∧
      OnlyScan ((a :: ls).reverse ++ suffix) (position endpoint.center)
        (radius+1-(xs.length+1)) (2*(xs.length+1)) 0 endpoint.left (right outer)
        watchEnd cycleEnd ∧
      OnlyCredit watchEnd cycleEnd ∧
      RadiusRep endpoint.radius (radius+1-(xs.length+1)) ∧
      GalilScaffoldChainWatchTrace.Trace watchEnd.machine [] watchEnd.machine ∧
      LeftMoves endpoint.left 0 endpoint.left ∧
      GalilScaffoldInputHead.read endpoint.center ≠ none ∧
      ∃ origin : OnlyOrigin ((a :: ls).reverse ++ suffix),
        origin.start = s ∧ origin.watched = GalilScaffoldChainWatch.immediate t ∧
        origin.shifted = watchEnd ∧ origin.shiftEnd = endpoint ∧
        origin.resumeLeft = endpoint.left ∧ origin.interior = xs ∧
        origin.steps = xs.length+1 ∧ origin.finish = cycleEnd ∧
        origin.center = position s.machine.verifier ∧ origin.radius = radius ∧
        4*(xs.length+1) ≤ GalilScaffoldCounter.value
          (GalilScaffoldChainWatch.immediate t).machine.control.distance ∧
        ∀ (n : ℕ) (finalState : OnlyCompareState),
          OnlyMatchedRun ⟨endpoint.center,endpoint.left,right outer,watchEnd,cycleEnd,
            endpoint.radius⟩ n finalState →
          GalilScaffoldCounter.singlePositive finalState.cycle = true →
          canRight finalState.right →
          GalilScaffoldInputHead.read (GalilScaffoldInputHead.left finalState.left) =
            GalilScaffoldInputHead.read (right finalState.right) →
          OnlyRestartReady ((a :: ls).reverse ++ suffix) (position endpoint.center)
            (radius+1-(xs.length+1)+n+1) (onlyCompareNext finalState) := by
  have hdist := GalilScaffoldChainPrediction.watch_phase_distance hr c b xs hs hphase
  have hreadyDist : GalilScaffoldCounter.value s.machine.control.distance = 0 := by
    rw [hs]
    rfl
  have hprepCan := GalilScaffoldChainCredits.run_canonical
    (GalilScaffoldChainCredits.start prepRadius)
    (GalilScaffoldChainCredits.prepEvents startMatch doneMatch copyMatches backMatches)
    hprepCanonical hprepCanonical
  have hwatchCanonical : GalilScaffoldChainWatch.CanonicalState s := by
    exact ⟨hprepLag ▸ hprepCan.2,hprepMargin ▸ hprepCan.1⟩
  have hprepared : GalilScaffoldChainWatch.balance s = 4*((xs.length+1 : ℕ) : ℤ) := by
    have hb := GalilScaffoldChainWatch.prepared_balance s.machine hreadyDist
      prepRadius startMatch doneMatch copyMatches backMatches
    simpa only [GalilScaffoldChainWatch.balance,hprepLag,hprepMargin,hcopyLength] using hb
  have hlagEnd : GalilScaffoldCounter.value t.lag = 0 := by
    have he := hzero
    simp only [GalilScaffoldCounter.zero,Bool.and_eq_true,List.isEmpty_iff] at he
    simp [GalilScaffoldCounter.value,he.1,he.2]
  have hprogress := watch_progress hr
  have hsize : 2*(xs.length+1) ≤ radius := by omega
  have hmargin := (GalilScaffoldChainWatch.run_canonical hr hwatchCanonical).2
  have hmarginValue := GalilScaffoldChainWatch.caught_margin hr (xs.length+1)
    hprepared hlagEnd (by simpa using hdist)
  obtain ⟨_,_,hext⟩ := caught_scan_prediction hr _ hh hp l outer radius initialRadius
    hi (by rw [hs]; rfl) hlag hzero hcount hcan predicted hpred hread
  have hz : GalilScaffoldCounter.value (GalilScaffoldChainWatch.immediate t).lag = 0 := by
    simp only [GalilScaffoldCounter.zero,Bool.and_eq_true,List.isEmpty_iff] at hzero
    simp [GalilScaffoldChainWatch.immediate,GalilScaffoldCounter.value,hzero.1,hzero.2]
  have hcount' : initialRadius+(bs ++ [true]).count true = radius+1 := by
    simp only [List.count_append,List.count_cons_self,List.count_nil]
    omega
  have hnew := watch_shift_palindrome hext a ls suffix gap w span lower radius c b xs
    hw hc hh hp hs hstart hi.palindrome hsize initialRadius hlag hz hcount'
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hext
  have hrep := reads_word ht.reads _ hh
  have hpres := reads_present ht.reads hp
  have hpos := caught_position hext _ hh hp initialRadius (by rw [hs]; rfl) hlag hz
  have hright := right_position outer hcan
    (represented_position outer.head _ hi.rightRep hi.rightPresent).1
  have halign : position (GalilScaffoldChainWatch.immediate t).machine.verifier =
      position (right outer) := by have := hi.rightPos; omega
  have hbroken : (GalilScaffoldChainWatch.immediate t).machine.control.broken = false := by
    rw [ht.broken,hs]
    rfl
  obtain ⟨endpoint,watchEnd,cycleEnd,hshift,hchain,hremaining,hradius,hlength,hscan⟩ :=
    shift_to_only _ s.machine.verifier l outer radius (xs.length+1)
    radiusCounter lengthCounter (GalilScaffoldChainWatch.immediate t) hcounter hh hp hi
      (by omega) (by omega) hcan hnew hrep hpres halign hzero hbroken
  have hcanon : ShiftCanonical ⟨s.machine.verifier,GalilScaffoldInputHead.left l,
      GalilScaffoldCounter.ofNat (xs.length+1),radiusCounter,lengthCounter⟩ :=
    ⟨GalilScaffoldCounter.ofNat_canonical _,hrcanon,hlcanon⟩
  have hcounter' : GalilScaffoldCounter.value radiusCounter = ((radius+1 : ℕ) : ℤ) := by
    simpa using hcounter
  have hmargin' : GalilScaffoldCounter.Canonical
      (GalilScaffoldChainWatch.immediate t).margin :=
    GalilScaffoldCounter.inc_canonical _ hmargin
  have hmarginValue' : 0 ≤ GalilScaffoldCounter.value
      (GalilScaffoldChainWatch.immediate t).margin := by
    change 0 ≤ GalilScaffoldCounter.value (GalilScaffoldCounter.inc t.margin)
    rw [GalilScaffoldCounter.inc_value]
    omega
  obtain ⟨_,hcredit,hrad,htrace,hleft,hcenter⟩ :=
    shift_only_entry hshift hchain (by omega) (by omega) hcanon hcounter' _ (right outer)
      hh hp hscan.caught.scan hrep hpres halign hzero hbroken hmargin' hmarginValue'
  have hcenterPos := (shift_run_center hshift _ hh hp).2.2
  have hresume : ScanInvariant ((a :: ls).reverse ++ suffix)
      (position s.machine.verifier+(xs.length+1)) (radius+1-(xs.length+1))
      endpoint.left (right outer) := by
    simpa only [hcenterPos] using hscan.caught.scan
  let origin : OnlyOrigin ((a :: ls).reverse ++ suffix) := {
    start := s
    watched := GalilScaffoldChainWatch.immediate t
    shifted := watchEnd
    ticks := bs ++ [true]
    shiftStart := ⟨s.machine.verifier,GalilScaffoldInputHead.left l,
      GalilScaffoldCounter.ofNat (xs.length+1),radiusCounter,lengthCounter⟩
    shiftEnd := endpoint
    cycle := GalilScaffoldCounter.reset
    finish := cycleEnd
    steps := xs.length+1
    center := position s.machine.verifier
    radius := radius
    left := l
    rightHead := outer
    resumeLeft := endpoint.left
    token := c
    boundary := b
    interior := xs
    watchRun := hext
    shiftRun := hchain
    scan := hi
    available := hcan
    mismatch := hmismatch
    represents := hh
    present := hp
    ready := hs
    startPosition := rfl
    endPosition := by rw [halign,hright,hi.rightPos]
    size := hsize
    resumed := hresume }
  have heprogress := watch_progress hext
  have hd : 4*(xs.length+1) ≤ GalilScaffoldCounter.value
      (GalilScaffoldChainWatch.immediate t).machine.control.distance := by
    rw [hreadyDist,hlag,hz] at heprogress
    have hc' := hcount'
    simp only [List.count_append,List.count_cons_self,List.count_nil] at heprogress hc'
    omega
  refine ⟨hnew,endpoint,watchEnd,cycleEnd,hshift,hchain,hremaining,hradius,hlength,
    hscan,hcredit,hrad,htrace,hleft,hcenter,origin,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hd,?_⟩
  intro n finalState run hend havailable hmatched
  exact only_matched_restart origin run rfl hd [] hscan hcredit hrad htrace hleft
    hcenter hend havailable hmatched

#print axioms scan_prediction_shift
#print axioms caught_position
#print axioms watch_shift_palindrome
#print axioms candidate_short_palindrome
#print axioms backward_palindrome
#print axioms shift_from_right
#print axioms shift_after_prediction
#print axioms shift_geometry
#print axioms watch_displacement
#print axioms scan_initial
#print axioms scan_first
#print axioms scan_arrival
#print axioms scan_matched
#print axioms palindrome_arrival
#print axioms found_window_safe
#print axioms window_mirrored_safe
#print axioms reachable_mirrored_safe
#print axioms reachable_coordinate_supply
#print axioms rightReads_suffix
#print axioms encoded_suffix
#print axioms reachable_prefix_supply
#print axioms represented_supply
#print axioms reads_word
end PalPeg.GalilScaffoldChainInputSupply
