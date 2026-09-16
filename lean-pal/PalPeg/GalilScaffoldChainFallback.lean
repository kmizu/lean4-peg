import PalPeg.GalilScaffoldChainReadOrigin
import PalPeg.GalilScaffoldSourceReady
import PalPeg.GalilFppPrepareLayout
import PalPeg.GalilFppMarkedCost
import PalPeg.GalilScaffoldPreload
import PalPeg.GalilScaffoldChainAnswer
import PalPeg.GalilScaffoldStagePrepare

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldChainVerifier GalilScaffoldChainVerifyRun

/-! # Fallback dispatch at the comparison level

Scala `stepScan` after the advance: `matchedPlace` if the outer symbols agree,
`beginChainShift` if not replaying, `Chain.canShift` and the prediction is the
right read, otherwise `beginFallback`. The fallback copies the window from the
right head leftwards into the fpp SOURCE tape (`remaining = length+1`), then
homes it; `place_ready` gives that copy/home execution at the place level.
Here the window is tied to the actual right head and the scan word. -/

/-- The fallback branch is taken: neither the matched nor the shift branch. -/
def FallbackGuard (replaying canShift : Bool) (s : OnlyCompareState) : Prop :=
  GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) ≠
    GalilScaffoldInputHead.read (right s.right) ∧
  ¬ (replaying = false ∧ canShift = true ∧
    GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus =
      GalilScaffoldInputHead.read (right s.right))

/-- A represented right head is the representation of the place whose letters
are the scan word read backwards from the head. -/
theorem right_place {raw : List (Fin 2)} (r : PlaceHead)
    (hrep : GalilScaffoldInputTrace.Represents r.head raw) :
    ∃ (xs rs q : List (Fin 2)), r = represent ⟨xs,r.gap⟩ (rs.map some) q ∧
      raw = xs.reverse ++ rs ++ q := by
  obtain ⟨xs,rs,q,hh,hw⟩ := hrep
  refine ⟨xs,rs,q,?_,hw⟩
  show r = ⟨layout xs (rs.map some) q,r.gap⟩
  rw [← hh]

/-- The fallback window: from the right head and the length counter, the fpp
SOURCE tape after copy and home holds exactly the mirrored prefix of the scan
word ending at the right head, truncated to `length+1` places. This is the
`w = (stream ⟨a :: ls, gap⟩).take span` shape that the fresh watch entry
(`scan_prediction_shift`) later consumes. -/
theorem fallback_window {raw : List (Fin 2)} (s : OnlyCompareState)
    (hrep : GalilScaffoldInputTrace.Represents s.right.head raw)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ) :
    ∃ (xs rs q : List (Fin 2)),
      s.right = represent ⟨xs,s.right.gap⟩ (rs.map some) q ∧
      raw = xs.reverse ++ rs ++ q ∧
      GalilScaffoldCounter.inc length = GalilScaffoldCounter.ofNat (ℓ+1) ∧
      let w := (GalilScaffoldPlace.stream ⟨xs,s.right.gap⟩).take (ℓ+1)
      ∃ y final, GalilScaffoldPlace.Copy
        ⟨⟨xs,s.right.gap⟩,ℓ+1,GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4)⟩
        (w.length+1) y final ∧
        GalilScaffoldLower.Rewind y.tape (w.length+2)
          (GalilScaffoldPreload.bounded (w.map GalilFppPreparation.symbol)) ∧
        (final = true ↔ (GalilScaffoldPlace.stream ⟨xs,s.right.gap⟩).length ≤ ℓ+1) := by
  obtain ⟨xs,rs,q,hr,hw⟩ := right_place s.right hrep
  refine ⟨xs,rs,q,hr,hw,?_,?_⟩
  · rw [GalilScaffoldChainCatch.canonical_nat length hc ℓ hv,GalilScaffoldCounter.inc_ofNat]
  · exact GalilScaffoldSourceReady.place_ready ⟨xs,s.right.gap⟩ ℓ

#print axioms fallback_window

/-! ## The chosen mark is a palindrome ending at the right head

`prepared_marks` characterises the fpp marks as the palindromic prefixes of
the copied window. Read leftwards from the right head, a prefix of the window
is a suffix of the encoded scan word ending at the head. Scala `stepChoose`
takes the longest odd mark; `stepRewind` then places the centre in its middle.
-/

theorem gaps_length (xs : List (Fin 2)) : (GalilScaffoldPlace.gaps xs).length = 2*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [GalilScaffoldPlace.gaps,ih]; omega

theorem stream_length (a : Fin 2) (xs : List (Fin 2)) (g : Bool) :
    (GalilScaffoldPlace.stream ⟨a :: xs,g⟩).length = (if g then 2 else 1)+2*xs.length := by
  cases g <;> simp [GalilScaffoldPlace.stream,gaps_length] <;> omega

theorem pairs_reverse_gaps (xs : List (Fin 2)) :
    pairs xs.reverse ++ [2] = 2 :: (GalilScaffoldPlace.gaps xs).reverse := by
  induction xs with
  | nil => rfl
  | cons c t ih =>
    have h1 : pairs (c :: t).reverse ++ [2] =
        (pairs t.reverse ++ [2]) ++ [GalilScaffoldPlace.letter c,2] := by
      rw [List.reverse_cons,pairs_append]; simp [pairs]
    rw [h1,ih]
    simp [GalilScaffoldPlace.gaps]

theorem pairs_reverse_stream (a : Fin 2) (xs : List (Fin 2)) :
    pairs (a :: xs).reverse = 2 :: (GalilScaffoldPlace.stream ⟨a :: xs,false⟩).reverse := by
  have h1 : pairs (a :: xs).reverse = (pairs xs.reverse ++ [2]) ++ [GalilScaffoldPlace.letter a] := by
    rw [List.reverse_cons,pairs_append]; simp [pairs]
  rw [h1,pairs_reverse_gaps]
  simp [GalilScaffoldPlace.stream]

/-- The encoded scan word around a represented head: the stream read leftwards
from the head, reversed, sits just after the leading gap. -/
theorem encoded_of_represent (a : Fin 2) (xs rs q : List (Fin 2)) :
    encoded ((a :: xs).reverse ++ rs ++ q) =
      2 :: (GalilScaffoldPlace.stream ⟨a :: xs,false⟩).reverse ++ (pairs (rs ++ q) ++ [2]) := by
  simp only [encoded,List.append_assoc,pairs_append,pairs_reverse_stream]

theorem position_represent (a : Fin 2) (xs : List (Fin 2)) (g : Bool)
    (rs : List (Option (Fin 2))) (q : List (Fin 2)) :
    position (represent ⟨a :: xs,g⟩ rs q) = (GalilScaffoldPlace.stream ⟨a :: xs,g⟩).length := by
  rw [stream_length]
  cases g <;> simp [position,represent,layout] <;> omega

/-- Reading the stream leftwards from the head is reading the encoded word
downwards from the head position. -/
theorem stream_index (a : Fin 2) (xs rs q : List (Fin 2)) (g : Bool) (i : ℕ)
    (hi : i < (GalilScaffoldPlace.stream ⟨a :: xs,g⟩).length) :
    (GalilScaffoldPlace.stream ⟨a :: xs,g⟩)[i]? =
      (encoded ((a :: xs).reverse ++ rs ++ q))[(GalilScaffoldPlace.stream ⟨a :: xs,g⟩).length-i]? := by
  rw [encoded_of_represent]
  set S := GalilScaffoldPlace.stream ⟨a :: xs,false⟩ with hS
  have hlen : S.length = 1+2*xs.length := by rw [hS,stream_length]; simp
  cases g with
  | false =>
    change S[i]? = _
    change i < S.length at hi
    have hk : S.length-i = (S.length-1-i)+1 := by omega
    rw [hk,List.cons_append,List.getElem?_cons_succ,List.getElem?_append_left (by simp; omega),
      List.getElem?_reverse (by omega)]
    congr 1
    omega
  | true =>
    have hT : GalilScaffoldPlace.stream ⟨a :: xs,true⟩ = 2 :: S := by
      rw [hS]; simp [GalilScaffoldPlace.stream]
    rw [hT] at hi ⊢
    simp only [List.length_cons] at hi ⊢
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero]
      have hk : S.length+1-0 = (S.length+1) := by omega
      rw [hk,List.cons_append,List.getElem?_cons_succ,List.getElem?_append_right (by simp),
        List.length_reverse,Nat.sub_self]
      cases rs with
      | nil => cases q with
        | nil => rfl
        | cons c q => simp [pairs]
      | cons c rs => simp [pairs]
    | succ i =>
      rw [List.getElem?_cons_succ]
      have hk : S.length+1-(i+1) = (S.length-1-i)+1 := by omega
      rw [hk,List.cons_append,List.getElem?_cons_succ,List.getElem?_append_left (by simp; omega),
        List.getElem?_reverse (by omega)]
      congr 1
      omega

/-- An odd palindromic prefix of the stream, of length `2r+1`, is a palindrome
of the encoded scan word centred `r` places below the head. -/
theorem stream_prefix_palindrome (a : Fin 2) (xs rs q : List (Fin 2)) (g : Bool) (r : ℕ)
    (hr : 2*r+1 ≤ (GalilScaffoldPlace.stream ⟨a :: xs,g⟩).length) :
    IsPal ((GalilScaffoldPlace.stream ⟨a :: xs,g⟩).take (2*r+1)) ↔
      Manacher.PalAt (encoded ((a :: xs).reverse ++ rs ++ q))
        ((GalilScaffoldPlace.stream ⟨a :: xs,g⟩).length-r) r := by
  set T := GalilScaffoldPlace.stream ⟨a :: xs,g⟩ with hT
  set e := encoded ((a :: xs).reverse ++ rs ++ q) with he
  have hlen : T.length < e.length := by
    have := position_bound (represent ⟨a :: xs,g⟩ (rs.map some) q) ((a :: xs).reverse ++ rs ++ q)
      ⟨a :: xs,rs,q,rfl,rfl⟩ (by simp [represent,layout])
    rw [position_represent] at this
    exact this
  have hidx : ∀ i, i < T.length → T[i]? = e[T.length-i]? := fun i hi => stream_index a xs rs q g i hi
  rw [Manacher.isPal_take_iff_index hr]
  constructor
  · intro h
    refine ⟨by omega,by omega,?_⟩
    intro i hi
    have h1 := hidx (r+i) (by omega)
    have h2 := hidx (r-i) (by omega)
    have hp := h (r+i) (by omega)
    have e1 : T.length-r-i = T.length-(r+i) := by omega
    have e2 : T.length-r+i = T.length-(r-i) := by omega
    have e3 : 2*r+1-1-(r+i) = r-i := by omega
    rw [e1,e2,← h1,← h2,hp,e3]
  · intro h i hi
    obtain ⟨_,_,hp⟩ := h
    have e3 : 2*r+1-1-i = 2*r-i := by omega
    rw [e3]
    by_cases hle : i ≤ r
    · have := hp (r-i) (by omega)
      rw [hidx i (by omega),hidx (2*r-i) (by omega)]
      have e1 : T.length-r-(r-i) = T.length-(2*r-i) := by omega
      have e2 : T.length-r+(r-i) = T.length-i := by omega
      rw [e1,e2] at this
      exact this.symm
    · have := hp (i-r) (by omega)
      rw [hidx i (by omega),hidx (2*r-i) (by omega)]
      have e1 : T.length-r-(i-r) = T.length-i := by omega
      have e2 : T.length-r+(i-r) = T.length-(2*r-i) := by omega
      rw [e1,e2] at this
      exact this

#print axioms stream_prefix_palindrome

/-- Scala `stepChoose`: from the END mark leftwards with alternating parity, the
first odd mark met is the longest odd palindromic prefix of the window. Its
radius is the largest `r` with `2r+1 ≤ |T|` and `T.take (2r+1)` a palindrome. -/
noncomputable def chosenRadius (T : List (Fin 3)) : ℕ :=
  Nat.findGreatest (fun r => 2*r+1 ≤ T.length ∧ IsPal (T.take (2*r+1))) T.length

theorem chosen_spec (T : List (Fin 3)) (hT : T ≠ []) :
    2*chosenRadius T+1 ≤ T.length ∧ IsPal (T.take (2*chosenRadius T+1)) := by
  classical
  have h0 : 2*0+1 ≤ T.length ∧ IsPal (T.take (2*0+1)) := by
    obtain ⟨x,xs,rfl⟩ := List.exists_cons_of_ne_nil hT
    exact ⟨by simp,by simp [IsPal]⟩
  exact Nat.findGreatest_spec (P := fun r => 2*r+1 ≤ T.length ∧ IsPal (T.take (2*r+1)))
    (Nat.zero_le _) h0

theorem chosen_greatest (T : List (Fin 3)) (r : ℕ) (hr : 2*r+1 ≤ T.length)
    (hp : IsPal (T.take (2*r+1))) : r ≤ chosenRadius T := by
  classical
  exact Nat.le_findGreatest (by omega) ⟨hr,hp⟩

/-- `stepChoose` then `stepRewind`: the new centre sits `r` places below the
right head and carries a palindrome of radius `r` there, the longest odd
palindrome of the encoded scan word ending at the head. -/
theorem choose_rewind (a : Fin 2) (xs rs q : List (Fin 2)) (g : Bool) :
    let T := GalilScaffoldPlace.stream ⟨a :: xs,g⟩
    let e := encoded ((a :: xs).reverse ++ rs ++ q)
    let r := chosenRadius T
    Manacher.PalAt e (T.length-r) r ∧
      ∀ r', 2*r'+1 ≤ T.length → Manacher.PalAt e (T.length-r') r' → r' ≤ r := by
  intro T e r
  have hne : T ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [stream_length] at this
    cases g <;> simp at this
  obtain ⟨hr,hp⟩ := chosen_spec T hne
  refine ⟨(stream_prefix_palindrome a xs rs q g r hr).1 hp,?_⟩
  intro r' hr' hp'
  exact chosen_greatest T r' hr' ((stream_prefix_palindrome a xs rs q g r' hr').2 hp')

#print axioms choose_rewind

/-- The fallback window is a prefix of the stream, so its palindromic prefixes
are the stream's, up to the window length. -/
theorem window_take (T : List (Fin 3)) (ℓ b : ℕ) (hb : b ≤ ℓ+1) :
    (T.take (ℓ+1)).take b = T.take b := by
  rw [List.take_take,Nat.min_eq_left hb]

/-- `stepChoose` on the fallback window: the chosen odd mark gives a palindrome
of the encoded scan word centred `r` places below the right head, and no
longer odd palindrome inside the window ends at the head. -/
theorem choose_rewind_window (a : Fin 2) (xs rs q : List (Fin 2)) (g : Bool) (ℓ : ℕ) :
    let T := GalilScaffoldPlace.stream ⟨a :: xs,g⟩
    let w := T.take (ℓ+1)
    let e := encoded ((a :: xs).reverse ++ rs ++ q)
    let r := chosenRadius w
    2*r+1 ≤ w.length ∧ IsPal (w.take (2*r+1)) ∧
      Manacher.PalAt e (T.length-r) r ∧
      ∀ r', 2*r'+1 ≤ w.length → Manacher.PalAt e (T.length-r') r' → r' ≤ r := by
  intro T w e r
  have hne : T ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [stream_length] at this
    cases g <;> simp at this
  have hwne : w ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [w,List.length_take,List.length_nil] at this
    have := List.length_pos_of_ne_nil hne
    omega
  obtain ⟨hr,hp⟩ := chosen_spec w hwne
  have hTl : (GalilScaffoldPlace.stream ⟨a :: xs,g⟩).length = T.length := rfl
  have hwT : w.length ≤ T.length := by simp [w,List.length_take]
  have hwl : w.length ≤ ℓ+1 := by simp [w,List.length_take]
  refine ⟨hr,hp,?_,?_⟩
  · rw [window_take T ℓ _ (by omega)] at hp
    exact (stream_prefix_palindrome a xs rs q g r (by omega)).1 hp
  · intro r' hr' hp'
    have := (stream_prefix_palindrome a xs rs q g r' (by omega)).2 hp'
    rw [← window_take T ℓ _ (by omega)] at this
    exact chosen_greatest w r' hr' this

/-- The actual fpp marks on the fallback window, and the choice they induce.
`marked_fpp` runs the exported nine-tape program on the window loaded in its
SOURCE tape; the chosen odd mark is set, and it is the longest odd palindrome
of the encoded scan word ending at the right head within the window.
The bridge from the scaffold's zipper SOURCE (`fallback_window`) to the
function-tape `GalilFppPrepareInit.initial` remains a separate refinement. -/
theorem fallback_fpp_choose (a : Fin 2) (xs rs q : List (Fin 2)) (g : Bool) (ℓ : ℕ) :
    let T := GalilScaffoldPlace.stream ⟨a :: xs,g⟩
    let w := T.take (ℓ+1)
    let e := encoded ((a :: xs).reverse ++ rs ++ q)
    let r := chosenRadius w
    ∃ y qs, GalilFppWide.Completed GalilFppMarkedCode.code
        (GalilFppPrepareInit.initial w) qs y ∧
      y.pos 8 = 0 ∧ y.pc = 0 ∧
      (∀ b, y.tape 8 b = 8 ↔ 0 < b ∧ b ≤ w.length ∧ IsPal (w.take b)) ∧
      y.tape 8 (2*r+1) = 8 ∧
      Manacher.PalAt e (T.length-r) r ∧
      ∀ r', 2*r'+1 ≤ w.length → Manacher.PalAt e (T.length-r') r' → r' ≤ r := by
  intro T w e r
  obtain ⟨y,qs,hrun,hpos,hpc,_,_,hmarks⟩ := GalilFppPrepareLayout.marked_fpp w
  obtain ⟨hr,hp,hpal,hmax⟩ := choose_rewind_window a xs rs q g ℓ
  refine ⟨y,qs,hrun,hpos,hpc,hmarks,?_,hpal,hmax⟩
  exact (hmarks _).2 ⟨by omega,hr,hp⟩

#print axioms fallback_fpp_choose

/-! ## The fpp program on the scaffold's zipper tapes

`fallback_window` leaves the window in the zipper SOURCE tape as
`bounded (w.map symbol)`. The exported nine-tape program is verified on
function tapes; `denote` and `realize_completed` carry that execution back to
the zipper configuration the scaffold actually holds. -/

/-- The fpp program's entry configuration on zipper tapes: SOURCE holds the
window behind LEFT, every other tape is fresh. -/
def fppInitial (w : List (Fin 3)) : GalilScaffoldProgram.Config 9 where
  pc := 320
  tapes := fun t => if t = 7 then GalilScaffoldPreload.bounded (w.map GalilFppPreparation.symbol)
    else GalilScaffoldTape.reset

theorem fppInitial_denote (w : List (Fin 3)) :
    GalilScaffoldProgram.denote (fppInitial w) = GalilFppPrepareInit.initial w := by
  apply GalilScaffoldProgram.wide_ext
  · rfl
  · funext t
    by_cases h7 : t = 7
    · subst t
      simpa [GalilScaffoldProgram.denote,fppInitial,GalilFppPrepareInit.initial] using
        GalilScaffoldPreload.bounded_source w
    · simp [GalilScaffoldProgram.denote,fppInitial,GalilFppPrepareInit.initial,h7,
        GalilScaffoldTape.reset_blank]
  · funext t
    by_cases h7 : t = 7
    · subst t; rfl
    · simp [GalilScaffoldProgram.denote,fppInitial,GalilFppPrepareInit.initial,h7,
        GalilScaffoldTape.reset_head]

/-- The fpp program runs on the scaffold's zipper tapes from the copied window
and halts with the palindromic-prefix marks, within the exported step bound. -/
theorem fpp_realized (w : List (Fin 3)) :
    ∃ v qs, GalilScaffoldProgram.Completed GalilFppMarkedCode.code (fppInitial w) qs v ∧
      (GalilScaffoldProgram.denote v).pc = 0 ∧ (GalilScaffoldProgram.denote v).pos 8 = 0 ∧
      (GalilScaffoldProgram.denote v).pos 7 = 0 ∧
      (GalilScaffoldProgram.denote v).tape 7 = GalilFppPrepareCopy.source w ∧
      (GalilScaffoldProgram.denote v).tape 8 = GalilFppMarkedLayout.marks w ∧
      qs.length ≤ 1584*w.length+830 := by
  obtain ⟨y,qs,hrun,hpc,hpos8,hpos7,h7,h8,hcost⟩ := GalilFppMarkedCost.marked_fpp_exact_cost w
  obtain ⟨v,hv,hd⟩ := GalilScaffoldProgram.realize_completed hrun (fppInitial w) (fppInitial_denote w)
  refine ⟨v,qs,hv,?_,?_,?_,?_,?_,hcost⟩ <;> rw [hd] <;> assumption

#print axioms fpp_realized

/-- Scala `stepFpp` runs the program in quanta of instruction opportunities;
once enough opportunities have been granted the fpp program has halted on the
scaffold's tapes with the marks in place (the fpp analogue of
`GalilScaffoldDpCost.scheduled_correct`). -/
theorem fpp_scheduled (w : List (Fin 3)) :
    ∃ v, (GalilScaffoldProgram.denote v).pc = 0 ∧ (GalilScaffoldProgram.denote v).pos 8 = 0 ∧
      (GalilScaffoldProgram.denote v).tape 7 = GalilFppPrepareCopy.source w ∧
      (GalilScaffoldProgram.denote v).tape 8 = GalilFppMarkedLayout.marks w ∧
      ∀ bs : List Bool, 1584*w.length+830 ≤ bs.count true →
        GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w,false⟩ bs ⟨v,true⟩ := by
  obtain ⟨v,qs,hv,hpc,hpos8,_,h7,h8,hcost⟩ := fpp_realized w
  refine ⟨v,hpc,hpos8,h7,h8,?_⟩
  intro bs hb
  exact GalilScaffoldControl.scheduled_completed hv bs (hcost.trans hb)

#print axioms fpp_scheduled

/-! ## The fallback controller: copy, home, then the program

Scala `beginFallback` resets the fpp program, points the walker at R, sets
`remaining = length+1`, writes LEFT on SOURCE and moves right, and enters
`Copy`. `stepCopy`/`stepHome` then copy the window and home SOURCE, and
`stepHome` starts the program. This is the fpp counterpart of
`GalilScaffoldPrepareControl` on nine tapes, without the LOWER phases. -/

namespace FppControl

inductive Mode where
  | copy | home | run
  deriving DecidableEq

structure State where
  mode : Mode
  program : GalilScaffoldControl.Machine 9
  work : GalilScaffoldCounter.Counter
  walker : GalilScaffoldPlace.Place
  finalStage : Bool

def tape (x : State) (i : Fin 9) (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    GalilScaffoldControl.Machine 9 :=
  {x.program with config := GalilScaffoldLoading.put x.program.config i (f (x.program.config.tapes i))}

/-- Decoded `beginFallback`: fresh program, walker on the right place,
`remaining = length+1`, LEFT written and passed on SOURCE, mode `Copy`. -/
def beginFallback (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) : State :=
  let r := GalilScaffoldControl.reset 320 old
  { mode := .copy
    program := {r with config := GalilScaffoldLoading.put r.config 7 (GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4))}
    work := GalilScaffoldCounter.inc length
    walker := p
    finalStage := false }

/-- One enabled controller tick in Scala dispatch order. -/
inductive Tick : Bool → State → State → Prop
  | idle (x : State) : Tick false x x
  | copyBit (x : State) (a : Fin 3) (hm : x.mode = .copy)
      (ha : GalilScaffoldPlace.read x.walker = some a)
      (hw : GalilScaffoldCounter.zero x.work = false) :
      Tick true x {x with program := tape x 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec x.work, walker := GalilScaffoldPlace.left x.walker}
  | copyEnd (x : State) (hm : x.mode = .copy)
      (he : GalilScaffoldPlace.read x.walker = none ∨ GalilScaffoldCounter.zero x.work = true) :
      Tick true x {x with program := tape x 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read x.walker).isNone}
  | sourceLeft (x : State) (hm : x.mode = .home)
      (hf : (x.program.config.tapes 7).focus ≠ 4) (hl : (x.program.config.tapes 7).left ≠ []) :
      Tick true x {x with program := tape x 7 GalilScaffoldTape.moveLeft}
  | startRun (x : State) (hm : x.mode = .home)
      (hf : (x.program.config.tapes 7).focus = 4) :
      Tick true x {x with program := GalilScaffoldControl.start 320 x.program, mode := .run}

inductive Run : State → List Bool → State → Prop
  | nil (x : State) : Run x [] x
  | cons (x y z : State) (b : Bool) (bs : List Bool)
      (ht : Tick b x y) (hr : Run y bs z) : Run x (b :: bs) z

theorem run_append {x y z : State} {bs cs : List Bool} (hb : Run x bs y) (hc : Run y cs z) :
    Run x (bs ++ cs) z := by
  induction hb with
  | nil x => exact hc
  | cons x y _ b bs ht _ ih => exact Run.cons _ _ _ _ _ ht (ih hc)

theorem source_copy {x y : GalilScaffoldPlace.Cursor} {n : ℕ} {final : Bool}
    (hr : GalilScaffoldPlace.Copy x n y final) (s : State) (hm : s.mode = .copy)
    (hw : s.work = GalilScaffoldCounter.ofNat x.work) (hp : s.walker = x.place)
    (ht : s.program.config.tapes 7 = x.tape) :
    ∃ t, Run s (List.replicate n true) t ∧ t.mode = .home ∧
      t.work = GalilScaffoldCounter.ofNat y.work ∧ t.walker = y.place ∧
      t.program.config.tapes 7 = y.tape ∧ t.finalStage = final ∧
      t.program.config.pc = s.program.config.pc ∧ t.program.done = s.program.done ∧
      (∀ i : Fin 9, i ≠ 7 → t.program.config.tapes i = s.program.config.tapes i) := by
  induction hr generalizing s with
  | stop x he =>
    let t : State := {s with program := tape s 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read s.walker).isNone}
    have hs : Tick true s t := .copyEnd s hm (by
      rcases he with he | he
      · exact Or.inl (by simpa [hp] using he)
      · right; simp [hw,he,GalilScaffoldCounter.ofNat,GalilScaffoldCounter.zero])
    refine ⟨t,.cons s t t true [] hs (.nil t),rfl,hw,hp,?_,?_,rfl,rfl,?_⟩
    · simp [t,tape,GalilScaffoldLoading.put,ht]
    · simp [t,hp]
    · intro i hi; simp [t,tape,GalilScaffoldLoading.put,hi]
  | next p k tape0 a ha n y final hr ih =>
    let u : State := {s with program := tape s 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec s.work, walker := GalilScaffoldPlace.left s.walker}
    have hs : Tick true s u := .copyBit s a hm (by simpa [hp] using ha)
      (by simp [hw,GalilScaffoldCounter.zero,GalilScaffoldCounter.ofNat,List.replicate_succ])
    obtain ⟨t,hrt,hmode,hwork,hplace,htape,hfinal,hpc,hdone,hother⟩ := ih u hm
      (by simp [u,hw,GalilScaffoldCounter.dec_ofNat_succ])
      (by simp [u,hp]) (by simp [u,tape,GalilScaffoldLoading.put,ht])
    refine ⟨t,?_,hmode,hwork,hplace,htape,hfinal,hpc,hdone,?_⟩
    · simpa [List.replicate_succ] using Run.cons s u t true _ hs hrt
    · intro i hi
      rw [hother i hi]
      simp [u,tape,GalilScaffoldLoading.put,hi]

theorem source_home {x y : GalilScaffoldTape.Tape} {n : ℕ} (hr : GalilScaffoldLower.Rewind x n y)
    (s : State) (hm : s.mode = .home) (ht : s.program.config.tapes 7 = x) :
    ∃ t, Run s (List.replicate n true) t ∧ t.mode = .run ∧
      t.program.config.tapes 7 = y ∧ t.program.config.pc = 320 ∧ t.program.done = false ∧
      t.finalStage = s.finalStage ∧
      (∀ i : Fin 9, i ≠ 7 → t.program.config.tapes i = s.program.config.tapes i) := by
  induction hr generalizing s with
  | done x hf =>
    let t : State := {s with program := GalilScaffoldControl.start 320 s.program, mode := .run}
    have hs : Tick true s t := .startRun s hm (by simpa [ht] using hf)
    exact ⟨t,.cons s t t true [] hs (.nil t),rfl,ht,rfl,rfl,rfl,fun _ _ => rfl⟩
  | left x y n hf hl hr ih =>
    let u : State := {s with program := tape s 7 GalilScaffoldTape.moveLeft}
    have hs : Tick true s u := .sourceLeft s hm (by simpa [ht] using hf) (by simpa [ht] using hl)
    obtain ⟨t,hrt,hmode,htape,hpc,hdone,hfinal,hother⟩ := ih u hm
      (by simp [u,tape,GalilScaffoldLoading.put,ht])
    refine ⟨t,?_,hmode,htape,hpc,hdone,hfinal,?_⟩
    · simpa [List.replicate_succ] using Run.cons s u t true _ hs hrt
    · intro i hi
      rw [hother i hi]
      simp [u,tape,GalilScaffoldLoading.put,hi]

/-- From `beginFallback`, copying the window and homing SOURCE reaches `run`
mode with exactly the fpp program's zipper entry configuration, not yet halted:
the start machine of `fpp_scheduled`. -/
theorem fallback_prepared (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ) :
    let w := (GalilScaffoldPlace.stream p).take (ℓ+1)
    ∃ t, Run (beginFallback old p length) (List.replicate (2*w.length+3) true) t ∧
      t.mode = .run ∧ t.program = ⟨fppInitial w,false⟩ ∧
      (t.finalStage = true ↔ (GalilScaffoldPlace.stream p).length ≤ ℓ+1) := by
  intro w
  obtain ⟨y,final,hcopy,hrewind,hfinal⟩ := GalilScaffoldSourceReady.place_ready p ℓ
  have hlen : GalilScaffoldCounter.inc length = GalilScaffoldCounter.ofNat (ℓ+1) := by
    rw [GalilScaffoldChainCatch.canonical_nat length hc ℓ hv,GalilScaffoldCounter.inc_ofNat]
  obtain ⟨u,hru,hmode,_,_,htape,hfin,hpc,hdone,hother⟩ :=
    source_copy hcopy (beginFallback old p length) rfl hlen rfl
      (by simp [beginFallback,GalilScaffoldLoading.put])
  obtain ⟨t,hrt,hmode',htape',hpc',hdone',hfinal',hother'⟩ := source_home hrewind u hmode htape
  refine ⟨t,?_,hmode',?_,by rw [hfinal',hfin]; exact hfinal⟩
  · have := run_append hru hrt
    rwa [← List.replicate_add,show w.length+1+(w.length+2) = 2*w.length+3 by omega] at this
  · rcases t with ⟨_,⟨⟨pc,tapes⟩,done⟩,_,_,_⟩
    simp only at hpc' hdone' htape' hother'
    subst hpc' hdone'
    dsimp only
    congr 1
    apply GalilScaffoldLoading.config_ext
    · rfl
    · funext i
      by_cases h7 : i = 7
      · subst h7
        show tapes 7 = _
        dsimp only [fppInitial]
        rw [if_pos rfl]
        exact htape'
      · show tapes i = _
        rw [hother' i h7,hother i h7]
        simp [fppInitial,beginFallback,GalilScaffoldLoading.put,GalilScaffoldControl.reset,h7]

#print axioms fallback_prepared

end FppControl

theorem marks_cell (w : List (Fin 3)) (i : ℕ) :
    GalilFppMarkedLayout.marks w i = 8 ↔ 0 < i ∧ i ≤ w.length ∧ IsPal (w.take i) := by
  unfold GalilFppMarkedLayout.marks IsPal
  by_cases h0 : i = 0
  · subst h0; simp
  · by_cases hl : i ≤ w.length
    · by_cases hp : (w.take i).reverse = w.take i
      · simp [h0,hl,hp]; omega
      · simp [h0,hl,hp]
    · by_cases he : i = w.length+1
      · simp [h0,hl,he]
      · simp [h0,hl,he]

/-- The fallback branch, end to end on the actual right head: the decoded
`beginFallback` controller copies the window and homes SOURCE, reaching the
fpp program's entry machine; granted enough instruction opportunities the
program halts with the palindromic-prefix marks; the chosen odd mark is set,
and it names the longest odd palindrome of the encoded scan word ending at
the right head within the window. Rewind's destination centre is
`position s.right - r`. -/
theorem fallback_end_to_end {raw : List (Fin 2)} (s : OnlyCompareState)
    (hrep : GalilScaffoldInputTrace.Represents s.right.head raw)
    (hfocus : s.right.head.focus ≠ none)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (old : GalilScaffoldControl.Machine 9) :
    ∃ (a : Fin 2) (xs rs q : List (Fin 2)),
      s.right = represent ⟨a :: xs,s.right.gap⟩ (rs.map some) q ∧
      raw = (a :: xs).reverse ++ rs ++ q ∧
      let p : GalilScaffoldPlace.Place := ⟨a :: xs,s.right.gap⟩
      let w := (GalilScaffoldPlace.stream p).take (ℓ+1)
      let r := chosenRadius w
      (∃ t, FppControl.Run (FppControl.beginFallback old p length)
        (List.replicate (2*w.length+3) true) t ∧ t.mode = .run ∧
        t.program = ⟨fppInitial w,false⟩) ∧
      (∃ v, (∀ bs : List Bool, 1584*w.length+830 ≤ bs.count true →
          GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w,false⟩ bs ⟨v,true⟩) ∧
        (GalilScaffoldProgram.denote v).pc = 0 ∧
        (∀ b, (GalilScaffoldProgram.denote v).tape 8 b = 8 ↔
          0 < b ∧ b ≤ w.length ∧ IsPal (w.take b)) ∧
        (GalilScaffoldProgram.denote v).tape 8 (2*r+1) = 8) ∧
      Manacher.PalAt (encoded raw) (position s.right-r) r ∧
      ∀ r', 2*r'+1 ≤ w.length → Manacher.PalAt (encoded raw) (position s.right-r') r' → r' ≤ r := by
  obtain ⟨xs',rs,q,hr,hw⟩ := right_place s.right hrep
  cases xs' with
  | nil =>
    exfalso
    apply hfocus
    rw [hr]
    rfl
  | cons a xs =>
    refine ⟨a,xs,rs,q,hr,hw,?_⟩
    intro p w r
    obtain ⟨t,hrun,hmode,hprog,_⟩ := FppControl.fallback_prepared old p length hc ℓ hv
    obtain ⟨v,hpc,_,_,h8,hsched⟩ := fpp_scheduled w
    obtain ⟨hr2,hp2,hpal,hmax⟩ := choose_rewind_window a xs rs q s.right.gap ℓ
    have hpos : position s.right = (GalilScaffoldPlace.stream p).length := by
      rw [hr,position_represent]
    refine ⟨⟨t,hrun,hmode,hprog⟩,⟨v,hsched,hpc,?_,?_⟩,?_,?_⟩
    · intro b
      rw [h8]
      exact marks_cell w b
    · rw [h8]
      exact (marks_cell w _).2 ⟨by omega,hr2,hp2⟩
    · rw [hw,hpos]
      exact hpal
    · intro r' hr' hp'
      rw [hw,hpos] at hp'
      exact hmax r' hr' hp'

#print axioms fallback_end_to_end

/-! ## Replay after `ReplayStart`

`stepReplayStart` puts L and R on the new centre with radius `0` and remembers
the chosen radius in `replay`. The following compares are guaranteed to match
by the palindrome the fallback established, so the scan invariant is rebuilt
up to that radius without any shift or fallback (Scala asserts as much). -/

theorem signedRead_pos (e : List (Fin 3)) (n : ℕ) (hn : 0 < n) :
    signedRead e n = e[n]? := by
  unfold signedRead
  rw [if_neg (by omega),Int.toNat_natCast]

/-- The replay compares: from the centre head with a known palindrome of
radius `r` strictly inside the arrived word, every one of the `r` outer
compares matches, and the scan invariant of radius `r` is rebuilt. -/
theorem replay_scan {raw : List (Fin 2)} (c r : ℕ) (h : PlaceHead)
    (hrep : GalilScaffoldInputTrace.Represents h.head raw) (hp : h.head.focus ≠ none)
    (hpos : position h = c) (hlow : r+1 ≤ c)
    (hpal : Manacher.PalAt (encoded raw) c r) :
    ∀ k, k ≤ r → ∃ l r', ScanInvariant raw c k l r' ∧ LeftMoves h k l := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨h,h,?_,.stop h⟩
    have := scan_initial raw h hrep hp
    rwa [hpos] at this
  | succ k ih =>
    obtain ⟨l,r',hi,hl⟩ := ih (by omega)
    have hbound := hpal.2.1
    have hcan : canRight r' := canRight_of_bound r' raw hi.rightRep hi.rightPresent
      (by rw [hi.rightPos]; omega)
    have hlpos := left_position l (represented_position _ raw hi.leftRep hi.leftPresent).1
    have hrpos := right_position r' hcan (represented_position _ raw hi.rightRep hi.rightPresent).1
    have hlrep := left_word l raw hi.leftRep hi.leftPresent
    have hrrep := right_word r' raw hi.rightRep hcan
    have hm : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
        GalilScaffoldInputHead.read (right r') := by
      rw [represented_signed_read _ raw hlrep,represented_signed_read _ raw hrrep]
      have e1 : position (GalilScaffoldInputHead.left l) = c-(k+1) := by
        have := hi.leftPos; omega
      have e2 : position (right r') = c+(k+1) := by
        have := hi.rightPos; omega
      rw [e1,e2,signedRead_pos _ _ (by omega),signedRead_pos _ _ (by omega)]
      exact hpal.2.2 (k+1) (by omega)
    refine ⟨GalilScaffoldInputHead.left l,right r',scan_matched hi hcan hm,?_⟩
    exact left_moves_append hl (LeftMoves.next l hi.leftPresent (.stop _))

#print axioms replay_scan

/-- A represented head strictly right of the origin has a symbol in focus. -/
theorem present_of_position {raw : List (Fin 2)} (p : PlaceHead)
    (hrep : GalilScaffoldInputTrace.Represents p.head raw) (hpos : 1 ≤ position p) :
    p.head.focus ≠ none := by
  obtain ⟨xs,rs,q,hh,_⟩ := hrep
  rcases p with ⟨h,gap⟩
  simp only at hh
  subst hh
  cases xs with
  | nil => cases gap <;> simp [position,layout] at hpos
  | cons a xs => simp [layout]

/-- `n` left moves exist from a represented head at position at least `n+1`. -/
theorem left_moves_exists {raw : List (Fin 2)} (n : ℕ) :
    ∀ p : PlaceHead, GalilScaffoldInputTrace.Represents p.head raw → n+1 ≤ position p →
      ∃ q, LeftMoves p n q ∧ GalilScaffoldInputTrace.Represents q.head raw ∧
        position q+n = position p := by
  induction n with
  | zero =>
    intro p hrep _
    exact ⟨p,.stop p,hrep,by simp⟩
  | succ n ih =>
    intro p hrep hpos
    have hp : p.head.focus ≠ none := present_of_position p hrep (by omega)
    have hlrep := left_word p raw hrep hp
    have hlpos := left_position p (represented_position _ raw hrep hp).1
    obtain ⟨q,hq,hqrep,hqpos⟩ := ih (GalilScaffoldInputHead.left p) hlrep (by omega)
    exact ⟨q,.next p hp hq,hqrep,by omega⟩

/-- Fallback, choose, rewind and replay on the actual right head: the centre
head `r` places below R exists, and the replay rebuilds the scan invariant of
radius `r` at that centre — the longest odd palindrome ending at R within
the fallback window. -/
theorem fallback_replay {raw : List (Fin 2)} (s : OnlyCompareState)
    (hrep : GalilScaffoldInputTrace.Represents s.right.head raw)
    (hfocus : s.right.head.focus ≠ none)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ) :
    ∃ (a : Fin 2) (xs rs q : List (Fin 2)),
      s.right = represent ⟨a :: xs,s.right.gap⟩ (rs.map some) q ∧
      raw = (a :: xs).reverse ++ rs ++ q ∧
      let w := (GalilScaffoldPlace.stream ⟨a :: xs,s.right.gap⟩).take (ℓ+1)
      let r := chosenRadius w
      let c := position s.right-r
      Manacher.PalAt (encoded raw) c r ∧
      (∀ r', 2*r'+1 ≤ w.length → Manacher.PalAt (encoded raw) (position s.right-r') r' → r' ≤ r) ∧
      ∃ h, LeftMoves s.right r h ∧ GalilScaffoldInputTrace.Represents h.head raw ∧
        h.head.focus ≠ none ∧ position h = c ∧
        ∀ k, k ≤ r → ∃ l r', ScanInvariant raw c k l r' ∧ LeftMoves h k l := by
  obtain ⟨a,xs,rs,q,hr,hw,_,_,hpal,hmax⟩ :=
    fallback_end_to_end s hrep hfocus length hc ℓ hv (GalilScaffoldControl.reset 320 ⟨⟨0,fun _ => GalilScaffoldTape.reset⟩,true⟩)
  refine ⟨a,xs,rs,q,hr,hw,?_⟩
  intro w r c
  have hT : 0 < (GalilScaffoldPlace.stream ⟨a :: xs,s.right.gap⟩).length := by
    rw [stream_length]; cases s.right.gap <;> simp
  have hwne : w ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [w,List.length_take]
    omega
  obtain ⟨hr2,_⟩ := chosen_spec w hwne
  have hwT : w.length ≤ (GalilScaffoldPlace.stream ⟨a :: xs,s.right.gap⟩).length := by
    simp only [w,List.length_take]
    omega
  have hpos : position s.right = (GalilScaffoldPlace.stream ⟨a :: xs,s.right.gap⟩).length := by
    have := position_represent a xs s.right.gap (rs.map some) q
    rw [← hr] at this
    exact this
  obtain ⟨h,hmoves,hhrep,hhpos⟩ := left_moves_exists r s.right hrep (by omega)
  have hcpos : position h = c := by omega
  refine ⟨hpal,hmax,h,hmoves,hhrep,present_of_position h hhrep (by omega),hcpos,?_⟩
  exact replay_scan c r h hhrep (present_of_position h hhrep (by omega)) hcpos (by omega) hpal

#print axioms fallback_replay

/-! ## From a found search candidate to the fresh watch entry

Scala `Chain.start` writes the centre symbol as the front mark, copies the
walker and verifier from C and aliases `lag`/`margin` to the radius;
`stepCopy` consumes the unary DP answer while copying C-1, C-2, … onto the
period tape; the last copied symbol is tail-marked and `stepBack` returns to
the front mark, entering `Watch`. The period tape then is exactly
`(ready c ys b).period` with `ys ++ [b]` the copied semiperiod. -/

theorem fill_snoc_shape (ls : List GalilScaffoldChainPeriod.Token)
    (f : GalilScaffoldChainPeriod.Token) (ys : List (Fin 3)) (b : Fin 3) :
    GalilScaffoldChainPeriod.fill ⟨ls,f,[]⟩ (ys ++ [b]) =
      ⟨(ys.map GalilScaffoldChainPeriod.Token.plain).reverse ++ f :: ls,.plain b,[]⟩ := by
  induction ys generalizing ls f with
  | nil => rfl
  | cons a ys ih =>
    show GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.put ⟨ls,f,[]⟩ a) (ys ++ [b]) = _
    have hput : GalilScaffoldChainPeriod.put ⟨ls,f,[]⟩ a = ⟨f :: ls,.plain a,[]⟩ := rfl
    rw [hput,ih]
    simp [List.reverse_cons,List.append_assoc]

theorem copy_walk_period {t : GalilScaffoldTape.Tape} {c : GalilScaffoldCounter.Counter}
    {p : GalilScaffoldPlace.Place} {n : ℕ} {u : GalilScaffoldTape.Tape}
    {d : GalilScaffoldCounter.Counter} {q : GalilScaffoldPlace.Place} {xs : List (Fin 3)}
    (hr : GalilScaffoldChainAnswer.CopyWalk t c p n u d q xs) :
    ∀ v : GalilScaffoldChainPeriod.Tape,
      GalilScaffoldChainPeriod.Copy t c p v n u d q (GalilScaffoldChainPeriod.fill v xs) := by
  induction hr with
  | stop t c p => intro v; exact .stop t c p v
  | next a one legal present _ ih =>
    intro v
    exact .next a one legal present (ih (GalilScaffoldChainPeriod.put v a))

/-- The fresh watch entry from a found search: the DP candidate `h`, the copied
semiperiod `ys ++ [b]` (the `h` places left of the centre), the period copy
and the back walk ending on `(ready c ys b).period`, and the paced credits of
Scala's copy/back with any outer matched events. -/
theorem fresh_watch_entry {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place) (c : Fin 3)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3) (u : GalilScaffoldTape.Tape)
      (q : GalilScaffoldPlace.Place),
      GalilDpCorrect.Candidate w lower h ∧ ys.length+1 = h ∧
      ys ++ [b] = ((GalilScaffoldPlace.stream p).drop 1).take h ∧
      GalilScaffoldPlace.stream q = (GalilScaffoldPlace.stream p).drop h ∧
      GalilScaffoldChainPeriod.Copy (y.config.tapes 11) GalilScaffoldCounter.reset p
        (GalilScaffoldChainPeriod.start c) h u (GalilScaffoldCounter.ofNat h) q
        ⟨(ys.map GalilScaffoldChainPeriod.Token.plain).reverse ++ [.first c],.plain b,[]⟩ ∧
      GalilScaffoldChainPeriod.Back
        ⟨(ys.map GalilScaffoldChainPeriod.Token.plain).reverse ++ [.first c],.last b,[]⟩
        (h+1) (GalilScaffoldChainConsume.ready c ys b).period ∧
      ∀ (radius : GalilScaffoldCounter.Counter), GalilScaffoldCounter.Canonical radius →
        0 < GalilScaffoldCounter.value radius →
        ∀ (sm dm : Bool) (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∃ copied final,
          GalilScaffoldChainCredits.PacedCopy
            ⟨y.config.tapes 11,GalilScaffoldCounter.reset,p,GalilScaffoldChainPeriod.start c,
              GalilScaffoldChainCredits.step (GalilScaffoldChainCredits.start radius) (false,sm)⟩
            bs ⟨u,GalilScaffoldCounter.ofNat h,q,
              ⟨(ys.map GalilScaffoldChainPeriod.Token.plain).reverse ++ [.first c],.plain b,[]⟩,
              copied⟩ ∧
          GalilScaffoldChainCredits.PacedBack
            ⟨(ys.map GalilScaffoldChainPeriod.Token.plain).reverse ++ [.first c],.last b,[]⟩
            (GalilScaffoldChainCredits.step copied (false,dm)) cs
            (GalilScaffoldChainConsume.ready c ys b).period final ∧
          final = GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
            (GalilScaffoldChainCredits.prepEvents sm dm bs cs) ∧
          GalilScaffoldCounter.Canonical final.margin ∧
          GalilScaffoldCounter.Canonical final.lag ∧
          GalilScaffoldCounter.zero final.lag = false := by
  obtain ⟨h,u,q,xs,hcand,hwalk,_,_,hxs,hq⟩ :=
    GalilScaffoldChainAnswer.found_copy_walk p hw hr hs ht hv
  have hpos : 0 < h := by have := hcand.1; omega
  have hlen : xs.length = h := by
    rw [hxs,List.length_take,List.length_drop]
    have h1 := hcand.2.1
    have h2 : w.length ≤ (GalilScaffoldPlace.stream p).length := by
      rw [hw]; simp [List.length_take]
    omega
  have hne : xs ≠ [] := by
    intro h0; rw [h0] at hlen; simp at hlen; omega
  obtain ⟨ys,b,hsplit⟩ : ∃ ys b, xs = ys ++ [b] :=
    ⟨xs.dropLast,xs.getLast hne,(List.dropLast_append_getLast hne).symm⟩
  have hys : ys.length+1 = h := by
    have := congrArg List.length hsplit
    simp at this; omega
  have hcopy := copy_walk_period hwalk (GalilScaffoldChainPeriod.start c)
  rw [hsplit,show GalilScaffoldChainPeriod.start c = ⟨[],.first c,[]⟩ from rfl,
    fill_snoc_shape] at hcopy
  have hplain : ∀ x ∈ (ys.map GalilScaffoldChainPeriod.Token.plain).reverse,
      GalilScaffoldChainPeriod.isFirst x = false := by
    intro x hx
    simp only [List.mem_reverse,List.mem_map] at hx
    obtain ⟨_,_,rfl⟩ := hx
    rfl
  have hback := GalilScaffoldChainPeriod.back_exact
    ((ys.map GalilScaffoldChainPeriod.Token.plain).reverse) c (.last b) [] rfl hplain
  simp only [List.length_reverse,List.length_map,List.reverse_reverse] at hback
  have hback' : GalilScaffoldChainPeriod.Back
      ⟨(ys.map GalilScaffoldChainPeriod.Token.plain).reverse ++ [.first c],.last b,[]⟩
      (h+1) (GalilScaffoldChainConsume.ready c ys b).period := by
    have e : ys.length+2 = h+1 := by omega
    rw [e] at hback
    exact hback
  refine ⟨h,ys,b,u,q,hcand,hys,hsplit ▸ hxs,hq,hcopy,hback',?_⟩
  intro radius hc hp sm dm bs cs hb hcs
  have hb' : bs.length = h := hb
  obtain ⟨copied,final,hpc,hpb,hfinal,hm,hl,hz⟩ :=
    GalilScaffoldChainCredits.prepare_paced hcopy b
      (by
        show GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write _ (.last b)) (h+1) _
        exact hback')
      radius hc hp sm dm bs cs hb' hcs
  exact ⟨copied,final,hpc,hpb,hfinal,hm,hl,hz⟩

#print axioms fresh_watch_entry

/-- The decoded watch state right after Scala `stepBack` enters `Watch`: the
verifier still on the centre head, the ready control with the copied
semiperiod, and the paced credits as lag and margin. -/
def watchStart (cen : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (final : GalilScaffoldChainCredits.State) : GalilScaffoldChainWatch.State :=
  ⟨⟨cen,GalilScaffoldChainConsume.ready c ys b⟩,final.lag,final.margin⟩

/-- From a found search to the restart conditions after the fresh shift and
any number of re-shift rounds. The chain-side premises of
`fresh_rounds_restart` — ready control, copied semiperiod, DP candidate,
paced lag/margin, centre position — are supplied by `fresh_watch_entry`;
what remains external is the actual watch run and the scan state at the
fresh mismatch. -/
theorem found_rounds_restart {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (span lower : ℕ)
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config))
    (radius : GalilScaffoldCounter.Counter) (hrc : GalilScaffoldCounter.Canonical radius)
    (hrp : 0 < GalilScaffoldCounter.value radius) (sm dm : Bool) :
    ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h ∧
      ys.length+1 = h ∧ ys ++ [b] = ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).drop 1).take h ∧
      ∀ (copyMatches backMatches : List Bool), copyMatches.length = h → backMatches.length = h+1 →
      let final := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches)
      let s0 := watchStart cen c ys b final
      ∀ {t' : GalilScaffoldChainWatch.State} {bs : List Bool}
        (hrun : GalilScaffoldChainWatch.Run s0 bs t') (hphase : t'.machine.control.phase = 4)
        (initialRadius scanRadius : ℕ)
        (hlag : GalilScaffoldCounter.value s0.lag = initialRadius)
        (hzero : GalilScaffoldCounter.zero t'.lag = true)
        (hcount : initialRadius+bs.count true = scanRadius)
        (l outer : PlaceHead)
        (hi : ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (position cen) scanRadius l outer)
        (hcan : canRight outer) (predicted : Fin 3)
        (hpred : GalilScaffoldChainConsume.symbol t'.machine.control.period.focus = some predicted)
        (hread : GalilScaffoldInputHead.read (right outer) = some predicted)
        (radiusCounter lengthCounter : GalilScaffoldCounter.Counter)
        (hcounter : GalilScaffoldCounter.value radiusCounter = (scanRadius : ℤ)+1)
        (hrcanon : GalilScaffoldCounter.Canonical radiusCounter)
        (hlcanon : GalilScaffoldCounter.Canonical lengthCounter)
        (hmismatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
          GalilScaffoldInputHead.read (right outer)),
      ∃ endpoint watchEnd cycleEnd,
        ShiftRun ⟨cen,GalilScaffoldInputHead.left l,
          GalilScaffoldCounter.ofNat h,radiusCounter,lengthCounter⟩ h endpoint ∧
        ChainShiftRun ⟨cen,GalilScaffoldInputHead.left l,
          GalilScaffoldCounter.ofNat h,radiusCounter,lengthCounter⟩
          (GalilScaffoldChainWatch.immediate t') GalilScaffoldCounter.reset h
          endpoint watchEnd cycleEnd ∧
        ∀ (m n : ℕ) (s' final' : OnlyCompareState),
          CompareRounds h
            ⟨endpoint.center,endpoint.left,right outer,watchEnd,cycleEnd,endpoint.radius⟩ m s' →
          OnlyMatchedRun s' n final' →
          GalilScaffoldInputHead.read s'.center ≠ none →
          GalilScaffoldCounter.singlePositive final'.cycle = true → canRight final'.right →
          GalilScaffoldInputHead.read (GalilScaffoldInputHead.left final'.left) =
            GalilScaffoldInputHead.read (right final'.right) →
          let endState := onlyCompareNext final'
          let center := position cen+(m+1)*h
          let radius' := scanRadius+1+m*h-h
          ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) center (radius'+n+1)
              endState.left endState.right ∧
            endState.watch.machine.control.broken = true ∧
            GalilScaffoldCounter.negative endState.watch.margin = false ∧
            GalilScaffoldCounter.positive endState.watch.machine.control.last = true ∧
            GalilScaffoldCounter.zero endState.watch.lag = true ∧
            GalilScaffoldInputHead.read endState.center ≠ none ∧
            RadiusRep endState.radius (radius'+n+1) ∧
            GalilScaffoldCounter.negative endState.radius = false ∧
            (GalilScaffoldSearchFinish.begin endState.watch.machine.control.last
              endState.radius).work = endState.watch.machine.control.last ∧
            GalilScaffoldCounter.Canonical endState.watch.machine.control.last := by
  obtain ⟨h,ys,b,u,q',hcand,hys,hsplit,_,_,_,hpaced⟩ :=
    fresh_watch_entry ⟨a :: ls,gap⟩ c rfl hr hs ht hv
  refine ⟨h,ys,b,hcand,hys,hsplit,?_⟩
  intro copyMatches backMatches hcl hbl final s0
  obtain ⟨_,_,_,_,hfinal,_,_,_⟩ := hpaced radius hrc hrp sm dm copyMatches backMatches hcl hbl
  intro t' bs hrun hphase initialRadius scanRadius hlag hzero hcount l outer hi hcan predicted
    hpred hread radiusCounter lengthCounter hcounter hrcanon hlcanon hmismatch
  have hh : GalilScaffoldInputTrace.Represents s0.machine.verifier.head
      ((a :: ls).reverse ++ (rs ++ q)) := by
    show GalilScaffoldInputTrace.Represents cen.head _
    rw [hcen]
    exact ⟨a :: ls,rs,q,rfl,by simp [List.append_assoc]⟩
  have hp : s0.machine.verifier.head.focus ≠ none := by
    show cen.head.focus ≠ none
    rw [hcen]; simp [represent,layout]
  have hstart : position s0.machine.verifier = if gap then 2*(ls.length+1) else 2*(ls.length+1)-1 := by
    show position cen = _
    rw [hcen,position_represent,stream_length]
    cases gap <;> simp <;> omega
  have hpos : position s0.machine.verifier = position cen := rfl
  have hcand' : GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1))
      lower (ys.length+1) := by rw [hys]; exact hcand
  have hcl' : copyMatches.length = ys.length+1 := by rw [hcl,hys]
  have hi' : ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (position s0.machine.verifier)
      scanRadius l outer := by rw [hpos]; exact hi
  have := fresh_rounds_restart hrun a ls (rs ++ q) gap _ (span+1) lower scanRadius c b ys rfl hcand'
    hh hp rfl hstart l outer hi' hphase initialRadius hlag hzero hcount hcan predicted hpred hread
    radiusCounter lengthCounter hcounter hrcanon hlcanon radius hrc sm dm copyMatches backMatches
    hcl' (by simp [s0,watchStart,final]) (by simp [s0,watchStart,final]) hmismatch
  rw [hys] at this
  exact this

#print axioms found_rounds_restart

/-! ## The candidate window is two bounces

A DP candidate `h` has palindromic prefixes of lengths `2h+1` and `4h+1`, so the
window is `2h`-periodic on its first `4h+1` places and the `4h` places after
the centre read `bounce c b ys ++ bounce c b ys`: exactly what the verifier is
predicted to see during its catch-up. -/

theorem palindrome_prefix_index (w : List (Fin 3)) (L : ℕ) (hL : L+1 ≤ w.length)
    (hp : (w.take (L+1)).reverse = w.take (L+1)) :
    ∀ j, j ≤ L → w[j]? = w[L-j]? := by
  intro j hj
  have := (Manacher.isPal_take_iff_index (x := w) (L := L+1) hL).1 hp j (by omega)
  simpa [Nat.add_sub_cancel] using this

theorem candidate_bounce (w : List (Fin 3)) (lower h : ℕ)
    (hc : GalilDpCorrect.Candidate w lower h) (c : Fin 3) (hc0 : w[0]? = some c)
    (ys : List (Fin 3)) (b : Fin 3) (hys : ys.length+1 = h)
    (hsplit : ys ++ [b] = (w.drop 1).take h) :
    (w.drop 1).take (4*h) =
      GalilScaffoldChainSweep.bounce c b ys ++ GalilScaffoldChainSweep.bounce c b ys := by
  obtain ⟨_,hlen,hp2,hp4⟩ := hc
  have h2 := palindrome_prefix_index w (2*h) (by omega) hp2
  have h4 := palindrome_prefix_index w (4*h) (by omega) hp4
  -- period 2h on [0,4h]
  have hper : ∀ j, 2*h ≤ j → j ≤ 4*h → w[j]? = w[j-2*h]? := by
    intro j hj1 hj2
    rw [h4 j hj2,h2 (4*h-j) (by omega)]
    congr 1; omega
  -- the first semiperiod after the centre
  have hfirst : ∀ i, i < h → w[i+1]? = (ys ++ [b])[i]? := by
    intro i hi
    rw [hsplit,List.getElem?_take,if_pos hi,List.getElem?_drop]
    congr 1; omega
  have hbl : (GalilScaffoldChainSweep.bounce c b ys).length = 2*h := by
    simp [GalilScaffoldChainSweep.bounce]; omega
  -- one bounce, placed at offset 0
  have hbounce : ∀ i, i < 2*h → w[i+1]? = (GalilScaffoldChainSweep.bounce c b ys)[i]? := by
    intro i hi
    unfold GalilScaffoldChainSweep.bounce
    by_cases hlt : i < h
    · rw [List.getElem?_append_left (by simp; omega)]
      exact hfirst i hlt
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append,List.length_singleton]
      have hmirror : w[i+1]? = w[2*h-(i+1)]? := h2 (i+1) (by omega)
      rw [hmirror]
      by_cases hlast : i = 2*h-1
      · subst hlast
        rw [List.getElem?_append_right (by (try simp); omega)]
        simp only [List.length_reverse]
        rw [show 2*h-1-(ys.length+1)-ys.length = 0 by omega,
          show 2*h-(2*h-1+1) = 0 by omega]
        simpa using hc0
      · rw [List.getElem?_append_left (by (try simp); omega),
          List.getElem?_reverse (by omega)]
        have := hfirst (ys.length-1-(i-(ys.length+1))) (by omega)
        rw [List.getElem?_append_left (by (try simp); omega)] at this
        rw [← this]
        congr 1; omega
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 4*h
  · rw [List.getElem?_take,if_pos hi,List.getElem?_drop]
    by_cases hi2 : i < 2*h
    · rw [List.getElem?_append_left (by rw [hbl]; exact hi2),show 1+i = i+1 by omega]
      exact hbounce i hi2
    · rw [List.getElem?_append_right (by rw [hbl]; omega),hbl]
      rw [show 1+i = (i-2*h+1)+2*h by omega,
        hper ((i-2*h+1)+2*h) (by omega) (by omega),Nat.add_sub_cancel]
      exact hbounce (i-2*h) (by omega)
  · rw [List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by simp [hbl]; omega)]

#print axioms candidate_bounce

/-! ## Lifting the verifier's catch-up to the watch controller

`found_window_safe` gives the verifier's unbroken consume run over the first
reads after the centre. Each such consume is a `Good` step of the watch
controller (`Internal.take`) while the lag is positive; with no outer events
in between this is a `Watch.Run` over `false` ticks that lowers the lag by
one per read and leaves the margin alone. -/

theorem good_of_consume (s : GalilScaffoldChainVerifier.State)
    (hp : GalilScaffoldChainVerifier.canRight s.verifier)
    (hc : (consume s).control.broken = false) (lag margin : GalilScaffoldCounter.Counter) :
    GalilScaffoldChainWatch.Good ⟨s,lag,margin⟩ := by
  refine ⟨hp,?_⟩
  cases ht : GalilScaffoldChainConsume.symbol s.control.period.focus with
  | none =>
    exfalso
    simp [consume,GalilScaffoldChainConsume.consume,ht] at hc
  | some a =>
    by_cases hr : GalilScaffoldInputHead.read (right s.verifier) = some a
    · exact ⟨a,rfl,hr⟩
    · exfalso
      simp [consume,GalilScaffoldChainConsume.consume,ht,hr] at hc

theorem verify_watch_run {s t : GalilScaffoldChainVerifier.State} {n : ℕ}
    (hr : GalilScaffoldChainVerifyRun.Run s n t) (ht : t.control.broken = false)
    (k : ℕ) (margin : GalilScaffoldCounter.Counter) :
    GalilScaffoldChainWatch.Run ⟨s,GalilScaffoldCounter.ofNat (n+k),margin⟩
      (List.replicate n false) ⟨t,GalilScaffoldCounter.ofNat k,margin⟩ := by
  induction hr with
  | stop s =>
    rw [Nat.zero_add]
    exact .stop _
  | @next s n' t' hp hr ih =>
    have hc : (consume s).control.broken = false := GalilScaffoldChainCatch.run_unbroken hr ht
    have hg := good_of_consume s hp hc (GalilScaffoldCounter.ofNat (n'+1+k)) margin
    have hpos : GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat (n'+1+k)) = true := by
      rw [GalilScaffoldCounter.positive_iff _ (GalilScaffoldCounter.ofNat_canonical _),
        GalilScaffoldCounter.ofNat_value]
      omega
    have e : GalilScaffoldCounter.dec (GalilScaffoldCounter.ofNat (n'+1+k)) =
        GalilScaffoldCounter.ofNat (n'+k) := by
      rw [show n'+1+k = (n'+k)+1 by omega,GalilScaffoldCounter.dec_ofNat_succ]
    have htick : GalilScaffoldChainWatch.Tick ⟨s,GalilScaffoldCounter.ofNat (n'+1+k),margin⟩ false
        ⟨consume s,GalilScaffoldCounter.ofNat (n'+k),margin⟩ := by
      have h1 : GalilScaffoldChainWatch.Internal ⟨s,GalilScaffoldCounter.ofNat (n'+1+k),margin⟩
          ⟨consume s,GalilScaffoldCounter.ofNat (n'+k),margin⟩ := by
        have := GalilScaffoldChainWatch.Internal.take _ hpos hg
        simpa [GalilScaffoldChainWatch.caught,e] using this
      exact .step h1 (.idle _)
    rw [List.replicate_succ]
    exact .next htick (ih ht)

#print axioms verify_watch_run

/-- Each enabled consume moves a represented verifier one place right. -/
theorem verify_run_position {raw : List (Fin 2)} {s t : GalilScaffoldChainVerifier.State} {n : ℕ}
    (hr : GalilScaffoldChainVerifyRun.Run s n t)
    (hrep : GalilScaffoldInputTrace.Represents s.verifier.head raw)
    (hp : s.verifier.head.focus ≠ none) :
    position t.verifier = position s.verifier+n ∧
      GalilScaffoldInputTrace.Represents t.verifier.head raw ∧ t.verifier.head.focus ≠ none := by
  induction hr with
  | stop s => exact ⟨by simp,hrep,hp⟩
  | @next s n' t' hc hr ih =>
    have hrep' := right_word s.verifier raw hrep hc
    have hp' := right_present s.verifier raw hrep hp hc
    have hpos := right_position s.verifier hc (represented_position _ raw hrep hp).1
    obtain ⟨h1,h2,h3⟩ := ih hrep' hp'
    refine ⟨?_,h2,h3⟩
    change position t'.verifier = _
    rw [h1]
    change position (right s.verifier)+n' = _
    rw [hpos]; omega

/-- The watch controller's catch-up after a found search, with no outer
events: from `watchStart` the verifier consumes `n ≤ min (radius, 4h)` reads
inside the guaranteed window, lowering the lag by `n`, staying unbroken and
represented; once `4h` reads are in, the chain is in phase `4`. Interleaved
outer matches (`true` ticks) and the general lag accounting remain external. -/
theorem found_watch_run
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
      (if gap then 2*(ls.length+1) else 2*(ls.length+1)-1) radius)
    (final : GalilScaffoldChainCredits.State) (v : ℕ)
    (hlag : final.lag = GalilScaffoldCounter.ofNat v) :
    ∃ h c xs b, GalilDpCorrect.Candidate w lower h ∧ h = xs.length+1 ∧
      ∀ n, n ≤ radius → n ≤ 4*h → n ≤ v →
        ∃ z, GalilScaffoldChainWatch.Run
            (watchStart ⟨layout (a :: ls) (rs.map some) qs,gap⟩ c xs b final)
            (List.replicate n false) ⟨z,GalilScaffoldCounter.ofNat (v-n),final.margin⟩ ∧
          z.control.broken = false ∧
          GalilScaffoldInputTrace.Represents z.verifier.head ((a :: ls).reverse ++ rs ++ qs) ∧
          GalilScaffoldCounter.value z.control.distance = n ∧
          (4*h ≤ n → z.control.phase = 4) := by
  obtain ⟨h,c,_,_,xs,b,hcand,hh,_,_,hruns⟩ :=
    found_window_safe a ls rs qs gap hreach hw hr hs ht hv radius hpal
  refine ⟨h,c,xs,b,hcand,hh,?_⟩
  intro n hn1 hn2 hn3
  obtain ⟨z,hrun,hb,hrep⟩ := hruns n hn1 hn2
  have hwatch := verify_watch_run hrun hb (v-n) final.margin
  rw [show n+(v-n) = v by omega] at hwatch
  have hstart : watchStart ⟨layout (a :: ls) (rs.map some) qs,gap⟩ c xs b final =
      ⟨⟨⟨layout (a :: ls) (rs.map some) qs,gap⟩,GalilScaffoldChainConsume.ready c xs b⟩,
        GalilScaffoldCounter.ofNat v,final.margin⟩ := by
    simp [watchStart,hlag]
  rw [hstart]
  obtain ⟨actual,htrace,_⟩ := GalilScaffoldChainWatchTrace.run_trace hwatch
  have hdist : GalilScaffoldCounter.value z.control.distance = n := by
    have := htrace.distance
    have hz : GalilScaffoldCounter.value (GalilScaffoldChainConsume.ready c xs b).distance = 0 := rfl
    simp only at this
    rw [hz,zero_add] at this
    have hlen : actual.length = n := by
      have hpos := reads_position htrace.reads ((a :: ls).reverse ++ rs ++ qs)
        ⟨a :: ls,rs,qs,rfl,rfl⟩ (by simp [layout])
      have hn := (verify_run_position hrun ⟨a :: ls,rs,qs,rfl,rfl⟩ (by simp [layout])).1
      simp only at hpos hn
      omega
    rw [this,hlen]
  refine ⟨z,hwatch,hb,hrep,hdist,?_⟩
  intro h4
  rw [hh] at h4
  exact (GalilScaffoldChainPrediction.watch_phase hwatch c b xs rfl (by rw [hdist]; omega)).1

#print axioms found_watch_run

/-! ## Interleaved outer matches

With outer matched events, a watch tick consumes once while the lag is
positive (`Internal.take`), then either queues the event (lag positive) or
consumes it immediately (lag zero). The number of consumes and the final lag
are determined by the event list; if the verifier can perform that many
unbroken consumes, the watch run exists and the margin grows by one per event. -/

/-- One tick's bookkeeping: consumes performed and the lag afterwards. -/
def watchTick (b : Bool) (lag : ℕ) : ℕ × ℕ :=
  let lag1 := lag-1
  let took := if 0 < lag then 1 else 0
  if b then (if lag1 = 0 ∧ 0 < lag then (took+1,0) else if lag1 = 0 then (took+1,0) else (took,lag1+1))
  else (took,lag1)

def watchConsumes : List Bool → ℕ → ℕ
  | [], _ => 0
  | b :: bs, lag => (watchTick b lag).1+watchConsumes bs (watchTick b lag).2

def watchLag : List Bool → ℕ → ℕ
  | [], lag => lag
  | b :: bs, lag => watchLag bs (watchTick b lag).2

theorem verify_run_add {s t : GalilScaffoldChainVerifier.State} (m n : ℕ)
    (hr : GalilScaffoldChainVerifyRun.Run s (m+n) t) :
    ∃ u, GalilScaffoldChainVerifyRun.Run s m u ∧ GalilScaffoldChainVerifyRun.Run u n t := by
  induction m generalizing s with
  | zero => exact ⟨s,.stop s,by simpa using hr⟩
  | succ m ih =>
    rw [show m+1+n = (m+n)+1 by omega] at hr
    cases hr with
    | next _ hp hr' =>
      obtain ⟨u,h1,h2⟩ := ih hr'
      exact ⟨u,.next _ hp h1,h2⟩

theorem inc_ofNat' (n : ℕ) : GalilScaffoldCounter.inc (GalilScaffoldCounter.ofNat n) =
    GalilScaffoldCounter.ofNat (n+1) := GalilScaffoldCounter.inc_ofNat n

/-- `n` increments of a counter. -/
def incN : ℕ → GalilScaffoldCounter.Counter → GalilScaffoldCounter.Counter
  | 0, m => m
  | n+1, m => incN n (GalilScaffoldCounter.inc m)

theorem incN_value (n : ℕ) : ∀ m : GalilScaffoldCounter.Counter,
    GalilScaffoldCounter.value (incN n m) = GalilScaffoldCounter.value m+n := by
  induction n with
  | zero => intro m; simp [incN]
  | succ n ih => intro m; rw [incN,ih,GalilScaffoldCounter.inc_value]; push_cast; ring

theorem incN_canonical (n : ℕ) : ∀ m : GalilScaffoldCounter.Counter,
    GalilScaffoldCounter.Canonical m → GalilScaffoldCounter.Canonical (incN n m) := by
  induction n with
  | zero => intro m h; exact h
  | succ n ih => intro m h; exact ih _ (GalilScaffoldCounter.inc_canonical _ h)

/-- The general watch run over any outer event list, from enough unbroken
consumes. Lag and margin are kept in canonical natural form. -/
theorem verify_watch_run_events (bs : List Bool) :
    ∀ (lag : ℕ) {s t : GalilScaffoldChainVerifier.State} (margin : GalilScaffoldCounter.Counter),
      GalilScaffoldChainVerifyRun.Run s (watchConsumes bs lag) t → t.control.broken = false →
      GalilScaffoldChainWatch.Run ⟨s,GalilScaffoldCounter.ofNat lag,margin⟩
        bs ⟨t,GalilScaffoldCounter.ofNat (watchLag bs lag),incN (bs.count true) margin⟩ := by
  induction bs with
  | nil =>
    intro lag s t margin hr ht
    cases hr
    simp only [watchLag,List.count_nil,incN]
    exact GalilScaffoldChainWatch.Run.stop _
  | cons b bs ih =>
    intro lag s t margin hr ht
    simp only [watchConsumes] at hr
    obtain ⟨u,h1,h2⟩ := verify_run_add _ _ hr
    have hu : u.control.broken = false := GalilScaffoldChainCatch.run_unbroken h2 ht
    -- the internal phase
    have hinternal : ∀ (m1 : GalilScaffoldChainVerifier.State),
        GalilScaffoldChainVerifyRun.Run s (if 0 < lag then 1 else 0) m1 → m1.control.broken = false →
        GalilScaffoldChainWatch.Internal ⟨s,GalilScaffoldCounter.ofNat lag,margin⟩
          ⟨m1,GalilScaffoldCounter.ofNat (lag-1),margin⟩ := by
      intro m1 hm1 hb1
      by_cases hl : 0 < lag
      · rw [if_pos hl] at hm1
        cases hm1 with
        | next _ hp hr' =>
          cases hr'
          have hpos : GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat lag) = true := by
            rw [GalilScaffoldCounter.positive_iff _ (GalilScaffoldCounter.ofNat_canonical _),
              GalilScaffoldCounter.ofNat_value]; omega
          have hg := good_of_consume s hp hb1 (GalilScaffoldCounter.ofNat lag) margin
          have := GalilScaffoldChainWatch.Internal.take _ hpos hg
          have e : GalilScaffoldCounter.dec (GalilScaffoldCounter.ofNat lag) = GalilScaffoldCounter.ofNat (lag-1) := by
            obtain ⟨k,rfl⟩ : ∃ k, lag = k+1 := ⟨lag-1,by omega⟩
            rw [GalilScaffoldCounter.dec_ofNat_succ]; simp
          simpa [GalilScaffoldChainWatch.caught,e] using this
      · rw [if_neg hl] at hm1
        cases hm1
        have hz : GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat lag) = false := by
          rw [Bool.eq_false_iff]
          intro h
          rw [GalilScaffoldCounter.positive_iff _ (GalilScaffoldCounter.ofNat_canonical _),
            GalilScaffoldCounter.ofNat_value] at h
          omega
        rw [show lag-1 = lag by omega]
        exact .idle _ hz
    -- split the tick's consumes into internal and outer parts
    by_cases hb : b = true
    · subst hb
      by_cases hz : lag-1 = 0
      · -- immediate outer consume
        have hc : watchTick true lag = ((if 0 < lag then 1 else 0)+1,0) := by
          simp [watchTick,hz]
        rw [hc] at h1 h2
        simp only at h1 h2
        obtain ⟨m1,hm1,hm2⟩ := verify_run_add _ 1 h1
        have hb1 : m1.control.broken = false := GalilScaffoldChainCatch.run_unbroken hm2 hu
        have hint := hinternal m1 hm1 hb1
        cases hm2 with
        | next _ hp hr' =>
          cases hr'
          have hg := good_of_consume m1 hp hu (GalilScaffoldCounter.ofNat (lag-1)) margin
          have hzero : GalilScaffoldCounter.zero (GalilScaffoldCounter.ofNat (lag-1)) = true := by
            rw [hz]; rfl
          have houter := GalilScaffoldChainWatch.Outer.immediate _ hzero hg
          have htick : GalilScaffoldChainWatch.Tick
              ⟨s,GalilScaffoldCounter.ofNat lag,margin⟩ true
              ⟨consume m1,GalilScaffoldCounter.ofNat 0,GalilScaffoldCounter.inc margin⟩ := by
            refine .step hint ?_
            simpa [GalilScaffoldChainWatch.immediate,hz] using houter
          have hrest := ih 0 (GalilScaffoldCounter.inc margin) h2 ht
          have hlag : watchLag (true :: bs) lag = watchLag bs 0 := by simp [watchLag,hc]
          rw [hlag,show (true :: bs).count true = bs.count true+1 by simp,incN]
          exact .next htick hrest
      · -- queued outer event
        have hc : watchTick true lag = ((if 0 < lag then 1 else 0),lag-1+1) := by
          simp [watchTick,hz]
        rw [hc] at h1 h2
        simp only at h1 h2
        have hint := hinternal u h1 hu
        have hnz : GalilScaffoldCounter.zero (GalilScaffoldCounter.ofNat (lag-1)) = false := by
          obtain ⟨k,hk⟩ : ∃ k, lag-1 = k+1 := ⟨lag-2,by omega⟩
          rw [hk]; rfl
        have houter := GalilScaffoldChainWatch.Outer.queued
          ⟨u,GalilScaffoldCounter.ofNat (lag-1),margin⟩ hnz
        have htick : GalilScaffoldChainWatch.Tick
            ⟨s,GalilScaffoldCounter.ofNat lag,margin⟩ true
            ⟨u,GalilScaffoldCounter.ofNat (lag-1+1),GalilScaffoldCounter.inc margin⟩ := by
          refine .step hint ?_
          simpa [GalilScaffoldChainWatch.queued,inc_ofNat'] using houter
        have hrest := ih (lag-1+1) (GalilScaffoldCounter.inc margin) h2 ht
        have hlag : watchLag (true :: bs) lag = watchLag bs (lag-1+1) := by simp [watchLag,hc]
        rw [hlag,show (true :: bs).count true = bs.count true+1 by simp,incN]
        exact .next htick hrest
    · have hb' : b = false := by cases b <;> simp_all
      subst hb'
      have hc : watchTick false lag = ((if 0 < lag then 1 else 0),lag-1) := by simp [watchTick]
      rw [hc] at h1 h2
      simp only at h1 h2
      have hint := hinternal u h1 hu
      have htick : GalilScaffoldChainWatch.Tick
          ⟨s,GalilScaffoldCounter.ofNat lag,margin⟩ false
          ⟨u,GalilScaffoldCounter.ofNat (lag-1),margin⟩ :=
        .step hint (.idle _)
      have hrest := ih (lag-1) margin h2 ht
      have hlag : watchLag (false :: bs) lag = watchLag bs (lag-1) := by simp [watchLag,hc]
      rw [hlag,show (false :: bs).count true = bs.count true by simp]
      exact .next htick hrest

#print axioms verify_watch_run_events

/-! ## The outer scan during the watch

Each `true` watch event is a matched outer compare of the scan: L moves left,
R moves right, and the palindrome grows by one; `false` ticks leave the scan
heads alone. -/

inductive ScanEvents (raw : List (Fin 2)) (c : ℕ) :
    ℕ → PlaceHead → PlaceHead → List Bool → PlaceHead → PlaceHead → Prop
  | stop (r l rr) : ScanEvents raw c r l rr [] l rr
  | skip (r l rr) {bs l' rr'} (rest : ScanEvents raw c r l rr bs l' rr') :
      ScanEvents raw c r l rr (false :: bs) l' rr'
  | matched (r l rr) {bs l' rr'} (hc : canRight rr)
      (hm : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) =
        GalilScaffoldInputHead.read (right rr))
      (rest : ScanEvents raw c (r+1) (GalilScaffoldInputHead.left l) (right rr) bs l' rr') :
      ScanEvents raw c r l rr (true :: bs) l' rr'

theorem scan_events_invariant {raw : List (Fin 2)} {c r : ℕ} {l rr : PlaceHead}
    {bs : List Bool} {l' rr' : PlaceHead}
    (he : ScanEvents raw c r l rr bs l' rr') (hi : ScanInvariant raw c r l rr) :
    ScanInvariant raw c (r+bs.count true) l' rr' := by
  induction he with
  | stop r l rr => simpa using hi
  | skip r l rr _ ih => simpa using ih hi
  | matched r l rr hc hm _ ih =>
    have := ih (scan_matched hi hc hm)
    simpa [List.count_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using this

#print axioms scan_events_invariant

/-- What the fresh shift needs from the watch phase, supplied from the same
event lists: the scan's matched compares during preparation and during the
watch grow the palindrome, the watch consumes the queued reads, and once the
lag is exhausted with at least four semiperiods verified the chain is in
phase `4`. The unbroken consume run is the branch condition of the shift
path (a broken consume is the restart path). -/
theorem watch_shift_supply {raw : List (Fin 2)} (cen : PlaceHead) (c : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : GalilScaffoldCounter.Counter)
    (r0 : ℕ) (hr0 : GalilScaffoldCounter.value radius = r0)
    (sm dm : Bool) (bs cs : List Bool)
    (hcanon : GalilScaffoldCounter.Canonical
      (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm bs cs)).lag)
    {l0 rr0 l1 rr1 l2 rr2 : PlaceHead} {ws : List Bool}
    (hi0 : ScanInvariant raw (position cen) r0 l0 rr0)
    (hprep : ScanEvents raw (position cen) r0 l0 rr0 (sm :: (bs ++ dm :: cs)) l1 rr1)
    (hwatch : ScanEvents raw (position cen) (r0+(sm :: (bs ++ dm :: cs)).count true) l1 rr1 ws l2 rr2)
    {z : GalilScaffoldChainVerifier.State}
    (hrun : GalilScaffoldChainVerifyRun.Run ⟨cen,GalilScaffoldChainConsume.ready c ys b⟩
      (watchConsumes ws (r0+(sm :: (bs ++ dm :: cs)).count true)) z)
    (hz : z.control.broken = false)
    (hexhausted : watchLag ws (r0+(sm :: (bs ++ dm :: cs)).count true) = 0) :
    let final := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
      (GalilScaffoldChainCredits.prepEvents sm dm bs cs)
    let s0 := watchStart cen c ys b final
    let initialRadius := r0+(sm :: (bs ++ dm :: cs)).count true
    let scanRadius := initialRadius+ws.count true
    ∃ t', GalilScaffoldChainWatch.Run s0 ws t' ∧
      GalilScaffoldCounter.value s0.lag = initialRadius ∧
      GalilScaffoldCounter.zero t'.lag = true ∧
      t'.machine = z ∧
      GalilScaffoldCounter.value t'.machine.control.distance = scanRadius ∧
      (4*(ys.length+1) ≤ scanRadius → t'.machine.control.phase = 4) ∧
      ScanInvariant raw (position cen) scanRadius l2 rr2 := by
  intro final s0 initialRadius scanRadius
  have hpv := (GalilScaffoldChainCredits.prep_value radius sm dm bs cs).2
  have hlagv : GalilScaffoldCounter.value final.lag = initialRadius := by
    rw [hpv,hr0]; simp [initialRadius]
  have hlagn : final.lag = GalilScaffoldCounter.ofNat initialRadius :=
    GalilScaffoldChainCatch.canonical_nat _ hcanon _ hlagv
  have hs0 : s0 = ⟨⟨cen,GalilScaffoldChainConsume.ready c ys b⟩,
      GalilScaffoldCounter.ofNat initialRadius,final.margin⟩ := by
    simp [s0,watchStart,hlagn]
  have hw := verify_watch_run_events ws initialRadius final.margin hrun hz
  rw [hexhausted] at hw
  rw [hs0]
  refine ⟨_,hw,by rw [GalilScaffoldCounter.ofNat_value],rfl,rfl,?_,?_,?_⟩
  · have hp := watch_progress hw
    simp only [GalilScaffoldCounter.ofNat_value] at hp
    have hz0 : GalilScaffoldCounter.value (GalilScaffoldChainConsume.ready c ys b).distance = 0 := rfl
    rw [hz0] at hp
    simp only [scanRadius]
    push_cast
    omega
  · intro h4
    have hd : (4*(ys.length+1) : ℤ) ≤ GalilScaffoldCounter.value z.control.distance := by
      have hp := watch_progress hw
      simp only [GalilScaffoldCounter.ofNat_value] at hp
      have hz0 : GalilScaffoldCounter.value (GalilScaffoldChainConsume.ready c ys b).distance = 0 := rfl
      rw [hz0] at hp
      simp only [scanRadius,initialRadius] at h4
      push_cast at hp ⊢
      omega
    exact (GalilScaffoldChainPrediction.watch_phase hw c b ys rfl hd).1
  · have h1 := scan_events_invariant hprep hi0
    exact scan_events_invariant hwatch h1

#print axioms watch_shift_supply

theorem credits_margin_canonical (es : List (Bool × Bool)) :
    ∀ s : GalilScaffoldChainCredits.State, GalilScaffoldCounter.Canonical s.margin →
      GalilScaffoldCounter.Canonical (GalilScaffoldChainCredits.run s es).margin := by
  induction es with
  | nil => intro s h; exact h
  | cons e es ih =>
    intro s h
    apply ih
    simp only [GalilScaffoldChainCredits.step,GalilScaffoldChainCredits.decFour]
    have h4 : GalilScaffoldCounter.Canonical (GalilScaffoldCounter.dec (GalilScaffoldCounter.dec
        (GalilScaffoldCounter.dec (GalilScaffoldCounter.dec s.margin)))) :=
      GalilScaffoldCounter.dec_canonical _ (GalilScaffoldCounter.dec_canonical _
        (GalilScaffoldCounter.dec_canonical _ (GalilScaffoldCounter.dec_canonical _ h)))
    split <;> split <;> first
      | exact GalilScaffoldCounter.inc_canonical _ h4 | exact h4
      | exact GalilScaffoldCounter.inc_canonical _ h | exact h

theorem credits_lag_canonical (es : List (Bool × Bool)) :
    ∀ s : GalilScaffoldChainCredits.State, GalilScaffoldCounter.Canonical s.lag →
      GalilScaffoldCounter.Canonical (GalilScaffoldChainCredits.run s es).lag := by
  induction es with
  | nil => intro s h; exact h
  | cons e es ih =>
    intro s h
    apply ih
    simp only [GalilScaffoldChainCredits.step]
    split <;> first | exact GalilScaffoldCounter.inc_canonical _ h | exact h

/-- `found_rounds_restart` with its watch-phase premises discharged by
`watch_shift_supply`. What remains external is the input-side branch
condition of the shift (right symbol available, prediction equal to it,
outer symbols unequal), the counter representations, and the same event
lists seen by the scan and by the chain. -/
theorem found_supplied_restart {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (span lower : ℕ)
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config))
    (radius : GalilScaffoldCounter.Counter) (hrc : GalilScaffoldCounter.Canonical radius)
    (r0 : ℕ) (hr0 : GalilScaffoldCounter.value radius = r0) (hrp : 0 < r0)
    (sm dm : Bool) :
    ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h ∧
      ys.length+1 = h ∧
      ∀ (copyMatches backMatches : List Bool), copyMatches.length = h → backMatches.length = h+1 →
      ∀ {l0 rr0 l1 rr1 l2 rr2 : PlaceHead} {ws : List Bool},
      ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (position cen) r0 l0 rr0 →
      ScanEvents ((a :: ls).reverse ++ (rs ++ q)) (position cen) r0 l0 rr0
        (sm :: (copyMatches ++ dm :: backMatches)) l1 rr1 →
      ScanEvents ((a :: ls).reverse ++ (rs ++ q)) (position cen)
        (r0+(sm :: (copyMatches ++ dm :: backMatches)).count true) l1 rr1 ws l2 rr2 →
      ∀ {z : GalilScaffoldChainVerifier.State},
      GalilScaffoldChainVerifyRun.Run ⟨cen,GalilScaffoldChainConsume.ready c ys b⟩
        (watchConsumes ws (r0+(sm :: (copyMatches ++ dm :: backMatches)).count true)) z →
      z.control.broken = false →
      watchLag ws (r0+(sm :: (copyMatches ++ dm :: backMatches)).count true) = 0 →
      let scanRadius := r0+(sm :: (copyMatches ++ dm :: backMatches)).count true+ws.count true
      4*h ≤ scanRadius →
      canRight rr2 →
      ∀ (predicted : Fin 3),
      GalilScaffoldChainConsume.symbol z.control.period.focus = some predicted →
      GalilScaffoldInputHead.read (right rr2) = some predicted →
      ∀ (radiusCounter lengthCounter : GalilScaffoldCounter.Counter),
      GalilScaffoldCounter.value radiusCounter = (scanRadius : ℤ)+1 →
      GalilScaffoldCounter.Canonical radiusCounter →
      GalilScaffoldCounter.Canonical lengthCounter →
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l2) ≠
        GalilScaffoldInputHead.read (right rr2) →
      ∃ t', GalilScaffoldChainWatch.Run
        (watchStart cen c ys b
          (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
            (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches))) ws t' ∧
      t'.machine = z ∧ GalilScaffoldCounter.zero t'.lag = true ∧
      ∃ endpoint watchEnd cycleEnd,
        ShiftRun ⟨cen,GalilScaffoldInputHead.left l2,
          GalilScaffoldCounter.ofNat h,radiusCounter,lengthCounter⟩ h endpoint ∧
        ChainShiftRun ⟨cen,GalilScaffoldInputHead.left l2,
          GalilScaffoldCounter.ofNat h,radiusCounter,lengthCounter⟩
          (GalilScaffoldChainWatch.immediate t') GalilScaffoldCounter.reset h
          endpoint watchEnd cycleEnd ∧
        ∀ (m n : ℕ) (s' final' : OnlyCompareState),
          CompareRounds h
            ⟨endpoint.center,endpoint.left,right rr2,watchEnd,cycleEnd,endpoint.radius⟩ m s' →
          OnlyMatchedRun s' n final' →
          GalilScaffoldInputHead.read s'.center ≠ none →
          GalilScaffoldCounter.singlePositive final'.cycle = true → canRight final'.right →
          GalilScaffoldInputHead.read (GalilScaffoldInputHead.left final'.left) =
            GalilScaffoldInputHead.read (right final'.right) →
          let endState := onlyCompareNext final'
          let center := position cen+(m+1)*h
          let radius' := scanRadius+1+m*h-h
          ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) center (radius'+n+1)
              endState.left endState.right ∧
            endState.watch.machine.control.broken = true ∧
            GalilScaffoldCounter.negative endState.watch.margin = false ∧
            GalilScaffoldCounter.positive endState.watch.machine.control.last = true ∧
            GalilScaffoldCounter.zero endState.watch.lag = true ∧
            GalilScaffoldInputHead.read endState.center ≠ none ∧
            RadiusRep endState.radius (radius'+n+1) ∧
            GalilScaffoldCounter.negative endState.radius = false ∧
            (GalilScaffoldSearchFinish.begin endState.watch.machine.control.last
              endState.radius).work = endState.watch.machine.control.last ∧
            GalilScaffoldCounter.Canonical endState.watch.machine.control.last := by
  obtain ⟨h,ys,b,hcand,hys,_,hrest⟩ :=
    found_rounds_restart a ls rs q gap cen hcen c hc span lower hr hs ht hv radius hrc
      (by rw [hr0]; exact_mod_cast hrp) sm dm
  refine ⟨h,ys,b,hcand,hys,?_⟩
  intro copyMatches backMatches hcl hbl l0 rr0 l1 rr1 l2 rr2 ws hi0 hprep hwatch z hrun hz
    hexhausted scanRadius h4 hcan predicted hpred hread radiusCounter lengthCounter hcounter
    hrcanon hlcanon hmismatch
  have hcanon : GalilScaffoldCounter.Canonical
      (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches)).lag :=
    credits_lag_canonical _ _ hrc
  obtain ⟨t',hwrun,hlag,hzero,hmach,_,hphase,hi⟩ :=
    watch_shift_supply cen c ys b radius r0 hr0 sm dm copyMatches backMatches hcanon
      hi0 hprep hwatch hrun hz hexhausted
  have hphase' := hphase (by rw [hys]; exact h4)
  have hpred' : GalilScaffoldChainConsume.symbol t'.machine.control.period.focus = some predicted := by
    rw [hmach]; exact hpred
  have := hrest copyMatches backMatches hcl hbl hwrun hphase' _ scanRadius hlag hzero rfl l2 rr2 hi
    hcan predicted hpred' hread radiusCounter lengthCounter hcounter hrcanon hlcanon hmismatch
  exact ⟨t',hwrun,hmach,hzero,this⟩

#print axioms found_supplied_restart

/-! ## Output semantics

Scala sets `output = left.isFirst` whenever R stands on a letter: the scan
reports a palindrome exactly when L has reached the first letter. On the
encoded word letters sit at odd positions, so a scan with L at position `1`
and R at position `2k-1` is a palindrome of the first `k` letters. -/

theorem pairs_odd (raw : List (Fin 2)) : ∀ i,
    (pairs raw)[2*i+1]? = raw[i]?.map GalilScaffoldPlace.letter := by
  induction raw with
  | nil => intro i; simp [pairs]
  | cons a raw ih =>
    intro i
    cases i with
    | zero => simp [pairs]
    | succ i =>
      rw [show 2*(i+1)+1 = (2*i+1)+2 by omega]
      simp only [pairs,List.getElem?_cons_succ]
      exact ih i

theorem encoded_odd (raw : List (Fin 2)) (i : ℕ) (hi : i < raw.length) :
    (encoded raw)[2*i+1]? = some (GalilScaffoldPlace.letter raw[i]) := by
  rw [encoded,List.getElem?_append_left (by rw [pairs_length]; omega),pairs_odd,
    List.getElem?_eq_getElem hi]
  rfl

theorem letter_inj {a b : Fin 2} (h : GalilScaffoldPlace.letter a = GalilScaffoldPlace.letter b) :
    a = b := by
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [GalilScaffoldPlace.letter] using this

/-- A palindrome of the encoded word centred on the `k`-th letter with radius
`k-1` is a palindrome of the first `k` letters. -/
theorem prefix_palindrome_of_encoded (raw : List (Fin 2)) (k : ℕ) (hk : 0 < k)
    (hk2 : k ≤ raw.length) (hpal : Manacher.PalAt (encoded raw) k (k-1)) :
    IsPal (raw.take k) := by
  rw [Manacher.isPal_take_iff_index hk2]
  intro i hi
  obtain ⟨_,_,hsym⟩ := hpal
  -- compare letters `i` and `k-1-i` through their odd encoded positions
  have key : ∀ i, i < k → i ≤ k-1-i →
      raw[i]? = raw[k-1-i]? := by
    intro i hi hle
    have hj := hsym (k-1-2*i) (by omega)
    have e1 : k-(k-1-2*i) = 2*i+1 := by omega
    have e2 : k+(k-1-2*i) = 2*(k-1-i)+1 := by omega
    rw [e1,e2,encoded_odd raw i (by omega),encoded_odd raw (k-1-i) (by omega)] at hj
    have := letter_inj (Option.some.inj hj)
    rw [List.getElem?_eq_getElem (by omega),List.getElem?_eq_getElem (by omega),this]
  by_cases hle : i ≤ k-1-i
  · exact key i hi hle
  · have := key (k-1-i) (by omega) (by omega)
    rw [show k-1-(k-1-i) = i by omega] at this
    exact this.symm

theorem pairs_even (raw : List (Fin 2)) : ∀ i, i < raw.length →
    (pairs raw)[2*i]? = some 2 := by
  induction raw with
  | nil => intro i hi; simp at hi
  | cons a raw ih =>
    intro i hi
    cases i with
    | zero => simp [pairs]
    | succ i =>
      rw [show 2*(i+1) = (2*i)+2 by omega]
      simp only [pairs,List.getElem?_cons_succ]
      exact ih i (by simp at hi; omega)

theorem encoded_even (raw : List (Fin 2)) (i : ℕ) (hi : i ≤ raw.length) :
    (encoded raw)[2*i]? = some 2 := by
  rcases Nat.lt_or_eq_of_le hi with h | h
  · rw [encoded,List.getElem?_append_left (by rw [pairs_length]; omega),pairs_even raw i h]
  · rw [encoded,List.getElem?_append_right (by rw [pairs_length]; omega),pairs_length,h]
    simp

/-- Converse of `prefix_palindrome_of_encoded`: a palindrome of the first `k`
letters is a palindrome of the encoded word centred on the `k`-th letter with
radius `k-1`. Even positions all carry the separator `2`, odd positions carry
the letters. -/
theorem encoded_of_prefix_palindrome (raw : List (Fin 2)) (k : ℕ) (hk : 0 < k)
    (hk2 : k ≤ raw.length) (hpal : IsPal (raw.take k)) :
    Manacher.PalAt (encoded raw) k (k-1) := by
  rw [Manacher.isPal_take_iff_index hk2] at hpal
  refine ⟨by omega,?_,?_⟩
  · rw [encoded,List.length_append,pairs_length]; simp; omega
  · intro j hj
    rcases Nat.even_or_odd (k-j) with ⟨m,hm⟩ | ⟨m,hm⟩
    · -- both positions even: separators
      have e1 : k-j = 2*m := by omega
      have e2 : k+j = 2*(m+j) := by omega
      rw [e1,e2,encoded_even raw _ (by omega),encoded_even raw _ (by omega)]
    · -- both positions odd: letters `m` and `m+j`
      have e1 : k-j = 2*m+1 := by omega
      have e2 : k+j = 2*(m+j)+1 := by omega
      rw [e1,e2,encoded_odd raw _ (by omega),encoded_odd raw _ (by omega)]
      have := hpal m (by omega)
      rw [show k-1-m = m+j by omega] at this
      rw [List.getElem?_eq_getElem (by omega),List.getElem?_eq_getElem (by omega)] at this
      rw [Option.some.inj this]

#print axioms encoded_of_prefix_palindrome

/-- Output completeness at the invariant level: when the scan invariant holds
with centre `k` and radius `k-1`, the heads stand exactly at the output
positions (L on the first letter, R on the `k`-th letter). -/
theorem scan_output_complete {raw : List (Fin 2)} {c r : ℕ} {l rr : PlaceHead}
    (hi : ScanInvariant raw c r l rr) (k : ℕ) (hc : c = k) (hr : r = k-1) (hk : 0 < k) :
    position l = 1 ∧ position rr = 2*k-1 := by
  have hlp := hi.leftPos
  have hrp := hi.rightPos
  subst hc; subst hr
  constructor <;> omega

#print axioms scan_output_complete

/-- The output condition of the scan: L on the first letter and R on the
`k`-th letter means the first `k` letters form a palindrome. -/
theorem scan_output {raw : List (Fin 2)} {c r : ℕ} {l rr : PlaceHead}
    (hi : ScanInvariant raw c r l rr) (k : ℕ) (hk : 0 < k) (hk2 : k ≤ raw.length)
    (hl : position l = 1) (hr : position rr = 2*k-1) : IsPal (raw.take k) := by
  have hle := hi.palindrome.1
  have hlp := hi.leftPos
  have hrp := hi.rightPos
  have hc : c = k := by omega
  have hrad : r = k-1 := by omega
  have hp := hi.palindrome
  rw [hc,hrad] at hp
  exact prefix_palindrome_of_encoded raw k hk hk2 hp

#print axioms scan_output

/-! ## Junction with the staged search

`GalilScaffoldStagePrepare.prepared_exit` drives the search from the paced
preparation through the DP run to `found`, `missed`, `idle` or the next
stage. Its search run is `SafeQuanta (runState p q) p.program cs u y`; when it
ends in `found` with the DP result on `y`, the chain entry above applies. -/

theorem stage_found_supplied {p : GalilScaffoldPrepareControl.State} {q : Fin 4}
    {cs : List Bool} {u : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (span lower : ℕ)
    (hr : GalilScaffoldSearchRun.SafeQuanta (GalilScaffoldStagePrepare.runState p q) p.program cs u y)
    (hm : p.mode = .run) (hu : u.mode = .found)
    (hv : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config))
    (radius : GalilScaffoldCounter.Counter) (hrc : GalilScaffoldCounter.Canonical radius)
    (r0 : ℕ) (hr0 : GalilScaffoldCounter.value radius = r0) (hrp : 0 < r0) (sm dm : Bool) :
    ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h ∧
      ys.length+1 = h :=
  let ⟨h,ys,b,hcand,hys,_⟩ := found_supplied_restart a ls rs qq gap cen hcen c hc span lower hr
    (by simp [GalilScaffoldStagePrepare.runState,hm]) hu hv radius hrc r0 hr0 hrp sm dm
  ⟨h,ys,b,hcand,hys⟩

#print axioms stage_found_supplied

/-! ## Determinism of the scheduled search

`Execute` is deterministic for well-formed instructions (read tables without
duplicate symbols), which `dp_wellFormed` certifies for the DP code. Hence the
ticked machine, the safe call sequence and the quanta run are functions of
their event lists, and the actual search run that leaves `run` mode is the
one `dp_quanta_safe` exhibits: its final machine carries the DP result. -/

theorem execute_unique {n : ℕ} {i : GalilFppWide.Instruction n}
    {x y y' : GalilScaffoldProgram.Config n}
    (hw : GalilScaffoldNextPc.WellFormed i)
    (h1 : GalilScaffoldProgram.Execute i x y) (h2 : GalilScaffoldProgram.Execute i x y') :
    y = y' := by
  cases h1 with
  | right x t m => cases h2; rfl
  | left x t m _ => cases h2; rfl
  | write x t s m => cases h2; rfl
  | read x t cs m hm =>
    cases h2 with
    | read _ _ _ m' hm' =>
      have hnodup : (cs.map Prod.fst).Nodup := hw
      have := List.inj_on_of_nodup_map hnodup hm hm' rfl
      cases this
      rfl

theorem control_tick_unique {n : ℕ} {code : List (GalilFppWide.Instruction n)}
    (hw : ∀ i ∈ code, GalilScaffoldNextPc.WellFormed i) {e : Bool}
    {x y y' : GalilScaffoldControl.Machine n}
    (h1 : GalilScaffoldControl.Tick code e x y) (h2 : GalilScaffoldControl.Tick code e x y') :
    y = y' := by
  cases h1 with
  | idle x e h =>
    cases h2 with
    | idle => rfl
    | halt _ _ => simp at h
    | execute _ _ _ _ _ => simp at h
  | halt x hi =>
    cases h2 with
    | idle _ _ h => simp at h
    | halt => rfl
    | execute _ _ i hi' he =>
      rw [hi] at hi'
      cases hi'
      cases he
  | execute x y i hi he =>
    cases h2 with
    | idle _ _ h => simp at h
    | halt _ hi' =>
      rw [hi] at hi'
      cases hi'
      cases he
    | execute _ y' i' hi' he' =>
      rw [hi] at hi'
      cases hi'
      have hwi : GalilScaffoldNextPc.WellFormed i := hw i (List.mem_of_getElem? hi)
      rw [execute_unique hwi he he']

theorem safe_calls_unique {s t t' : GalilScaffoldSearchFinish.State}
    {x y y' : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (h1 : GalilScaffoldSearchRun.SafeCalls s x bs t y)
    (h2 : GalilScaffoldSearchRun.SafeCalls s x bs t' y') : t = t' ∧ y = y' := by
  induction h1 generalizing t' y' with
  | nil s x => cases h2; exact ⟨rfl,rfl⟩
  | cons s x y z b bs t ht _ _ ih =>
    cases h2 with
    | cons _ _ y₂ _ _ _ _ ht₂ _ hr₂ =>
      have := control_tick_unique GalilScaffoldNextPc.dp_wellFormed ht ht₂
      subst this
      exact ih hr₂

theorem safe_quanta_unique {s t t' : GalilScaffoldSearchFinish.State}
    {x y y' : GalilScaffoldControl.Machine 12} {as : List Bool}
    (h1 : GalilScaffoldSearchRun.SafeQuanta s x as t y)
    (h2 : GalilScaffoldSearchRun.SafeQuanta s x as t' y') : t = t' ∧ y = y' := by
  induction h1 generalizing t' y' with
  | nil s x => cases h2; exact ⟨rfl,rfl⟩
  | cons s u t x y z a as _ hq _ ih =>
    cases h2 with
    | cons _ u₂ _ _ y₂ _ _ _ _ hq₂ hr₂ =>
      obtain ⟨rfl,rfl⟩ := safe_calls_unique hq hq₂
      exact ih hr₂

theorem safe_quanta_append {s t : GalilScaffoldSearchFinish.State}
    {x z : GalilScaffoldControl.Machine 12} (as bs : List Bool)
    (h : GalilScaffoldSearchRun.SafeQuanta s x (as ++ bs) t z) :
    ∃ m y, GalilScaffoldSearchRun.SafeQuanta s x as m y ∧
      GalilScaffoldSearchRun.SafeQuanta m y bs t z := by
  induction as generalizing s x with
  | nil => exact ⟨s,x,.nil s x,h⟩
  | cons a as ih =>
    cases h with
    | cons _ u _ _ y _ _ _ hm hq hr =>
      obtain ⟨m,y',h1,h2⟩ := ih hr
      exact ⟨m,y',.cons _ _ _ _ _ _ _ _ hm hq h1,h2⟩

theorem safe_quanta_cons_run {s t : GalilScaffoldSearchFinish.State}
    {x z : GalilScaffoldControl.Machine 12} {b : Bool} {bs : List Bool}
    (h : GalilScaffoldSearchRun.SafeQuanta s x (b :: bs) t z) : s.mode = .run := by
  cases h with
  | cons _ _ _ _ _ _ _ _ hm _ _ => exact hm

/-- The actual search run with the DP budget: leaving `run` mode is the halt
that `dp_quanta_safe` describes, so the final machine has the DP result and
the run used exactly the exhibited prefix. -/
theorem dp_run_result (w : List (Fin 3)) (lower : ℕ) (cs : List Bool)
    (ha : 3186*w.length+1683 ≤ 64*cs.length)
    (s : GalilScaffoldSearchFinish.State) (hs : s.mode = .run)
    (hc : GalilScaffoldCounter.Canonical s.debt)
    (hb : (cs.count true : ℤ) ≤ GalilScaffoldCounter.value s.debt)
    {u : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    (hr : GalilScaffoldSearchRun.SafeQuanta s ⟨GalilScaffoldPreload.initial w lower,false⟩ cs u y) :
    ∃ v, y = ⟨v,true⟩ ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) := by
  obtain ⟨used,rest,t,v,hsplit,hq,ht,hres,_,_,_⟩ :=
    GalilScaffoldSearchRun.dp_quanta_safe w lower cs ha s hs hc hb
  subst hsplit
  obtain ⟨m,y',h1,h2⟩ := safe_quanta_append used rest hr
  obtain ⟨rfl,rfl⟩ := safe_quanta_unique h1 hq
  cases rest with
  | nil =>
    cases h2
    exact ⟨v,rfl,hres⟩
  | cons b rest =>
    exact absurd (safe_quanta_cons_run h2) ht

#print axioms dp_run_result

/-- The scheduler/machine invariant along safe calls: `run` mode is exactly
"not yet halted", and once halted the mode is `found` exactly when the halt
pc is the found entry. -/
def RunInvariant (s : GalilScaffoldSearchFinish.State) (x : GalilScaffoldControl.Machine 12) : Prop :=
  (s.mode = .run ↔ x.done = false) ∧
    (x.done = true → (s.mode = .found ↔ x.config.pc = 346))

theorem safe_calls_invariant {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (h : GalilScaffoldSearchRun.SafeCalls s x bs t y) (hi : RunInvariant s x) :
    RunInvariant t y := by
  induction h with
  | nil s x => exact hi
  | cons s x y z b bs t ht _ _ ih =>
    apply ih
    obtain ⟨h1,h2⟩ := hi
    generalize he : (b && decide (s.mode = .run)) = e at ht ⊢
    cases ht with
    | idle _ _ hidle =>
      have he' : e = false := by
        rcases hidle with h | h
        · exact h
        · cases e with
          | false => rfl
          | true =>
            exfalso
            simp only [Bool.and_eq_true,decide_eq_true_eq] at he
            have := h1.mp he.2
            rw [h] at this
            cases this
      rw [he']
      unfold RunInvariant
      simp only [GalilScaffoldSearchFinish.finish,Bool.false_and,Bool.false_eq_true,if_false]
      exact ⟨h1,h2⟩
    | halt c hc =>
      refine ⟨?_,?_⟩
      · rw [GalilScaffoldSearchRun.finish_run_iff]; simp
      · intro _
        exact GalilScaffoldSearchFinish.found_iff s c.pc
    | execute c c' i hc hex =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at he
      have hs : s.mode = .run := he.2
      have hfin : GalilScaffoldSearchFinish.finish s true false c'.pc = s := by
        simp [GalilScaffoldSearchFinish.finish]
      rw [hfin]
      exact ⟨by simp [hs],by simp⟩

theorem safe_quanta_invariant {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (h : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hi : RunInvariant s x) :
    RunInvariant t y := by
  induction h with
  | nil s x => exact hi
  | cons s u t x y z a as _ hq _ ih =>
    apply ih
    have := safe_calls_invariant hq hi
    cases a <;> simpa [RunInvariant,GalilScaffoldSearchRun.advance] using this

/-- The actual search run with the DP budget ends in `found` exactly when a
candidate exists, and its final machine carries the DP result. -/
theorem run_found_candidate (w : List (Fin 3)) (lower : ℕ) (cs : List Bool)
    (ha : 3186*w.length+1683 ≤ 64*cs.length)
    (s : GalilScaffoldSearchFinish.State) (hs : s.mode = .run)
    (hc : GalilScaffoldCounter.Canonical s.debt)
    (hb : (cs.count true : ℤ) ≤ GalilScaffoldCounter.value s.debt)
    {u : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12}
    (hr : GalilScaffoldSearchRun.SafeQuanta s ⟨GalilScaffoldPreload.initial w lower,false⟩ cs u y) :
    ∃ v, y = ⟨v,true⟩ ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      u.mode ≠ .run ∧ (u.mode = .found ↔ ∃ k, GalilDpCorrect.Candidate w lower k) := by
  obtain ⟨v,hy,hres⟩ := dp_run_result w lower cs ha s hs hc hb hr
  have hinv := safe_quanta_invariant hr ⟨by simp [hs],by simp⟩
  subst hy
  obtain ⟨h1,h2⟩ := hinv
  refine ⟨v,rfl,hres,by simpa using h1,?_⟩
  have h2' : u.mode = .found ↔ v.pc = 346 := h2 rfl
  rw [h2']
  constructor
  · intro hpc
    rcases hres with ⟨k,_,hk,_⟩ | ⟨hpc',_⟩
    · exact ⟨k,hk⟩
    · exfalso
      change v.pc = 347 at hpc'
      omega
  · rintro ⟨k,hk⟩
    rcases hres with ⟨_,_,_,_,hpc,_⟩ | ⟨_,hnone⟩
    · exact hpc
    · exact absurd hk (hnone k (Nat.zero_le _))

#print axioms run_found_candidate

/-- The search stage after its preparation: the actual quanta run from the
prepared machine, with the DP budget, halts with the DP result; when it lands
in `found` the chain entry follows with all its watch-side supplies. -/
theorem stage_run_chain (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (span lower : ℕ) (s0 : GalilScaffoldPrepareControl.State)
    (hspan : s0.span = GalilScaffoldCounter.ofNat span)
    (hdebt : GalilScaffoldCounter.Canonical s0.debt)
    (q : Fin 4) (cs : List Bool)
    (ha : 3186*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)).length+1683 ≤ 64*cs.length)
    (hb : (cs.count true : ℤ) ≤ GalilScaffoldCounter.value s0.debt) :
    ∃ t, GalilScaffoldPrepareControl.PreparedRun (GalilScaffoldCounter.ofNat lower)
        ⟨a :: ls,gap⟩ s0
        (2*lower+2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)).length+7) t ∧
      t.mode = .run ∧
      t.program = ⟨GalilScaffoldPreload.initial ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower,false⟩ ∧
      ∀ {u : GalilScaffoldSearchFinish.State} {y : GalilScaffoldControl.Machine 12},
        GalilScaffoldSearchRun.SafeQuanta (GalilScaffoldStagePrepare.runState t q) t.program cs u y →
        ∃ v, y = ⟨v,true⟩ ∧
          GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
            (GalilScaffoldProgram.denote v) ∧
          u.mode ≠ .run ∧
          (u.mode = .found ↔ ∃ k, GalilDpCorrect.Candidate
            ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower k) ∧
          (u.mode = .found →
            ∀ (radius : GalilScaffoldCounter.Counter), GalilScaffoldCounter.Canonical radius →
            ∀ (r0 : ℕ), GalilScaffoldCounter.value radius = r0 → 0 < r0 → ∀ (sm dm : Bool),
            ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
              GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h ∧
              ys.length+1 = h) := by
  obtain ⟨t,hprep,hmode,hconfig,hdone,hdebt',_⟩ :=
    GalilScaffoldPrepareControl.prepare_complete s0 lower span ⟨a :: ls,gap⟩ hspan
  have hprog : t.program = ⟨GalilScaffoldPreload.initial
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower,false⟩ := by
    rcases hp : t.program with ⟨cfg,done⟩
    rw [hp] at hconfig hdone
    simp only at hconfig hdone
    rw [hconfig,hdone]
  refine ⟨t,hprep,hmode,hprog,?_⟩
  intro u y hr
  rw [hprog] at hr
  have hs : (GalilScaffoldStagePrepare.runState t q).mode = .run := by
    simp [GalilScaffoldStagePrepare.runState,hmode]
  have hcanon : GalilScaffoldCounter.Canonical (GalilScaffoldStagePrepare.runState t q).debt := by
    simp only [GalilScaffoldStagePrepare.runState]
    rw [hdebt']; exact hdebt
  have hb' : (cs.count true : ℤ) ≤
      GalilScaffoldCounter.value (GalilScaffoldStagePrepare.runState t q).debt := by
    simp only [GalilScaffoldStagePrepare.runState]
    rw [hdebt']; exact hb
  obtain ⟨v,hy,hres,hnr,hfound⟩ := run_found_candidate _ lower cs ha _ hs hcanon hb' hr
  refine ⟨v,hy,hres,hnr,hfound,?_⟩
  intro hu radius hrc r0 hr0 hrp sm dm
  rw [← hprog] at hr
  exact stage_found_supplied a ls rs qq gap cen hcen c hc span lower hr hmode hu
    (by rw [hy]; exact hres) radius hrc r0 hr0 hrp sm dm

#print axioms stage_run_chain

/-- The first search stage (`first_stage_safe`: grow, paced preparation, DP
run under the clock/advance correspondence) feeding the chain: when its
search lands in `found`, the DP candidate and the copied semiperiod follow
(and, through `found_supplied_restart`, the whole shift/restart chain). -/
theorem first_stage_chain (as bs cs : List Bool) (es : List (Bool × Bool))
    (s : GalilScaffoldPrepareControl.State) (r radius : ℕ)
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (quarter : Fin 4)
    (hm : s.mode = .grow) (hw : s.work = GalilScaffoldCounter.ofNat (max r 1))
    (hs : s.span = GalilScaffoldCounter.ofNat 0)
    (hd : GalilScaffoldCounter.value s.debt = -(radius : ℤ))
    (hcanon : GalilScaffoldCounter.Canonical s.debt)
    (ha : as.length = max r 1)
    (hb : bs.length = 2*r+2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max r 1+1)).length+7)
    (hcs : cs.length = GalilScaffoldTimingCost.runBudget (8*max r 1))
    (he : as++bs++cs = GalilScaffoldAdvanceClock.advances 2048 2048 es)
    (hr : 3*radius ≤ 5*r) :
    let w := (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max r 1+1)
    ∃ u p used rest t v, GalilScaffoldStagePrepare.PacedGrowing s as u ∧
      GalilScaffoldPreparePaced.PacedPrepared (GalilScaffoldCounter.ofNat r) ⟨a :: ls,gap⟩ u bs p ∧
      cs = used++rest ∧
      GalilScaffoldSearchRun.SafeQuanta (GalilScaffoldStagePrepare.runState p quarter) p.program
        used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w r 0 (GalilScaffoldProgram.denote v) ∧
      (t.mode = .found → p.mode = .run →
        ∀ (rad : GalilScaffoldCounter.Counter), GalilScaffoldCounter.Canonical rad →
        ∀ (r0 : ℕ), GalilScaffoldCounter.value rad = r0 → 0 < r0 → ∀ (sm dm : Bool),
        ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
          GalilDpCorrect.Candidate w r h ∧ ys.length+1 = h) := by
  intro w
  obtain ⟨u,p,used,rest,t,v,hg,hp,hsplit,hq,hnr,hres,_,_,_⟩ :=
    GalilScaffoldStagePrepare.first_stage_safe as bs cs es s r radius ⟨a :: ls,gap⟩ quarter
      hm hw hs hd hcanon ha hb hcs he hr
  refine ⟨u,p,used,rest,t,v,hg,hp,hsplit,hq,hnr,hres,?_⟩
  intro hfound hpm rad hrc r0 hr0 hrp sm dm
  exact stage_found_supplied a ls rs qq gap cen hcen c hc (8*max r 1) r hq hpm hfound hres
    rad hrc r0 hr0 hrp sm dm

#print axioms first_stage_chain

/-! ## The paced preparation ends in `run`

`PrepareControl.Tick` reads and writes everything but the debt, and the
paced run only touches the debt between ticks. So the paced preparation
agrees with the plain `prepare_complete` run on every field except the debt,
and in particular ends in `run` mode with the prepared DP machine. -/

namespace Prep

/-- Equality of all controller fields except the debt. -/
def Same (x y : GalilScaffoldPrepareControl.State) : Prop :=
  x.mode = y.mode ∧ x.program = y.program ∧ x.work = y.work ∧ x.span = y.span ∧
    x.walker = y.walker ∧ x.finalStage = y.finalStage

theorem same_refl (x : GalilScaffoldPrepareControl.State) : Same x x := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem same_symm {x y : GalilScaffoldPrepareControl.State} (h : Same x y) : Same y x :=
  ⟨h.1.symm,h.2.1.symm,h.2.2.1.symm,h.2.2.2.1.symm,h.2.2.2.2.1.symm,h.2.2.2.2.2.symm⟩

theorem same_trans {x y z : GalilScaffoldPrepareControl.State} (h1 : Same x y) (h2 : Same y z) : Same x z :=
  ⟨h1.1.trans h2.1,h1.2.1.trans h2.2.1,h1.2.2.1.trans h2.2.2.1,h1.2.2.2.1.trans h2.2.2.2.1,
    h1.2.2.2.2.1.trans h2.2.2.2.2.1,h1.2.2.2.2.2.trans h2.2.2.2.2.2⟩

theorem same_afterAdvance (b : Bool) (x : GalilScaffoldPrepareControl.State) :
    Same (GalilScaffoldPreparePaced.afterAdvance b x) x := by
  cases b <;> simp [Same,GalilScaffoldPreparePaced.afterAdvance]

theorem tape_same {x y : GalilScaffoldPrepareControl.State} (h : Same x y) (i : Fin 12)
    (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) : GalilScaffoldPrepareControl.tape x i f = GalilScaffoldPrepareControl.tape y i f := by
  simp [GalilScaffoldPrepareControl.tape,h.2.1]

/-- A tick transports along `Same`. -/
theorem tick_same {x y x' : GalilScaffoldPrepareControl.State} {b : Bool} (ht : GalilScaffoldPrepareControl.Tick b x y) (h : Same x x') :
    ∃ y', GalilScaffoldPrepareControl.Tick b x' y' ∧ Same y y' := by
  obtain ⟨hm,hp,hw,hs,hwk,hf⟩ := h
  cases ht with
  | idle x => exact ⟨x',.idle x',⟨hm,hp,hw,hs,hwk,hf⟩⟩
  | lowerBit x hm0 hp0 =>
    refine ⟨_,.lowerBit x' (by rw [← hm]; exact hm0) (by rw [← hw]; exact hp0),?_⟩
    simp [Same,GalilScaffoldPrepareControl.tape,hm,hp,hw,hs,hwk,hf]
  | lowerEnd x hm0 hp0 =>
    refine ⟨_,.lowerEnd x' (by rw [← hm]; exact hm0) (by rw [← hw]; exact hp0),?_⟩
    simp [Same,GalilScaffoldPrepareControl.tape,hm,hp,hw,hs,hwk,hf]
  | lowerLeft x hm0 hf0 hl0 =>
    refine ⟨_,.lowerLeft x' (by rw [← hm]; exact hm0) (by rw [← hp]; exact hf0)
      (by rw [← hp]; exact hl0),?_⟩
    simp [Same,GalilScaffoldPrepareControl.tape,hm,hp,hw,hs,hwk,hf]
  | beginCopy x hm0 hf0 =>
    refine ⟨_,.beginCopy x' (by rw [← hm]; exact hm0) (by rw [← hp]; exact hf0),?_⟩
    simp [Same,GalilScaffoldPrepareControl.tape,hm,hp,hw,hs,hwk,hf]
  | copyBit x a hm0 ha0 hw0 =>
    refine ⟨_,.copyBit x' a (by rw [← hm]; exact hm0) (by rw [← hwk]; exact ha0)
      (by rw [← hw]; exact hw0),?_⟩
    simp [Same,GalilScaffoldPrepareControl.tape,hm,hp,hw,hs,hwk,hf]
  | copyEnd x hm0 he0 =>
    refine ⟨_,.copyEnd x' (by rw [← hm]; exact hm0) (by rw [← hwk,← hw]; exact he0),?_⟩
    simp [Same,GalilScaffoldPrepareControl.tape,hm,hp,hw,hs,hwk,hf]
  | sourceLeft x hm0 hf0 hl0 =>
    refine ⟨_,.sourceLeft x' (by rw [← hm]; exact hm0) (by rw [← hp]; exact hf0)
      (by rw [← hp]; exact hl0),?_⟩
    simp [Same,GalilScaffoldPrepareControl.tape,hm,hp,hw,hs,hwk,hf]
  | startRun x hm0 hf0 =>
    refine ⟨_,.startRun x' (by rw [← hm]; exact hm0) (by rw [← hp]; exact hf0),?_⟩
    simp [Same,hm,hp,hw,hs,hwk,hf]

/-- Enabled ticks are deterministic. -/
theorem tick_unique {x y y' : GalilScaffoldPrepareControl.State} (h1 : GalilScaffoldPrepareControl.Tick true x y) (h2 : GalilScaffoldPrepareControl.Tick true x y') : y = y' := by
  cases h1 with
  | lowerBit x hm hp =>
    cases h2 with
    | lowerBit => rfl
    | lowerEnd _ _ hp' => rw [hp] at hp'; cases hp'
    | lowerLeft _ hm' | beginCopy _ hm' | copyBit _ _ hm' | copyEnd _ hm' | sourceLeft _ hm' | startRun _ hm' =>
      rw [hm] at hm'; cases hm'
  | lowerEnd x hm hp =>
    cases h2 with
    | lowerEnd => rfl
    | lowerBit _ _ hp' => rw [hp] at hp'; cases hp'
    | lowerLeft _ hm' | beginCopy _ hm' | copyBit _ _ hm' | copyEnd _ hm' | sourceLeft _ hm' | startRun _ hm' =>
      rw [hm] at hm'; cases hm'
  | lowerLeft x hm hf hl =>
    cases h2 with
    | lowerLeft => rfl
    | beginCopy _ _ hf' => exact absurd hf' hf
    | lowerBit _ hm' | lowerEnd _ hm' | copyBit _ _ hm' | copyEnd _ hm' | sourceLeft _ hm' | startRun _ hm' =>
      rw [hm] at hm'; cases hm'
  | beginCopy x hm hf =>
    cases h2 with
    | beginCopy => rfl
    | lowerLeft _ _ hf' => exact absurd hf hf'
    | lowerBit _ hm' | lowerEnd _ hm' | copyBit _ _ hm' | copyEnd _ hm' | sourceLeft _ hm' | startRun _ hm' =>
      rw [hm] at hm'; cases hm'
  | copyBit x a hm ha hw =>
    cases h2 with
    | copyBit _ a' _ ha' _ => rw [ha] at ha'; cases ha'; rfl
    | copyEnd _ _ he =>
      rcases he with he | he
      · rw [ha] at he; cases he
      · rw [hw] at he; cases he
    | lowerBit _ hm' | lowerEnd _ hm' | lowerLeft _ hm' | beginCopy _ hm' | sourceLeft _ hm' | startRun _ hm' =>
      rw [hm] at hm'; cases hm'
  | copyEnd x hm he =>
    cases h2 with
    | copyEnd => rfl
    | copyBit _ a _ ha hw =>
      rcases he with he | he
      · rw [ha] at he; cases he
      · rw [hw] at he; cases he
    | lowerBit _ hm' | lowerEnd _ hm' | lowerLeft _ hm' | beginCopy _ hm' | sourceLeft _ hm' | startRun _ hm' =>
      rw [hm] at hm'; cases hm'
  | sourceLeft x hm hf hl =>
    cases h2 with
    | sourceLeft => rfl
    | startRun _ _ hf' => exact absurd hf' hf
    | lowerBit _ hm' | lowerEnd _ hm' | lowerLeft _ hm' | beginCopy _ hm' | copyBit _ _ hm' | copyEnd _ hm' =>
      rw [hm] at hm'; cases hm'
  | startRun x hm hf =>
    cases h2 with
    | startRun => rfl
    | sourceLeft _ _ hf' => exact absurd hf hf'
    | lowerBit _ hm' | lowerEnd _ hm' | lowerLeft _ hm' | beginCopy _ hm' | copyBit _ _ hm' | copyEnd _ hm' =>
      rw [hm] at hm'; cases hm'

theorem run_unique {x y y' : GalilScaffoldPrepareControl.State} {n : ℕ} (h1 : GalilScaffoldPrepareControl.Run x (List.replicate n true) y)
    (h2 : GalilScaffoldPrepareControl.Run x (List.replicate n true) y') : y = y' := by
  induction n generalizing x with
  | zero => cases h1; cases h2; rfl
  | succ n ih =>
    rw [List.replicate_succ] at h1 h2
    cases h1 with
    | cons _ m _ _ _ ht hr =>
      cases h2 with
      | cons _ m' _ _ _ ht' hr' =>
        have := tick_unique ht ht'
        subst this
        exact ih hr hr'

/-- A fully enabled paced run is a plain run on every field but the debt. -/
theorem paced_same {x z : GalilScaffoldPrepareControl.State} (es : List (Bool × Bool)) (hall : ∀ e ∈ es, e.1 = true)
    (hr : GalilScaffoldPreparePaced.PacedRun x es z) :
    ∀ x', Same x x' → ∃ z', GalilScaffoldPrepareControl.Run x' (List.replicate es.length true) z' ∧ Same z z' := by
  induction hr with
  | nil x => intro x' h; exact ⟨x',.nil x',h⟩
  | cons x y z enabled advance es ht _ ih =>
    intro x' h
    have he : enabled = true := hall (enabled,advance) (by simp)
    subst he
    obtain ⟨y',hty,hsy⟩ := tick_same ht h
    have hsy' : Same (GalilScaffoldPreparePaced.afterAdvance advance y) y' :=
      same_trans (same_afterAdvance advance y) hsy
    obtain ⟨z',hrz,hsz⟩ := ih (fun e he => hall e (by simp [he])) y' hsy'
    refine ⟨z',?_,hsz⟩
    rw [List.length_cons,List.replicate_succ]
    exact .cons x' y' z' true _ hty hrz

/-- The paced preparation of the right length ends where `prepare_complete`
ends: in `run` mode with the prepared DP machine, on all fields but the debt. -/
theorem paced_prepared_mode {lower span : ℕ} {center : GalilScaffoldPlace.Place}
    {s p : GalilScaffoldPrepareControl.State} {bs : List Bool}
    (hp : GalilScaffoldPreparePaced.PacedPrepared (GalilScaffoldCounter.ofNat lower) center s bs p)
    (hspan : s.span = GalilScaffoldCounter.ofNat span)
    (hlen : bs.length = 2*lower+2*((GalilScaffoldPlace.stream center).take (span+1)).length+7) :
    p.mode = .run ∧
      p.program.config = GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream center).take (span+1)) lower ∧
      p.program.done = false := by
  obtain ⟨t,hprep,hmode,hconfig,hdone,hdebt,hfin⟩ :=
    GalilScaffoldPrepareControl.prepare_complete s lower span center hspan
  cases hp
  rename_i a as hr
  cases hprep
  rename_i hrun
  have hall : ∀ e ∈ (List.replicate as.length true).zip as, e.1 = true := by
    intro e he
    rcases e with ⟨e1,e2⟩
    exact List.eq_of_mem_replicate (List.of_mem_zip he).1
  obtain ⟨z',hrz,hsz⟩ := paced_same _ hall hr
    (GalilScaffoldPrepareControl.prepare s (GalilScaffoldCounter.ofNat lower) center)
    (same_afterAdvance a _)
  have hlen' : ((List.replicate as.length true).zip as).length =
      2*lower+2*((GalilScaffoldPlace.stream center).take (span+1)).length+6 := by
    simp only [List.length_zip,List.length_replicate,Nat.min_self]
    simp only [List.length_cons] at hlen
    omega
  rw [hlen'] at hrz
  have := run_unique hrz hrun
  subst this
  exact ⟨hsz.1.trans hmode,hsz.2.1 ▸ hconfig,hsz.2.1 ▸ hdone⟩

end Prep

#print axioms Prep.paced_prepared_mode

/-- The paced grow phase adds eight places of span per grow tick. -/
theorem paced_growing_span {s t : GalilScaffoldPrepareControl.State} {as : List Bool}
    (hr : GalilScaffoldStagePrepare.PacedGrowing s as t) :
    ∀ n, s.span = GalilScaffoldCounter.ofNat n → t.span = GalilScaffoldCounter.ofNat (n+8*as.length) := by
  induction hr with
  | stop s _ _ => intro n h; simpa using h
  | next s t a as _ _ _ ih =>
    intro n h
    have h' : (GalilScaffoldPreparePaced.afterAdvance a (GalilScaffoldStagePrepare.growStep s)).span =
        GalilScaffoldCounter.ofNat (n+8) := by
      cases a <;> simp [GalilScaffoldPreparePaced.afterAdvance,GalilScaffoldStagePrepare.growStep,h,
        GalilScaffoldStagePrepare.add_ofNat]
    have := ih (n+8) h'
    rw [this]
    congr 1
    simp only [List.length_cons]
    ring

/-- `first_stage_chain` with the run mode of the prepared state derived from
the paced preparation itself. -/
theorem first_stage_chain_run (as bs cs : List Bool) (es : List (Bool × Bool))
    (s : GalilScaffoldPrepareControl.State) (r radius : ℕ)
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (quarter : Fin 4)
    (hm : s.mode = .grow) (hw : s.work = GalilScaffoldCounter.ofNat (max r 1))
    (hs : s.span = GalilScaffoldCounter.ofNat 0)
    (hd : GalilScaffoldCounter.value s.debt = -(radius : ℤ))
    (hcanon : GalilScaffoldCounter.Canonical s.debt)
    (ha : as.length = max r 1)
    (hb : bs.length = 2*r+2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max r 1+1)).length+7)
    (hcs : cs.length = GalilScaffoldTimingCost.runBudget (8*max r 1))
    (he : as++bs++cs = GalilScaffoldAdvanceClock.advances 2048 2048 es)
    (hr : 3*radius ≤ 5*r) :
    let w := (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max r 1+1)
    ∃ u p used rest t v, GalilScaffoldStagePrepare.PacedGrowing s as u ∧
      GalilScaffoldPreparePaced.PacedPrepared (GalilScaffoldCounter.ofNat r) ⟨a :: ls,gap⟩ u bs p ∧
      p.mode = .run ∧
      cs = used++rest ∧
      GalilScaffoldSearchRun.SafeQuanta (GalilScaffoldStagePrepare.runState p quarter) p.program
        used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w r 0 (GalilScaffoldProgram.denote v) ∧
      (t.mode = .found →
        ∀ (rad : GalilScaffoldCounter.Counter), GalilScaffoldCounter.Canonical rad →
        ∀ (r0 : ℕ), GalilScaffoldCounter.value rad = r0 → 0 < r0 → ∀ (sm dm : Bool),
        ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
          GalilDpCorrect.Candidate w r h ∧ ys.length+1 = h) := by
  intro w
  obtain ⟨u,p,used,rest,t,v,hg,hp,hsplit,hq,hnr,hres,hchain⟩ :=
    first_stage_chain as bs cs es s r radius a ls rs qq gap cen hcen c hc quarter
      hm hw hs hd hcanon ha hb hcs he hr
  have huspan : u.span = GalilScaffoldCounter.ofNat (8*max r 1) := by
    have := paced_growing_span hg 0 hs
    rw [this,ha]; congr 1; omega
  have hpm := (Prep.paced_prepared_mode hp huspan hb).1
  exact ⟨u,p,used,rest,t,v,hg,hp,hpm,hsplit,hq,hnr,hres,fun hf => hchain hf hpm⟩

/-- A later search stage (`later_stage_safe`: double, paced preparation, DP
run under the clock/advance correspondence) feeding the chain. -/
theorem later_stage_chain (as bs cs : List Bool) (es : List (Bool × Bool))
    (s : GalilScaffoldPrepareControl.State) (lower clock : ℕ)
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (hm : s.mode = .double) (hw : s.work = GalilScaffoldCounter.ofNat as.length)
    (hs : s.span = GalilScaffoldCounter.ofNat 0)
    (hcanon : GalilScaffoldCounter.Canonical s.debt)
    (hd : 0 ≤ GalilScaffoldCounter.value s.debt ∨
      (-1 ≤ GalilScaffoldCounter.value s.debt ∧ clock = 2048))
    (ha : as.length % 4 = 0) (hn : 8 ≤ as.length) (hl : 4*lower ≤ as.length)
    (hb : bs.length = 2*lower+2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*as.length+1)).length+7)
    (hcs : cs.length = GalilScaffoldTimingCost.runBudget (2*as.length))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (he : as++bs++cs = GalilScaffoldAdvanceClock.advances 2048 clock es) :
    let w := (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*as.length+1)
    ∃ u p used rest t v,
      GalilScaffoldDouble.Run (GalilScaffoldStagePrepare.runState s 0) as u ∧ u.quarter = 0 ∧
      GalilScaffoldPreparePaced.PacedPrepared (GalilScaffoldCounter.ofNat lower) ⟨a :: ls,gap⟩
        (GalilScaffoldStagePrepare.restoreState s u) bs p ∧
      p.mode = .run ∧
      cs = used++rest ∧
      GalilScaffoldSearchRun.SafeQuanta (GalilScaffoldStagePrepare.runState p u.quarter) p.program
        used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      (t.mode = .found →
        ∀ (rad : GalilScaffoldCounter.Counter), GalilScaffoldCounter.Canonical rad →
        ∀ (r0 : ℕ), GalilScaffoldCounter.value rad = r0 → 0 < r0 → ∀ (sm dm : Bool),
        ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
          GalilDpCorrect.Candidate w lower h ∧ ys.length+1 = h) := by
  intro w
  obtain ⟨u,p,used,rest,t,v,hdr,hq0,hp,hsplit,hq,hnr,hres,_,_,_⟩ :=
    GalilScaffoldStagePrepare.later_stage_safe as bs cs es s lower clock ⟨a :: ls,gap⟩
      hm hw hs hcanon hd ha hn hl hb hcs hclock he
  have huspan : (GalilScaffoldStagePrepare.restoreState s u).span =
      GalilScaffoldCounter.ofNat (2*as.length) := by
    show u.span = _
    have := GalilScaffoldDouble.span_of_run hdr 0 (by simp [GalilScaffoldStagePrepare.runState,hs])
    simpa using this
  have hpm := (Prep.paced_prepared_mode hp huspan hb).1
  refine ⟨u,p,used,rest,t,v,hdr,hq0,hp,hpm,hsplit,hq,hnr,hres,?_⟩
  intro hfound rad hrc r0 hr0 hrp sm dm
  exact stage_found_supplied a ls rs qq gap cen hcen c hc (2*as.length) lower hq hpm hfound hres
    rad hrc r0 hr0 hrp sm dm

#print axioms first_stage_chain_run
#print axioms later_stage_chain

/-! ## After a restart: the search begins a grow stage

`restart` installs `SearchFinish.begin last radius` as the scheduler
(`restart_input_tick` exports its `grow` mode). That state is exactly the
entry of `first_stage_safe`: grow mode, `work = last`, empty span and the
initial debt `-radius`. Restoring it over any prepare-controller base state
therefore re-enters the staged search from `first_stage_chain_run`. -/

theorem initialDebt_value (radius : GalilScaffoldCounter.Counter) :
    GalilScaffoldCounter.value (GalilScaffoldSearchFinish.initialDebt radius) =
      -GalilScaffoldCounter.value radius := by
  simp [GalilScaffoldSearchFinish.initialDebt,GalilScaffoldCounter.value]

theorem initialDebt_canonical (radius : GalilScaffoldCounter.Counter)
    (h : GalilScaffoldCounter.Canonical radius) :
    GalilScaffoldCounter.Canonical (GalilScaffoldSearchFinish.initialDebt radius) := by
  unfold GalilScaffoldCounter.Canonical at *
  simp only [GalilScaffoldSearchFinish.initialDebt]
  exact h.symm

/-- The scheduler right after `Search.start` is a fresh grow stage. -/
theorem begin_entry (lower radius : GalilScaffoldCounter.Counter)
    (hc : GalilScaffoldCounter.Canonical lower) (k : ℕ) (hk : GalilScaffoldCounter.value lower = k)
    (hrc : GalilScaffoldCounter.Canonical radius)
    (r : ℕ) (hr : GalilScaffoldCounter.value radius = r) :
    let sch := GalilScaffoldSearchFinish.begin lower radius
    sch.mode = .grow ∧ sch.work = GalilScaffoldCounter.ofNat (max k 1) ∧
      sch.span = GalilScaffoldCounter.ofNat 0 ∧
      GalilScaffoldCounter.value sch.debt = -(r : ℤ) ∧
      GalilScaffoldCounter.Canonical sch.debt := by
  intro sch
  have hl : lower = GalilScaffoldCounter.ofNat k := GalilScaffoldChainCatch.canonical_nat lower hc k hk
  refine ⟨rfl,?_,rfl,?_,initialDebt_canonical radius hrc⟩
  · show (if GalilScaffoldCounter.zero lower then GalilScaffoldCounter.inc lower else lower) = _
    rw [hl]
    cases k with
    | zero => rfl
    | succ j =>
      have hz : GalilScaffoldCounter.zero (GalilScaffoldCounter.ofNat (j+1)) = false := rfl
      rw [hz,if_neg (by simp)]
      congr 1
      omega
  · show GalilScaffoldCounter.value (GalilScaffoldSearchFinish.initialDebt radius) = _
    rw [initialDebt_value,hr]

/-- After `ReplayStart`, `search.start(zero)` with the reset radius: the
scheduler is a grow stage with one unit of work and zero debt. -/
theorem replay_stage_entry :
    let sch := GalilScaffoldSearchFinish.begin (GalilScaffoldCounter.ofNat 0) GalilScaffoldCounter.reset
    sch.mode = .grow ∧ sch.work = GalilScaffoldCounter.ofNat 1 ∧
      sch.span = GalilScaffoldCounter.ofNat 0 ∧
      GalilScaffoldCounter.value sch.debt = 0 ∧ GalilScaffoldCounter.Canonical sch.debt := by
  have := begin_entry (GalilScaffoldCounter.ofNat 0) GalilScaffoldCounter.reset
    (GalilScaffoldCounter.ofNat_canonical 0) 0 (GalilScaffoldCounter.ofNat_value 0)
    (Or.inl rfl) 0 rfl
  simpa using this

/-- The staged search re-entered after a restart, from the restored
prepare-controller state, into the chain. -/
theorem restart_first_stage (b0 : GalilScaffoldPrepareControl.State)
    (lower radius : GalilScaffoldCounter.Counter)
    (hc : GalilScaffoldCounter.Canonical lower) (k : ℕ) (hk : GalilScaffoldCounter.value lower = k)
    (hpos : 0 < k) (hrc : GalilScaffoldCounter.Canonical radius)
    (rad : ℕ) (hrad : GalilScaffoldCounter.value radius = rad)
    (as bs cs : List Bool) (es : List (Bool × Bool))
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hcc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (quarter : Fin 4)
    (ha : as.length = max k 1)
    (hb : bs.length = 2*k+2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)).length+7)
    (hcs : cs.length = GalilScaffoldTimingCost.runBudget (8*max k 1))
    (he : as++bs++cs = GalilScaffoldAdvanceClock.advances 2048 2048 es)
    (hr : 3*rad ≤ 5*k) :
    let s := GalilScaffoldStagePrepare.restoreState b0 (GalilScaffoldSearchFinish.begin lower radius)
    let w := (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)
    ∃ u p used rest t v, GalilScaffoldStagePrepare.PacedGrowing s as u ∧
      GalilScaffoldPreparePaced.PacedPrepared (GalilScaffoldCounter.ofNat k) ⟨a :: ls,gap⟩ u bs p ∧
      p.mode = .run ∧
      cs = used++rest ∧
      GalilScaffoldSearchRun.SafeQuanta (GalilScaffoldStagePrepare.runState p quarter) p.program
        used t ⟨v,true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w k 0 (GalilScaffoldProgram.denote v) ∧
      (t.mode = .found →
        ∀ (rad' : GalilScaffoldCounter.Counter), GalilScaffoldCounter.Canonical rad' →
        ∀ (r0 : ℕ), GalilScaffoldCounter.value rad' = r0 → 0 < r0 → ∀ (sm dm : Bool),
        ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
          GalilDpCorrect.Candidate w k h ∧ ys.length+1 = h) := by
  intro s w
  obtain ⟨hm,hw,hs,hd,hcanon⟩ := begin_entry lower radius hc k hk hrc rad hrad
  exact first_stage_chain_run as bs cs es s k rad a ls rs qq gap cen hcen c hcc quarter
    hm hw hs hd hcanon ha hb hcs he hr

#print axioms restart_first_stage

/-- The restart tick installs `Search.start(last)` with the current scan
radius: the scheduler is `begin last radius` and the DP program is reset to
its entry. Only the scan heads see the arrival first. -/
theorem restart_input_tick_scheduler {n slots : ℕ} (entry delay : ℕ) (replaying trailing : Bool)
    (input : Option (Fin 2)) {s t : RestartState n slots}
    (h : restartInputTick entry delay replaying trailing input s = some t) :
    let arrived := receiveRestart s input
    t.search = GalilScaffoldSearchFinish.startSearch entry
      arrived.scan.watch.machine.control.last arrived.scan.radius arrived.search ∧
    t.search.scheduler = GalilScaffoldSearchFinish.begin
      arrived.scan.watch.machine.control.last arrived.scan.radius ∧
    t.search.program = GalilScaffoldRawTick.reset entry arrived.search.program := by
  intro arrived
  unfold restartInputTick restartScanTick at h
  obtain ⟨t0,ht0,rfl⟩ := Option.map_eq_some_iff.mp h
  unfold restart at ht0
  split at ht0
  · cases ht0
    exact ⟨rfl,rfl,rfl⟩
  · cases ht0

#print axioms restart_input_tick_scheduler

/-! ## The preparation on the heap-implemented program

`restart_input_tick` hands the search a heap machine that represents the
reset abstract program. The abstract preparation ticks write and move tapes
of the abstract machine; each is realised on the heap machine by
`written`/`moved` with a fresh cell, preserving representation. -/

namespace RawPrep

theorem written_heap {n slots : ℕ} (x : GalilScaffoldHeapProgram.Config n slots) (k : Fin n)
    (v : Fin 9) (pc : ℕ) : (GalilScaffoldHeapProgram.written x k v pc).heap = x.heap := rfl

theorem moved_heap_other {n slots : ℕ} (x : GalilScaffoldHeapProgram.Config n slots) (k : Fin n)
    (a : GalilScaffoldHeap.Address slots) (r : Bool) (pc : ℕ) (a' : GalilScaffoldHeap.Address slots)
    (h : a' ≠ a) : (GalilScaffoldHeapProgram.moved x k a r pc).heap a' = x.heap a' := by
  cases r <;> simp [GalilScaffoldHeapProgram.moved,GalilScaffoldHeapTape.right,
    GalilScaffoldHeapTape.left,GalilScaffoldHeap.put,Function.update_of_ne h]

theorem represents_write {n slots : ℕ} {x : GalilScaffoldHeapProgram.Config n slots}
    {u : GalilScaffoldProgram.Config n} (hr : GalilScaffoldHeapProgram.Represents x u)
    (k : Fin n) (v : Fin 9) :
    GalilScaffoldHeapProgram.Represents (GalilScaffoldHeapProgram.written x k v u.pc)
      (GalilScaffoldLoading.put u k (GalilScaffoldTape.write (u.tapes k) v)) :=
  GalilScaffoldHeapProgram.written_represents hr k v u.pc

theorem represents_write_right {n slots : ℕ} {x : GalilScaffoldHeapProgram.Config n slots}
    {u : GalilScaffoldProgram.Config n} (hr : GalilScaffoldHeapProgram.Represents x u)
    (k : Fin n) (v : Fin 9) (a : GalilScaffoldHeap.Address slots) (hf : x.heap a = none) :
    GalilScaffoldHeapProgram.Represents
      (GalilScaffoldHeapProgram.moved (GalilScaffoldHeapProgram.written x k v u.pc) k a true u.pc)
      (GalilScaffoldLoading.put u k (GalilScaffoldTape.moveRight (GalilScaffoldTape.write (u.tapes k) v))) := by
  have h1 := GalilScaffoldHeapProgram.written_represents hr k v u.pc
  have h2 := GalilScaffoldHeapProgram.moved_right h1 k a hf u.pc
  simp only [GalilScaffoldProgram.changed,Function.update_self] at h2
  convert h2 using 1
  simp [GalilScaffoldLoading.put,GalilScaffoldProgram.changed,Function.update_idem]

theorem represents_left {n slots : ℕ} {x : GalilScaffoldHeapProgram.Config n slots}
    {u : GalilScaffoldProgram.Config n} (hr : GalilScaffoldHeapProgram.Represents x u)
    (k : Fin n) (a : GalilScaffoldHeap.Address slots) (hf : x.heap a = none)
    (legal : (u.tapes k).left ≠ []) :
    GalilScaffoldHeapProgram.Represents (GalilScaffoldHeapProgram.moved x k a false u.pc)
      (GalilScaffoldLoading.put u k (GalilScaffoldTape.moveLeft (u.tapes k))) :=
  (GalilScaffoldHeapProgram.moved_left hr k a hf u.pc legal).2

theorem represents_start {n slots : ℕ} {x : GalilScaffoldHeapProgram.Config n slots}
    {u : GalilScaffoldProgram.Config n} (hr : GalilScaffoldHeapProgram.Represents x u) (pc : ℕ) :
    GalilScaffoldHeapProgram.Represents ⟨x.heap,pc,x.tapes⟩ {u with pc := pc} :=
  ⟨rfl,hr.2⟩

theorem moved_finite {n slots : ℕ} (x : GalilScaffoldHeapProgram.Config n slots) (k : Fin n)
    (a : GalilScaffoldHeap.Address slots) (r : Bool) (pc : ℕ)
    (h : GalilScaffoldHeapProgram.FiniteHeap x.heap) :
    GalilScaffoldHeapProgram.FiniteHeap (GalilScaffoldHeapProgram.moved x k a r pc).heap := by
  cases r <;> simp only [GalilScaffoldHeapProgram.moved,GalilScaffoldHeapTape.right,
    GalilScaffoldHeapTape.left,if_true,if_false,Bool.false_eq_true] <;>
    exact GalilScaffoldHeapProgram.put_finite h _ _

/-- A finite heap has any number of distinct fresh cells. -/
theorem fresh_addresses {slots : ℕ} (h : GalilScaffoldHeap.Heap slots (Fin 9))
    (hh : GalilScaffoldHeapProgram.FiniteHeap h) (hs : 0 < slots) (n : ℕ) :
    ∃ addresses : List (GalilScaffoldHeap.Address slots), addresses.length = n ∧
      addresses.Nodup ∧ ∀ a ∈ addresses, h a = none := by
  obtain ⟨bound,hb⟩ := hh
  refine ⟨(List.range n).map (fun i => (bound+i,⟨0,hs⟩)),by simp,?_,?_⟩
  · refine List.Nodup.map ?_ List.nodup_range
    intro i j hij
    simp only [Prod.mk.injEq] at hij
    omega
  · intro a ha
    simp only [List.mem_map,List.mem_range] at ha
    obtain ⟨i,_,rfl⟩ := ha
    exact hb _ (by simp)

/-- One abstract preparation tick is realised on the heap machine with at
most one fresh cell, touching no other cell. -/
theorem prepare_tick_raw {slots : ℕ} {b : Bool} {x y : GalilScaffoldPrepareControl.State}
    (ht : GalilScaffoldPrepareControl.Tick b x y)
    (raw : GalilScaffoldRawTick.Machine 12 slots) (hr : GalilScaffoldRawTick.Represents raw x.program)
    (a : GalilScaffoldHeap.Address slots) (hf : raw.config.heap a = none) :
    ∃ raw' : GalilScaffoldRawTick.Machine 12 slots, GalilScaffoldRawTick.Represents raw' y.program ∧
      (∀ a', a' ≠ a → raw'.config.heap a' = raw.config.heap a') ∧
      (GalilScaffoldHeapProgram.FiniteHeap raw.config.heap →
        GalilScaffoldHeapProgram.FiniteHeap raw'.config.heap) := by
  obtain ⟨hc,hd⟩ := hr
  cases ht with
  | idle x => exact ⟨raw,⟨hc,hd⟩,fun _ _ => rfl,fun h => h⟩
  | lowerBit x _ _ =>
    refine ⟨⟨GalilScaffoldHeapProgram.moved
      (GalilScaffoldHeapProgram.written raw.config 10 8 x.program.config.pc) 10 a true
      x.program.config.pc,raw.done⟩,⟨represents_write_right hc 10 8 a hf,hd⟩,?_,
      moved_finite (GalilScaffoldHeapProgram.written raw.config 10 8 x.program.config.pc) 10 a true
        x.program.config.pc⟩
    intro a' ha'
    rw [moved_heap_other,written_heap]; exact ha'
  | lowerEnd x _ _ =>
    exact ⟨⟨GalilScaffoldHeapProgram.written raw.config 10 5 x.program.config.pc,raw.done⟩,
      ⟨represents_write hc 10 5,hd⟩,fun _ _ => rfl,fun h => h⟩
  | lowerLeft x _ _ hl =>
    refine ⟨⟨GalilScaffoldHeapProgram.moved raw.config 10 a false x.program.config.pc,raw.done⟩,
      ⟨represents_left hc 10 a hf hl,hd⟩,?_,moved_finite _ _ _ _ _⟩
    intro a' ha'
    rw [moved_heap_other]; exact ha'
  | beginCopy x _ _ =>
    refine ⟨⟨GalilScaffoldHeapProgram.moved
      (GalilScaffoldHeapProgram.written raw.config 7 4 x.program.config.pc) 7 a true
      x.program.config.pc,raw.done⟩,⟨represents_write_right hc 7 4 a hf,hd⟩,?_,
      moved_finite (GalilScaffoldHeapProgram.written raw.config 7 4 x.program.config.pc) 7 a true
        x.program.config.pc⟩
    intro a' ha'
    rw [moved_heap_other,written_heap]; exact ha'
  | copyBit x sym _ _ _ =>
    refine ⟨⟨GalilScaffoldHeapProgram.moved
      (GalilScaffoldHeapProgram.written raw.config 7 (GalilFppPreparation.symbol sym) x.program.config.pc)
      7 a true x.program.config.pc,raw.done⟩,
      ⟨represents_write_right hc 7 (GalilFppPreparation.symbol sym) a hf,hd⟩,?_,
      moved_finite (GalilScaffoldHeapProgram.written raw.config 7 (GalilFppPreparation.symbol sym)
        x.program.config.pc) 7 a true x.program.config.pc⟩
    intro a' ha'
    rw [moved_heap_other,written_heap]; exact ha'
  | copyEnd x _ _ =>
    exact ⟨⟨GalilScaffoldHeapProgram.written raw.config 7 5 x.program.config.pc,raw.done⟩,
      ⟨represents_write hc 7 5,hd⟩,fun _ _ => rfl,fun h => h⟩
  | sourceLeft x _ _ hl =>
    refine ⟨⟨GalilScaffoldHeapProgram.moved raw.config 7 a false x.program.config.pc,raw.done⟩,
      ⟨represents_left hc 7 a hf hl,hd⟩,?_,moved_finite _ _ _ _ _⟩
    intro a' ha'
    rw [moved_heap_other]; exact ha'
  | startRun x _ _ =>
    exact ⟨⟨⟨raw.config.heap,320,raw.config.tapes⟩,false⟩,⟨represents_start hc 320,rfl⟩,
      fun _ _ => rfl,fun h => h⟩

/-- A preparation run is realised on the heap machine along any list of
distinct fresh cells, one per tick. -/
theorem prepare_run_raw {slots : ℕ} {x y : GalilScaffoldPrepareControl.State} {bs : List Bool}
    (hrun : GalilScaffoldPrepareControl.Run x bs y) :
    ∀ (raw : GalilScaffoldRawTick.Machine 12 slots), GalilScaffoldRawTick.Represents raw x.program →
    ∀ (addresses : List (GalilScaffoldHeap.Address slots)), addresses.length = bs.length →
      addresses.Nodup → (∀ a ∈ addresses, raw.config.heap a = none) →
      ∃ raw' : GalilScaffoldRawTick.Machine 12 slots, GalilScaffoldRawTick.Represents raw' y.program ∧
        (GalilScaffoldHeapProgram.FiniteHeap raw.config.heap →
          GalilScaffoldHeapProgram.FiniteHeap raw'.config.heap) := by
  induction hrun with
  | nil x => intro raw hr _ _ _ _; exact ⟨raw,hr,fun h => h⟩
  | cons x y z b bs ht _ ih =>
    intro raw hr addresses hlen hnodup hfresh
    cases addresses with
    | nil => simp at hlen
    | cons a rest =>
      obtain ⟨raw1,hr1,hframe,hfin1⟩ := prepare_tick_raw ht raw hr a (hfresh a (by simp))
      obtain ⟨raw',hr',hfin'⟩ := ih raw1 hr1 rest (by simpa using hlen) (List.nodup_cons.mp hnodup).2
        (by
          intro a' ha'
          have hne : a' ≠ a := by
            intro h; subst h
            exact (List.nodup_cons.mp hnodup).1 ha'
          rw [hframe a' hne]
          exact hfresh a' (by simp [ha']))
      exact ⟨raw',hr',fun h => hfin' (hfin1 h)⟩

/-- The prepare dispatch (`Search.start`'s program reset followed by LEFT on
LOWER) on the heap machine: `RawTick.reset` then one write-right with a fresh
cell. -/
theorem prepare_raw {slots : ℕ} (x : GalilScaffoldPrepareControl.State)
    (lower : GalilScaffoldCounter.Counter) (center : GalilScaffoldPlace.Place)
    (raw : GalilScaffoldRawTick.Machine 12 slots)
    (a : GalilScaffoldHeap.Address slots) (hf : raw.config.heap a = none) :
    ∃ raw' : GalilScaffoldRawTick.Machine 12 slots,
      GalilScaffoldRawTick.Represents raw'
        (GalilScaffoldPrepareControl.prepare x lower center).program ∧
      (∀ a', a' ≠ a → raw'.config.heap a' = raw.config.heap a') ∧
      (GalilScaffoldHeapProgram.FiniteHeap raw.config.heap →
        GalilScaffoldHeapProgram.FiniteHeap raw'.config.heap) := by
  have hreset := GalilScaffoldRawTick.reset_represents 320 raw
  obtain ⟨hc,hd⟩ := hreset
  have hf' : (GalilScaffoldRawTick.reset 320 raw).config.heap a = none := by
    rw [GalilScaffoldRawTick.reset_heap]; exact hf
  refine ⟨⟨GalilScaffoldHeapProgram.moved
    (GalilScaffoldHeapProgram.written (GalilScaffoldRawTick.reset 320 raw).config 10 4 320) 10 a true 320,
    true⟩,⟨?_,rfl⟩,?_,?_⟩
  · have := represents_write_right hc 10 4 a hf'
    simpa [GalilScaffoldPrepareControl.prepare,GalilScaffoldControl.reset] using this
  · intro a' ha'
    rw [moved_heap_other,written_heap,GalilScaffoldRawTick.reset_heap]; exact ha'
  · intro h
    apply moved_finite
    show GalilScaffoldHeapProgram.FiniteHeap (GalilScaffoldRawTick.reset 320 raw).config.heap
    rw [GalilScaffoldRawTick.reset_heap]; exact h

/-- A prepared run (`prepare` dispatch then the four preparation phases) is
realised on the heap machine along `n+1` distinct fresh cells. -/
theorem prepared_run_raw {slots : ℕ} {lower : GalilScaffoldCounter.Counter}
    {center : GalilScaffoldPlace.Place} {s t : GalilScaffoldPrepareControl.State} {n : ℕ}
    (hp : GalilScaffoldPrepareControl.PreparedRun lower center s n t)
    (raw : GalilScaffoldRawTick.Machine 12 slots)
    (addresses : List (GalilScaffoldHeap.Address slots)) (hlen : addresses.length = n)
    (hnodup : addresses.Nodup) (hfresh : ∀ a ∈ addresses, raw.config.heap a = none) :
    ∃ raw' : GalilScaffoldRawTick.Machine 12 slots, GalilScaffoldRawTick.Represents raw' t.program ∧
      (GalilScaffoldHeapProgram.FiniteHeap raw.config.heap →
        GalilScaffoldHeapProgram.FiniteHeap raw'.config.heap) := by
  cases hp
  rename_i hrun
  cases addresses with
  | nil => simp at hlen
  | cons a rest =>
    obtain ⟨raw1,hr1,hframe,hfin1⟩ := prepare_raw s lower center raw a (hfresh a (by simp))
    obtain ⟨raw',hr',hfin'⟩ := prepare_run_raw hrun raw1 hr1 rest (by simpa using hlen)
      (List.nodup_cons.mp hnodup).2
      (by
        intro a' ha'
        have hne : a' ≠ a := by
          intro h; subst h
          exact (List.nodup_cons.mp hnodup).1 ha'
        rw [hframe a' hne]
        exact hfresh a' (by simp [ha']))
    exact ⟨raw',hr',fun h => hfin' (hfin1 h)⟩

/-- A fully enabled paced run is realised like the plain run: the pacing
only touches the debt, never the program. -/
theorem paced_run_raw {slots : ℕ} {x z : GalilScaffoldPrepareControl.State}
    {es : List (Bool × Bool)} (hall : ∀ e ∈ es, e.1 = true)
    (hr : GalilScaffoldPreparePaced.PacedRun x es z) :
    ∀ (raw : GalilScaffoldRawTick.Machine 12 slots), GalilScaffoldRawTick.Represents raw x.program →
    ∀ (addresses : List (GalilScaffoldHeap.Address slots)), addresses.length = es.length →
      addresses.Nodup → (∀ a ∈ addresses, raw.config.heap a = none) →
      ∃ raw' : GalilScaffoldRawTick.Machine 12 slots, GalilScaffoldRawTick.Represents raw' z.program ∧
        (GalilScaffoldHeapProgram.FiniteHeap raw.config.heap →
          GalilScaffoldHeapProgram.FiniteHeap raw'.config.heap) := by
  induction hr with
  | nil x => intro raw hr _ _ _ _; exact ⟨raw,hr,fun h => h⟩
  | cons x y z enabled advance es ht _ ih =>
    intro raw hr addresses hlen hnodup hfresh
    cases addresses with
    | nil => simp at hlen
    | cons a rest =>
      obtain ⟨raw1,hr1,hframe,hfin1⟩ := prepare_tick_raw ht raw hr a (hfresh a (by simp))
      have hr1' : GalilScaffoldRawTick.Represents raw1
          (GalilScaffoldPreparePaced.afterAdvance advance y).program := by
        cases advance <;> simpa [GalilScaffoldPreparePaced.afterAdvance] using hr1
      obtain ⟨raw',hr',hfin'⟩ := ih (fun e he => hall e (by simp [he])) raw1 hr1' rest
        (by simpa using hlen) (List.nodup_cons.mp hnodup).2
        (by
          intro a' ha'
          have hne : a' ≠ a := by
            intro h; subst h
            exact (List.nodup_cons.mp hnodup).1 ha'
          rw [hframe a' hne]
          exact hfresh a' (by simp [ha']))
      exact ⟨raw',hr',fun h => hfin' (hfin1 h)⟩

/-- The paced preparation (`PacedPrepared`) on the heap machine. -/
theorem paced_prepared_raw {slots : ℕ} {lower : GalilScaffoldCounter.Counter}
    {center : GalilScaffoldPlace.Place} {s p : GalilScaffoldPrepareControl.State} {bs : List Bool}
    (hp : GalilScaffoldPreparePaced.PacedPrepared lower center s bs p)
    (raw : GalilScaffoldRawTick.Machine 12 slots)
    (addresses : List (GalilScaffoldHeap.Address slots)) (hlen : addresses.length = bs.length)
    (hnodup : addresses.Nodup) (hfresh : ∀ a ∈ addresses, raw.config.heap a = none) :
    ∃ raw' : GalilScaffoldRawTick.Machine 12 slots, GalilScaffoldRawTick.Represents raw' p.program ∧
      (GalilScaffoldHeapProgram.FiniteHeap raw.config.heap →
        GalilScaffoldHeapProgram.FiniteHeap raw'.config.heap) := by
  cases hp
  rename_i a as hr
  cases addresses with
  | nil => simp at hlen
  | cons a0 rest =>
    obtain ⟨raw1,hr1,hframe,hfin1⟩ := prepare_raw s lower center raw a0 (hfresh a0 (by simp))
    have hr1' : GalilScaffoldRawTick.Represents raw1
        (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare s lower center)).program := by
      cases a <;> simpa [GalilScaffoldPreparePaced.afterAdvance] using hr1
    have hall : ∀ e ∈ (List.replicate as.length true).zip as, e.1 = true := by
      intro e he
      rcases e with ⟨e1,e2⟩
      exact List.eq_of_mem_replicate (List.of_mem_zip he).1
    obtain ⟨raw',hr',hfin'⟩ := paced_run_raw hall hr raw1 hr1' rest
      (by simp only [List.length_zip,List.length_replicate,Nat.min_self]
          simp only [List.length_cons] at hlen; omega)
      (List.nodup_cons.mp hnodup).2
      (by
        intro a' ha'
        have hne : a' ≠ a0 := by
          intro h; subst h
          exact (List.nodup_cons.mp hnodup).1 ha'
        rw [hframe a' hne]
        exact hfresh a' (by simp [ha']))
    exact ⟨raw',hr',fun h => hfin' (hfin1 h)⟩

end RawPrep

#print axioms RawPrep.prepare_run_raw
#print axioms RawPrep.prepared_run_raw
#print axioms RawPrep.paced_prepared_raw

/-! ## The DP run on the heap machine

The machine sequence of a safe call sequence is a `Control.Run` over the
effective enabled flags (`b && mode = run`); the quanta run concatenates them.
`RawSchedule.realize_run` then realises it on the heap machine along fresh
cells, keeping the representation of the halted DP machine. -/

theorem safe_calls_control_run {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (h : GalilScaffoldSearchRun.SafeCalls s x bs t y) :
    ∃ es : List Bool, es.length = bs.length ∧ GalilScaffoldControl.Run GalilDpCode.code x es y := by
  induction h with
  | nil s x => exact ⟨[],rfl,.nil x⟩
  | cons s x y z b bs t ht _ _ ih =>
    obtain ⟨es,hlen,hrun⟩ := ih
    exact ⟨(b && decide (s.mode = .run)) :: es,by simp [hlen],.cons x y z _ es ht hrun⟩

theorem control_run_append {n : ℕ} {code : List (GalilFppWide.Instruction n)}
    {x y z : GalilScaffoldControl.Machine n} {as bs : List Bool}
    (h1 : GalilScaffoldControl.Run code x as y) (h2 : GalilScaffoldControl.Run code y bs z) :
    GalilScaffoldControl.Run code x (as ++ bs) z := by
  induction h1 with
  | nil x => exact h2
  | cons x y _ b as hs _ ih => exact .cons x y _ b _ hs (ih h2)

theorem safe_quanta_control_run {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (h : GalilScaffoldSearchRun.SafeQuanta s x as t y) :
    ∃ es : List Bool, es.length = 64*as.length ∧ GalilScaffoldControl.Run GalilDpCode.code x es y := by
  induction h with
  | nil s x => exact ⟨[],by simp,.nil x⟩
  | cons s u t x y z a as _ hq _ ih =>
    obtain ⟨es1,hl1,hr1⟩ := safe_calls_control_run hq
    obtain ⟨es2,hl2,hr2⟩ := ih
    refine ⟨es1 ++ es2,?_,control_run_append hr1 hr2⟩
    simp [hl1,hl2]; ring

theorem dp_wellFormed_lookup : ∀ (pc : ℕ) (i : GalilFppWide.Instruction 12),
    GalilDpCode.code[pc]? = some i → GalilScaffoldNextPc.WellFormed i :=
  fun _ i hi => GalilScaffoldNextPc.dp_wellFormed i (List.mem_of_getElem? hi)

/-- The actual DP quanta run, realised on the heap machine. -/
theorem quanta_raw {slots : ℕ} {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (h : GalilScaffoldSearchRun.SafeQuanta s x as t y)
    (raw : GalilScaffoldRawTick.Machine 12 slots) (hr : GalilScaffoldRawTick.Represents raw x)
    (addresses : List (GalilScaffoldHeap.Address slots)) (hlen : addresses.length = 64*as.length)
    (hnodup : addresses.Nodup) (hfresh : ∀ a ∈ addresses, raw.config.heap a = none) :
    ∃ (es : List Bool) (raw' : GalilScaffoldRawTick.Machine 12 slots),
      es.length = 64*as.length ∧
      GalilScaffoldRawSchedule.Run GalilDpCode.code raw es addresses raw' ∧
      GalilScaffoldRawTick.Represents raw' y := by
  obtain ⟨es,hl,hrun⟩ := safe_quanta_control_run h
  obtain ⟨raw',hraw,hrep⟩ := GalilScaffoldRawSchedule.realize_run hrun dp_wellFormed_lookup raw hr
    addresses (by rw [hlen,hl]) hnodup hfresh
  exact ⟨es,raw',hl,hraw,hrep⟩

#print axioms quanta_raw

/-- The grow phase never touches the program. -/
theorem paced_growing_program {s t : GalilScaffoldPrepareControl.State} {as : List Bool}
    (hr : GalilScaffoldStagePrepare.PacedGrowing s as t) : t.program = s.program := by
  induction hr with
  | stop s _ _ => rfl
  | next s t a as _ _ _ ih =>
    rw [ih]
    cases a <;> rfl

/-- A whole search stage on the heap machine: from a finite heap machine
representing the stage's program, the paced preparation and the DP quanta run
are realised along fresh cells, ending in a machine representing the halted
DP machine `⟨v,true⟩`. -/
theorem stage_raw {slots : ℕ} (hs : 0 < slots)
    {s u p : GalilScaffoldPrepareControl.State} {as bs used : List Bool}
    {lower : GalilScaffoldCounter.Counter} {center : GalilScaffoldPlace.Place}
    {q : Fin 4} {t : GalilScaffoldSearchFinish.State} {v : GalilScaffoldProgram.Config 12}
    (hg : GalilScaffoldStagePrepare.PacedGrowing s as u)
    (hp : GalilScaffoldPreparePaced.PacedPrepared lower center u bs p)
    (hq : GalilScaffoldSearchRun.SafeQuanta (GalilScaffoldStagePrepare.runState p q) p.program
      used t ⟨v,true⟩)
    (raw : GalilScaffoldRawTick.Machine 12 slots) (hr : GalilScaffoldRawTick.Represents raw s.program)
    (hfin : GalilScaffoldHeapProgram.FiniteHeap raw.config.heap) :
    ∃ (rawP rawV : GalilScaffoldRawTick.Machine 12 slots) (es : List Bool)
      (addresses : List (GalilScaffoldHeap.Address slots)),
      GalilScaffoldRawTick.Represents rawP p.program ∧
      GalilScaffoldHeapProgram.FiniteHeap rawP.config.heap ∧
      es.length = 64*used.length ∧
      GalilScaffoldRawSchedule.Run GalilDpCode.code rawP es addresses rawV ∧
      GalilScaffoldRawTick.Represents rawV ⟨v,true⟩ := by
  have hru : GalilScaffoldRawTick.Represents raw u.program := by
    rw [paced_growing_program hg]; exact hr
  obtain ⟨addr1,hl1,hn1,hf1⟩ := RawPrep.fresh_addresses raw.config.heap hfin hs bs.length
  obtain ⟨rawP,hrP,hfinP⟩ := RawPrep.paced_prepared_raw hp raw addr1 hl1 hn1 hf1
  have hfinP' := hfinP hfin
  obtain ⟨addr2,hl2,hn2,hf2⟩ := RawPrep.fresh_addresses rawP.config.heap hfinP' hs (64*used.length)
  obtain ⟨es,rawV,hes,hrun,hrV⟩ := quanta_raw hq rawP hrP addr2 hl2 hn2 hf2
  exact ⟨rawP,rawV,es,addr2,hrP,hfinP',hes,hrun,hrV⟩

#print axioms stage_raw

/-! ## Scala's allocator

Scala allocates cells per tick node from a block of tags. A `Bounded`
allocator only holds cells at nodes up to the current one, so its heap is
finite and every later node's block is fresh. -/

theorem bounded_finite {slots : ℕ} (s : GalilScaffoldHeap.Allocator slots (Fin 9))
    (hb : GalilScaffoldHeap.Bounded s) : GalilScaffoldHeapProgram.FiniteHeap s.heap := by
  refine ⟨s.node+1,?_⟩
  intro a ha
  cases he : s.heap a with
  | none => rfl
  | some c =>
    have := hb a c he
    omega

/-- The blocks of `m` consecutive nodes after the allocator's node: `64` cells
per node, all distinct and fresh. -/
theorem blocks_fresh {slots : ℕ} (s : GalilScaffoldHeap.Allocator slots (Fin 9))
    (hb : GalilScaffoldHeap.Bounded s) (hq : 64 ≤ slots) (m : ℕ) :
    let addresses := (List.range m).flatMap
      (fun i => GalilScaffoldRawSchedule.block (s.node+1+i) 64 slots hq)
    addresses.length = 64*m ∧ addresses.Nodup ∧ ∀ a ∈ addresses, s.heap a = none := by
  intro addresses
  refine ⟨?_,?_,?_⟩
  · simp [addresses,List.length_flatMap,GalilScaffoldRawSchedule.block_length]; ring
  · apply List.nodup_flatMap.mpr
    refine ⟨fun i _ => GalilScaffoldRawSchedule.block_nodup _ _ _ _,?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_range]
    intro a ha1 ha2
    have h1 := (GalilScaffoldRawSchedule.block_prefix ha1).1
    have h2 := (GalilScaffoldRawSchedule.block_prefix ha2).1
    omega
  · intro a ha
    simp only [addresses,List.mem_flatMap,List.mem_range] at ha
    obtain ⟨i,_,hai⟩ := ha
    have h1 := (GalilScaffoldRawSchedule.block_prefix hai).1
    cases he : s.heap a with
    | none => rfl
    | some c =>
      have := hb a c he
      omega

#print axioms blocks_fresh

/-! ## One tick for the scan and the chain

Scala `stepScan` counts the match clock down on every available tick and
compares when it reaches one; the compare that matches grows the scan and is
the chain's outer `matched` event of the same tick. The joint relation below
fixes that identification: the event list seen by the chain (`Watch.Run`) and
by the scan (`ScanEvents`) is one and the same, and its compare count and
final clock are those of `GalilScaffoldMatchClock.run`. Shift and fallback
compares are the other branches, handled above. -/

structure JointState where
  left : PlaceHead
  right : PlaceHead
  watch : GalilScaffoldChainWatch.State
  clock : ℕ

inductive JointTick (delay : ℕ) : Bool → JointState → JointState → Prop
  | idle (s : JointState) (w' : GalilScaffoldChainWatch.State)
      (ht : GalilScaffoldChainWatch.Tick s.watch false w') :
      JointTick delay false s ⟨s.left,s.right,w',s.clock⟩
  | count (s : JointState) (w' : GalilScaffoldChainWatch.State) (hc : s.clock ≠ 1)
      (ht : GalilScaffoldChainWatch.Tick s.watch false w') :
      JointTick delay true s ⟨s.left,s.right,w',s.clock-1⟩
  | compare (s : JointState) (w' : GalilScaffoldChainWatch.State) (hc : s.clock = 1)
      (hr : canRight s.right)
      (hm : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
        GalilScaffoldInputHead.read (right s.right))
      (ht : GalilScaffoldChainWatch.Tick s.watch true w') :
      JointTick delay true s ⟨GalilScaffoldInputHead.left s.left,right s.right,w',delay⟩

inductive JointRun (delay : ℕ) : JointState → List Bool → JointState → Prop
  | nil (s : JointState) : JointRun delay s [] s
  | cons (s m t : JointState) (a : Bool) (as : List Bool)
      (ht : JointTick delay a s m) (hr : JointRun delay m as t) : JointRun delay s (a :: as) t

/-- The joint run yields one event list for both the chain and the scan. -/
theorem joint_run_events {delay : ℕ} {s t : JointState} {avail : List Bool}
    (hr : JointRun delay s avail t) :
    ∃ events : List Bool, events.length = avail.length ∧
      GalilScaffoldChainWatch.Run s.watch events t.watch ∧
      (∀ (raw : List (Fin 2)) (c r : ℕ), ScanEvents raw c r s.left s.right events t.left t.right) ∧
      events.count true = (GalilScaffoldMatchClock.run delay s.clock avail).2 ∧
      t.clock = (GalilScaffoldMatchClock.run delay s.clock avail).1 := by
  induction hr with
  | nil s =>
    exact ⟨[],rfl,.stop _,fun raw c r => .stop r s.left s.right,by simp [GalilScaffoldMatchClock.run],
      by simp [GalilScaffoldMatchClock.run]⟩
  | cons s m t a as ht _ ih =>
    obtain ⟨events,hlen,hw,hs,hcount,hclock⟩ := ih
    cases ht with
    | idle _ w' htw =>
      refine ⟨false :: events,by simp [hlen],.next htw hw,fun raw c r => .skip r _ _ (hs raw c r),?_,?_⟩
      · simpa [GalilScaffoldMatchClock.run] using hcount
      · simpa [GalilScaffoldMatchClock.run] using hclock
    | count _ w' hc htw =>
      refine ⟨false :: events,by simp [hlen],.next htw hw,fun raw c r => .skip r _ _ (hs raw c r),?_,?_⟩
      · simp only [GalilScaffoldMatchClock.run,if_neg hc]
        simpa using hcount
      · simp only [GalilScaffoldMatchClock.run,if_neg hc]
        exact hclock
    | compare _ w' hc hcr hm htw =>
      refine ⟨true :: events,by simp [hlen],.next htw hw,
        fun raw c r => .matched r _ _ hcr hm (hs raw c (r+1)),?_,?_⟩
      · simp only [GalilScaffoldMatchClock.run,if_pos hc,List.count_cons_self]
        simpa using hcount
      · simp only [GalilScaffoldMatchClock.run,if_pos hc]
        exact hclock

#print axioms joint_run_events

/-- `watch_shift_supply` from the joint run: the chain's watch run and the
scan's growth come from the same ticks, the lag accounting is the match
clock's compare count, and phase `4` follows once four semiperiods are in. -/
theorem joint_shift_supply {raw : List (Fin 2)} (cen : PlaceHead) (c : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : GalilScaffoldCounter.Counter)
    (r0 : ℕ) (hr0 : GalilScaffoldCounter.value radius = r0)
    (sm dm : Bool) (bs cs : List Bool)
    (hcanon : GalilScaffoldCounter.Canonical
      (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm bs cs)).lag)
    (hmcanon : GalilScaffoldCounter.Canonical
      (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm bs cs)).margin)
    {l0 rr0 l1 rr1 : PlaceHead}
    (hi0 : ScanInvariant raw (position cen) r0 l0 rr0)
    (hprep : ScanEvents raw (position cen) r0 l0 rr0 (sm :: (bs ++ dm :: cs)) l1 rr1)
    {delay clock0 : ℕ} {avail : List Bool} {t : JointState}
    (hjoint : JointRun delay ⟨l1,rr1,watchStart cen c ys b
      (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm bs cs)),clock0⟩ avail t)
    (hexhausted : GalilScaffoldCounter.zero t.watch.lag = true) :
    let final := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
      (GalilScaffoldChainCredits.prepEvents sm dm bs cs)
    let s0 := watchStart cen c ys b final
    let initialRadius := r0+(sm :: (bs ++ dm :: cs)).count true
    let scanRadius := initialRadius+(GalilScaffoldMatchClock.run delay clock0 avail).2
    ∃ events : List Bool, events.length = avail.length ∧
      events.count true = (GalilScaffoldMatchClock.run delay clock0 avail).2 ∧
      GalilScaffoldChainWatch.Run s0 events t.watch ∧
      GalilScaffoldCounter.value s0.lag = initialRadius ∧
      GalilScaffoldCounter.value t.watch.machine.control.distance = scanRadius ∧
      (4*(ys.length+1) ≤ scanRadius → t.watch.machine.control.phase = 4) ∧
      ScanInvariant raw (position cen) scanRadius t.left t.right ∧
      t.clock = (GalilScaffoldMatchClock.run delay clock0 avail).1 := by
  intro final s0 initialRadius scanRadius
  obtain ⟨events,hlen,hw,hs,hcount,hclock⟩ := joint_run_events hjoint
  have hpv := (GalilScaffoldChainCredits.prep_value radius sm dm bs cs).2
  have hlagv : GalilScaffoldCounter.value s0.lag = initialRadius := by
    show GalilScaffoldCounter.value final.lag = _
    rw [hpv,hr0]; simp [initialRadius]
  have hcan : GalilScaffoldChainWatch.CanonicalState s0 := ⟨hcanon,hmcanon⟩
  have hcan' := GalilScaffoldChainWatch.run_canonical hw hcan
  have hlag0 : GalilScaffoldCounter.value t.watch.lag = 0 :=
    (GalilScaffoldCounter.zero_iff _ hcan'.1).1 hexhausted
  have hp := watch_progress hw
  have hz0 : GalilScaffoldCounter.value s0.machine.control.distance = 0 := rfl
  rw [hz0,hlag0,hlagv] at hp
  have hdist : GalilScaffoldCounter.value t.watch.machine.control.distance = scanRadius := by
    simp only [scanRadius]
    rw [← hcount]
    push_cast
    omega
  refine ⟨events,hlen,hcount,hw,hlagv,hdist,?_,?_,hclock⟩
  · intro h4
    have hd : (4*(ys.length+1) : ℤ) ≤ GalilScaffoldCounter.value t.watch.machine.control.distance := by
      rw [hdist]; exact_mod_cast h4
    exact (GalilScaffoldChainPrediction.watch_phase hw c b ys rfl hd).1
  · have h1 := scan_events_invariant hprep hi0
    have h2 := scan_events_invariant (hs raw (position cen) initialRadius) h1
    simp only [scanRadius]
    rw [← hcount]
    exact h2

#print axioms joint_shift_supply

/-! ## The break of the chain on a matched compare

Scala forbids a break with pending lag (`chain restart violates the
confirmed-period invariant`): the chain breaks only when a matched outer
compare's immediate consume disagrees with the prediction. Then `matched()`
has incremented the margin, the verifier has moved, the control is `broken`,
and the lag stays zero — the background restart's guard. -/

inductive JointBreak (delay : ℕ) : JointState → JointState → Prop
  | intro (s : JointState) (hc : s.clock = 1) (hr : canRight s.right)
      (hm : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
        GalilScaffoldInputHead.read (right s.right))
      (hz : GalilScaffoldCounter.zero s.watch.lag = true)
      (hv : GalilScaffoldChainVerifier.canRight s.watch.machine.verifier)
      (a : Fin 3) (ht : GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus = some a)
      (hne : GalilScaffoldInputHead.read (right s.watch.machine.verifier) ≠ some a) :
      JointBreak delay s ⟨GalilScaffoldInputHead.left s.left,right s.right,
        ⟨consume s.watch.machine,s.watch.lag,GalilScaffoldCounter.inc s.watch.margin⟩,delay⟩

theorem joint_break_facts {delay : ℕ} {s t : JointState} (h : JointBreak delay s t) :
    t.watch.machine.control.broken = true ∧ t.watch.lag = s.watch.lag ∧
      t.watch.margin = GalilScaffoldCounter.inc s.watch.margin ∧
      t.watch.machine.control.last = s.watch.machine.control.last ∧
      t.watch.machine.control.distance = s.watch.machine.control.distance ∧
      t.clock = delay ∧
      ∀ (raw : List (Fin 2)) (c r : ℕ), ScanInvariant raw c r s.left s.right →
        ScanInvariant raw c (r+1) t.left t.right := by
  cases h with
  | intro hc hr hm hz hv a ht hne =>
    have hcm := GalilScaffoldChainVerifier.consume_mismatch s.watch.machine a ht hne
    refine ⟨?_,rfl,rfl,?_,?_,rfl,?_⟩
    · show (consume s.watch.machine).control.broken = true
      rw [hcm]
    · show (consume s.watch.machine).control.last = _
      rw [hcm]
    · show (consume s.watch.machine).control.distance = _
      rw [hcm]
    · intro raw c r hi
      exact scan_matched hi hr hm

/-- The fresh watch's break after the lag is exhausted and four semiperiods
are verified: every condition of the background restart holds on the same
state, and the scan has grown by one more place. -/
theorem joint_break_restart {raw : List (Fin 2)} (cen : PlaceHead) (c : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : GalilScaffoldCounter.Counter)
    (hrc : GalilScaffoldCounter.Canonical radius)
    (r0 : ℕ) (hr0 : GalilScaffoldCounter.value radius = r0)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = ys.length+1)
    {l0 rr0 l1 rr1 : PlaceHead}
    (hi0 : ScanInvariant raw (position cen) r0 l0 rr0)
    (hprep : ScanEvents raw (position cen) r0 l0 rr0 (sm :: (bs ++ dm :: cs)) l1 rr1)
    {delay clock0 : ℕ} {avail : List Bool} {m t : JointState}
    (hjoint : JointRun delay ⟨l1,rr1,watchStart cen c ys b
      (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm bs cs)),clock0⟩ avail m)
    (hexhausted : GalilScaffoldCounter.zero m.watch.lag = true)
    (h4 : 4*(ys.length+1) ≤ r0+(sm :: (bs ++ dm :: cs)).count true+
      (GalilScaffoldMatchClock.run delay clock0 avail).2)
    (hbreak : JointBreak delay m t) :
    let scanRadius := r0+(sm :: (bs ++ dm :: cs)).count true+
      (GalilScaffoldMatchClock.run delay clock0 avail).2
    t.watch.machine.control.broken = true ∧
      GalilScaffoldCounter.zero t.watch.lag = true ∧
      GalilScaffoldCounter.negative t.watch.margin = false ∧
      GalilScaffoldCounter.positive t.watch.machine.control.last = true ∧
      GalilScaffoldCounter.Canonical t.watch.machine.control.last ∧
      ScanInvariant raw (position cen) (scanRadius+1) t.left t.right := by
  intro scanRadius
  have hlcanon := credits_lag_canonical (GalilScaffoldChainCredits.prepEvents sm dm bs cs) (GalilScaffoldChainCredits.start radius) hrc
  have hmcanon := credits_margin_canonical (GalilScaffoldChainCredits.prepEvents sm dm bs cs) (GalilScaffoldChainCredits.start radius) hrc
  obtain ⟨events,_,hcount,hw,_,hdist,hphase,hscan,_⟩ :=
    joint_shift_supply cen c ys b radius r0 hr0 sm dm bs cs hlcanon hmcanon hi0 hprep hjoint hexhausted
  obtain ⟨hbroken,hlag,hmargin,hlast,_,_,hgrow⟩ := joint_break_facts hbreak
  have hbal : GalilScaffoldChainWatch.balance
      (watchStart cen c ys b (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm bs cs))) = 4*((ys.length+1 : ℕ) : ℤ) := by
    have := GalilScaffoldChainWatch.prepared_balance ⟨cen,GalilScaffoldChainConsume.ready c ys b⟩ rfl
      radius sm dm bs cs
    rw [hbl] at this
    exact this
  have hd4 : (4*(ys.length+1) : ℤ) ≤ GalilScaffoldCounter.value m.watch.machine.control.distance := by
    rw [hdist]; exact_mod_cast h4
  have hp4 := hphase h4
  obtain ⟨actual,htrace,_⟩ := GalilScaffoldChainWatchTrace.run_trace hw
  have hunbroken : m.watch.machine.control.broken = false := by
    rw [htrace.broken]; rfl
  have hguard := GalilScaffoldChainWatch.shift_ready hw ⟨hlcanon,hmcanon⟩ (ys.length+1) hbal hexhausted
    hd4 hp4 hunbroken
  simp only [GalilScaffoldChainCatch.freshShiftGuard,Bool.and_eq_true,Bool.not_eq_true'] at hguard
  have hmneg : GalilScaffoldCounter.negative m.watch.margin = false := hguard.2
  have hmc := (GalilScaffoldChainWatch.run_canonical hw ⟨hlcanon,hmcanon⟩).2
  have hmval : 0 ≤ GalilScaffoldCounter.value m.watch.margin := by
    by_contra hneg
    have := (GalilScaffoldCounter.negative_iff _ hmc).2 (by omega)
    rw [hmneg] at this; cases this
  have hlow := watch_last_lower hw c b ys rfl hd4
  have hlc : GalilScaffoldCounter.Canonical m.watch.machine.control.last := by
    have := GalilScaffoldChainRestart.run_canonical (GalilScaffoldChainConsume.ready c ys b) actual
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    have hctl : m.watch.machine.control =
        GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready c ys b) actual := htrace.control
    rw [hctl]
    exact this.1
  refine ⟨hbroken,?_,?_,?_,?_,hgrow raw (position cen) scanRadius hscan⟩
  · rw [hlag]; exact hexhausted
  · rw [hmargin]
    rw [Bool.eq_false_iff]
    intro hneg
    have := (GalilScaffoldCounter.negative_iff _ (GalilScaffoldCounter.inc_canonical _ hmc)).1 hneg
    rw [GalilScaffoldCounter.inc_value] at this
    omega
  · rw [hlast]
    rw [GalilScaffoldCounter.positive_iff _ hlc]
    omega
  · rw [hlast]; exact hlc

#print axioms joint_break_facts
#print axioms joint_break_restart

end PalPeg.GalilScaffoldChainInputSupply
