import MacroPeg.CBV.SequentialCursorDecrease

/-! Direct cursor decrement and counted consumption on list/tape machines.
No new absolute cursor value is supplied or constructed by the decrement. -/
namespace Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialCursorDecrease

variable {k : Nat}

def decrement (src tmp : Fin k) : LProg k :=
  .seq (.pop src) (.seq (scan src tmp) (.seq (.pop src)
    (.seq (.ite src nonEmpty (.push src 1) (skipP src))
      (.seq (.push src 0) (moveAll tmp src)))))

/-- One consumed character is accounted for by a direct local bit move. All
scratch is cleared, the untouched suffix remains encoded, and the original
capacity suffices at every instruction state. -/
theorem decrement_runs {src tmp : Fin k} (hd : src ≠ tmp) (p : Nat) (rest : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = rest ++ [0] ++ unary (p+1))
    (htmp : L tmp = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (decrement src tmp) L
      (L.set src (lowerRest rest ++ [0] ++ unary p)) T := by
  have hsize := hL src
  rw [hsrc] at hsize
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at hsize
  let M := L.set src (rest ++ [0] ++ unary p)
  have hM : LenOK B M := lenOK_set hL src (by simp; omega)
  have hepop : L.set src (L src).dropLast = M := by
    have hlast : L src = (rest ++ [0] ++ unary p) ++ [1] := by
      simpa only [List.replicate_succ',List.append_assoc] using hsrc
    rw [hlast]
    simp only [List.dropLast_append_cons,List.dropLast_singleton,List.append_nil]
    rfl
  have hp := runs_pop (i := src) hL (by rw [hepop]; exact hM)
  rw [hepop] at hp
  have hms : M src = (rest ++ [0]) ++ unary p := by simp [M]
  have hmt : M tmp = [] := by simp [M,Lists.set,Ne.symm hd,htmp]
  have hs := scan_runs hd p (rest ++ [0]) M hms (by simp [lastSym_append,symIs]) hM
    (by simp only [hmt,List.length_nil]; omega)
  let N := (L.set src (rest ++ [0])).set tmp (unary p)
  have heN : (M.set src (rest ++ [0])).set tmp (M tmp ++ unary p) = N := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [M,N,Lists.set]
  rw [heN] at hs
  have hN := end_fits hs
  let D := (L.set src rest).set tmp (unary p)
  have hD : LenOK B D := lenOK_set (lenOK_set hL src (by omega)) tmp (by simp; omega)
  have heD : N.set src (N src).dropLast = D := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [N,D,Lists.set]
  have hpop := runs_pop (i := src) hN (by rw [heD]; exact hD)
  rw [heD] at hpop
  let R := (L.set src (lowerRest rest)).set tmp (unary p)
  have hR : LenOK B R := by
    have hh := lowerRest_length rest
    exact lenOK_set (lenOK_set hL src (by omega)) tmp (by simp; omega)
  have hbranch : ∃ T, Runs (LenOK B) (.ite src nonEmpty (.push src 1) (skipP src)) D R T := by
    by_cases hr : rest = []
    · have he : D = R := by simp [D,R,lowerRest,hr]
      refine ⟨1+1,?_⟩
      rw [← he]
      exact (runs_skip src hD).iteF hD (by simp [D,Lists.set,hd,hr,nonEmpty,lastSym])
    · have he : D.set src (D src ++ [1]) = R := by
        funext i
        by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [D,R,Lists.set,lowerRest]
      have hpush := runs_push (i := src) (e := 1) hD (by rw [he]; exact hR)
      rw [he] at hpush
      have hn : nonEmpty (lastSym (D src)) = true := by
        have hh : lastSym rest ≠ 3 := fun he => hr (lastSym_eq_three.mp he)
        simpa [D,Lists.set,hd,nonEmpty] using hh
      exact ⟨_,hpush.iteT hD hn⟩
  let U := (L.set src (lowerRest rest ++ [0])).set tmp (unary p)
  have hU : LenOK B U := by
    have hh := lowerRest_length rest
    exact lenOK_set (lenOK_set hL src (by simp; omega)) tmp (by simp; omega)
  have heU : R.set src (R src ++ [0]) = U := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [R,U,Lists.set]
  have hpush := runs_push (i := src) (e := 0) hR (by rw [heU]; exact hU)
  rw [heU] at hpush
  have htmpU : U tmp = unary p := by simp [U]
  have hcap : (U src).length + p + 2 ≤ B := by
    have hh := lowerRest_length rest
    simp [U,Lists.set,hd]
    omega
  have hr := restore_runs hd p U htmpU hU hcap
  have he : (U.set src (U src ++ unary p)).set tmp [] =
      L.set src (lowerRest rest ++ [0] ++ unary p) := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [U,Lists.set]
  rw [he] at hr
  obtain ⟨Tb,hb⟩ := hbranch
  exact ⟨_,hp.seq (hs.seq (hpop.seq (hb.seq (hpush.seq hr))))⟩

theorem decrement_current_runs {src tmp : Fin k} (hd : src ≠ tmp) {p n : Nat} {ps : List Nat}
    (hchain : SequentialCursorChain.Chain (p+1) ps n) (L : Lists k) {B : Nat}
    (hsrc : L src = cursors ((p+1) :: ps)) (htmp : L tmp = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (decrement src tmp) L (L.set src (cursors (p :: ps))) T := by
  rw [cursors_cons] at hsrc
  simpa only [lower_current hchain] using decrement_runs hd p _ L hsrc htmp hL


def consume (src tmp count : Fin k) : LProg k :=
  .loop count nonEmpty (.seq (.pop count) (decrement src tmp))

/-- The counter contains a number of consumed characters, not a new absolute
position. Its production by input/word matching is a separate obligation. -/
theorem consume_runs {src tmp count : Fin k} (hst : src ≠ tmp) (hsc : src ≠ count)
    (htc : tmp ≠ count) (used p n : Nat) (ps : List Nat)
    (hchain : SequentialCursorChain.Chain p ps n) (hused : used ≤ p) (L : Lists k) {B : Nat}
    (hsrc : L src = cursors (p :: ps)) (htmp : L tmp = []) (hcount : L count = unary used)
    (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (consume src tmp count) L
      ((L.set src (cursors ((p-used) :: ps))).set count []) T := by
  induction used generalizing p L with
  | zero =>
    have he : (L.set src (cursors ((p-0) :: ps))).set count [] = L := by
      simp only [Nat.sub_zero]
      rw [← hsrc,Lists.set_get_self]
      have hc : L count = [] := hcount
      rw [← hc,Lists.set_get_self]
    rw [he]
    exact ⟨1,1,Nat.le_refl _,.loopF hL (by simp [hcount,nonEmpty,lastSym])⟩
  | succ used ih =>
    cases p with
    | zero => omega
    | succ p =>
      let N := L.set count (unary used)
      have hN : LenOK B N := by
        apply lenOK_set hL count
        have hc := hL count
        rw [hcount] at hc
        simp only [List.length_replicate] at hc ⊢
        omega
      have hepop : L.set count (L count).dropLast = N := by
        rw [hcount]
        simp only [List.replicate_succ',List.dropLast_append_cons,List.dropLast_singleton,List.append_nil]
        rfl
      have hp := runs_pop (i := count) hL (by rw [hepop]; exact hN)
      rw [hepop] at hp
      have hns : N src = cursors ((p+1) :: ps) := by simp [N,Lists.set,hsc,hsrc]
      have hnt : N tmp = [] := by simp [N,Lists.set,htc,htmp]
      obtain ⟨Td,hd⟩ := decrement_current_runs hst hchain N hns hnt hN
      let M := N.set src (cursors (p :: ps))
      have hM : LenOK B M := end_fits hd
      have hms : M src = cursors (p :: ps) := by simp [M]
      have hmt : M tmp = [] := by simp [M,N,Lists.set,Ne.symm hst,htc,htmp]
      have hmc : M count = unary used := by simp [M,N,Lists.set,Ne.symm hsc]
      obtain ⟨Ti,hi⟩ := ih p (hchain.lower (Nat.le_succ p)) (by omega) M hms hmt hmc hM
      have he : (M.set src (cursors ((p-used) :: ps))).set count [] =
          (L.set src (cursors (((p+1)-(used+1)) :: ps))).set count [] := by
        funext i
        by_cases hs : i=src <;> by_cases hc : i=count <;>
          simp_all [M,N,Lists.set,Nat.succ_sub_succ_eq_sub]
      rw [he] at hi
      obtain ⟨t1,ht1,hx1⟩ := hp.seq hd
      obtain ⟨t2,ht2,hx2⟩ := hi
      exact ⟨t1+1+t2,t1+1+t2,Nat.le_refl _,.loopC hL
        (by simp [hcount,List.replicate_succ',lastSym_append,nonEmpty]) hx1 hx2⟩


/-- For a source-fixed consumption length, the program itself creates its
counter. This does not test whether any particular literal matches the input. -/
def consumeFixed (src tmp count : Fin k) (used : Nat) : LProg k :=
  .seq (appendP count (unary used)) (consume src tmp count)

theorem consumeFixed_runs {src tmp count : Fin k} (hst : src ≠ tmp) (hsc : src ≠ count)
    (htc : tmp ≠ count) (used p n : Nat) (ps : List Nat)
    (hchain : SequentialCursorChain.Chain p ps n) (hused : used ≤ p) (L : Lists k) {B : Nat}
    (hsrc : L src = cursors (p :: ps)) (htmp : L tmp = []) (hcount : L count = [])
    (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (consumeFixed src tmp count used) L
      (L.set src (cursors ((p-used) :: ps))) T := by
  have hsize := hL src
  rw [hsrc,cursors_cons] at hsize
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at hsize
  have hcap : (L count).length + (unary used).length + 2 ≤ B := by
    simp only [hcount,List.length_nil,List.length_replicate]
    omega
  have ha := append_runs count (unary used) hL hcap
  let M := L.set count (unary used)
  have heM : L.set count (L count ++ unary used) = M := by simp [M,hcount]
  rw [heM] at ha
  have hM := end_fits ha
  have hms : M src = cursors (p :: ps) := by simp [M,Lists.set,hsc,hsrc]
  have hmt : M tmp = [] := by simp [M,Lists.set,htc,htmp]
  have hmc : M count = unary used := by simp [M]
  obtain ⟨T,hr⟩ := consume_runs hst hsc htc used p n ps hchain hused M hms hmt hmc hM
  have he : (M.set src (cursors ((p-used) :: ps))).set count [] =
      L.set src (cursors ((p-used) :: ps)) := by
    funext i
    by_cases hs : i=src <;> by_cases hc : i=count <;> simp_all [M,Lists.set]
  rw [he] at hr
  exact ⟨_,ha.seq hr⟩

theorem consume_tape {src tmp count : Fin k} (hst : src ≠ tmp) (hsc : src ≠ count)
    (htc : tmp ≠ count) (used p n : Nat) (ps : List Nat)
    (hchain : SequentialCursorChain.Chain p ps n) (hused : used ≤ p) (L : Lists k) {B : Nat}
    (hsrc : L src = cursors (p :: ps)) (htmp : L tmp = []) (hcount : L count = unary used)
    (hL : LenOK B L) (τ : Tapes k) (hrep : Rep L τ) :
    ∃ t τ', Exec (TFits B) (consume src tmp count).compile τ t (.cont τ') ∧
      Rep ((L.set src (cursors ((p-used) :: ps))).set count []) τ' := by
  obtain ⟨T,hr⟩ := consume_runs hst hsc htc used p n ps hchain hused L hsrc htmp hcount hL
  exact tape_runs hr τ hrep


theorem decrement_constOK {E : Nat} (hE : 2 ≤ E) (src tmp : Fin k) :
    (decrement src tmp).ConstOK E := by
  simp [decrement,scan,moveTop,moveAll,skipP,LProg.ConstOK]
  omega

theorem consume_constOK {E : Nat} (hE : 2 ≤ E) (src tmp count : Fin k) :
    (consume src tmp count).ConstOK E := by
  exact ⟨trivial,decrement_constOK hE src tmp⟩

theorem consumeFixed_constOK {E : Nat} (hE : 2 ≤ E) (src tmp count : Fin k) (used : Nat) :
    (consumeFixed src tmp count used).ConstOK E := by
  refine ⟨?_,consume_constOK hE src tmp count⟩
  induction used with
  | zero => simp [appendP,skipP,LProg.ConstOK]
  | succ used ih =>
    rw [show unary (used+1) = 1 :: unary used from List.replicate_succ]
    refine ⟨?_,ih⟩
    change 1 < E
    omega

end Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine
