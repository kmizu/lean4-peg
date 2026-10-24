import Complexity.UnarySpec
import Complexity.ListCompile

/-! Streaming conversion of a single binary word to a unary local register.
The untouched registers can hold the rest of a binary continuation stack.
Every intermediate state, including arithmetic scratch, satisfies `LenOK`.
-/

namespace Complexity.BinaryWord

def bit (b : Bool) : Nat := if b then 1 else 0

/-- Horner evaluation, most significant bit first. -/
def value (a : Nat) : List Bool → Nat
  | [] => a
  | b :: bs => value (2 * a + bit b) bs

theorem le_value (a : Nat) (bs : List Bool) : a ≤ value a bs := by
  induction bs generalizing a with
  | nil => exact Nat.le_refl _
  | cons b bs ih =>
    have := ih (2 * a + bit b)
    simp only [value]
    omega

theorem value_append (a : Nat) (bs cs : List Bool) :
    value a (bs ++ cs) = value (value a bs) cs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Top of the list is the next most significant bit. -/
def storage (bs : List Bool) : List Nat := (bs.map bit).reverse

def hornerBody {k : Nat} (w acc two p2 ta tb : Fin k) : LProg k :=
  .seq (powStepP acc two p2 ta tb)
    (.seq (.ite w (· == 5) (.push acc 1) (skipP acc)) (.pop w))

def horner {k : Nat} (w acc two p2 ta tb : Fin k) : LProg k :=
  .loop w nonEmpty (hornerBody w acc two p2 ta tb)

/-- Move exactly the unary counter's number of symbols, leaving the tail of
the source stack untouched. This reverses the extracted word. -/
def takeP {k : Nat} (src dst count : Fin k) : LProg k :=
  .loop count nonEmpty (.seq (moveTop src dst) (.pop count))

theorem take_runs {k : Nat} {src dst count : Fin k}
    (hd : [src, dst, count].Nodup) {B : Nat} {L : Lists k}
    (chunk tail : List Nat)
    (hs : L src = tail ++ chunk.reverse)
    (hc : L count = List.replicate chunk.length 1)
    (hB : LenOK B L) (hcap : (L dst).length + chunk.length + 2 ≤ B) :
    ∃ T, Runs (LenOK B) (takeP src dst count) L
      (((L.set src tail).set dst (L dst ++ chunk)).set count []) T := by
  have hsd : src ≠ dst := by rintro rfl; simp at hd
  have hsc : src ≠ count := by rintro rfl; simp at hd
  have hdc : dst ≠ count := by rintro rfl; simp at hd
  induction chunk generalizing L with
  | nil =>
    have he : ((L.set src tail).set dst (L dst ++ [])).set count [] = L := by
      simp only [List.append_nil, List.reverse_nil] at hs ⊢
      rw [← hs, Lists.set_get_self, Lists.set_get_self]
      rw [show ([] : List Nat) = L count by simpa using hc.symm]
      simp [Lists.set_get_self]
    refine ⟨1, ?_⟩
    rw [he]
    exact ⟨1, Nat.le_refl _, .loopF hB (by simp [hc, nonEmpty, lastSym])⟩
  | cons b bs ih =>
    have hlast : (L src).getLast?.toList = [b] := by simp [hs]
    have hdrop : (L src).dropLast = tail ++ bs.reverse := by simp [hs]
    obtain ⟨hcopy, hmove⟩ := lenOK_moveTop hB hsd (by simp at hcap; omega)
    have hm := runs_moveTop hsd hB hcopy hmove
    let M := L.moveTop src dst
    have hms : M src = tail ++ bs.reverse := by
      simp [M, Lists.moveTop, hdrop]
    have hmd : M dst = L dst ++ [b] := by
      simp [M, Lists.moveTop, Lists.set_ne _ _ hsd.symm, hlast]
    have hmc : M count = List.replicate (bs.length + 1) 1 := by
      simp [M, Lists.moveTop, Lists.set_ne _ _ hsc.symm,
        Lists.set_ne _ _ hdc.symm, hc]
    let N := M.set count (List.replicate bs.length 1)
    have he : M.set count (M count).dropLast = N := by
      simp [hmc, N, List.dropLast_replicate]
    have hN : LenOK B N := lenOK_set hmove count (by
      have := hB count
      simp [hc] at this
      simp; omega)
    have hp := runs_pop (i := count) hmove (by rw [he]; exact hN)
    rw [he] at hp
    obtain ⟨T, hr⟩ := ih (L := N)
      (by simp [N, Lists.set_ne _ _ hsc, hms])
      (by simp [N]) hN
      (by simp [N, Lists.set_ne _ _ hdc, hmd]; simp at hcap; omega)
    have hout : ((N.set src tail).set dst (N dst ++ bs)).set count [] =
        ((L.set src tail).set dst (L dst ++ b :: bs)).set count [] := by
      funext i
      by_cases his : i = src <;> by_cases hid : i = dst <;> by_cases hic : i = count <;>
        simp_all [N, M, Lists.moveTop, Lists.set, List.append_assoc]
    rw [hout] at hr
    obtain ⟨t1, _, hx1⟩ := hm.seq hp
    obtain ⟨t2, _, hx2⟩ := hr
    exact ⟨t1 + 1 + t2, t1 + 1 + t2, Nat.le_refl _,
      .loopC hB (by
        have hn : lastSym (L count) ≠ 3 := by
          intro heq
          have hz := congrArg List.length (lastSym_eq_three.mp heq)
          simp [hc] at hz
        simpa [nonEmpty] using hn) hx1 hx2⟩

/-- Only the word and accumulator change. In particular the unused registers
are preserved, and the multiplication scratch is empty again. -/
theorem horner_runs {k : Nat} {w acc two p2 ta tb : Fin k}
    (hd : [w, acc, two, p2, ta, tb].Nodup)
    {B a : Nat} {L : Lists k} (bs : List Bool)
    (hw : L w = storage bs) (ha : L acc = List.replicate a 1)
    (htwo : L two = [1, 1]) (hp2 : L p2 = [])
    (hta : L ta = []) (htb : L tb = [])
    (hB : LenOK B L) (hcap : 3 * value a bs + 4 ≤ B) :
    ∃ T, Runs (LenOK B) (horner w acc two p2 ta tb) L
      ((L.set w []).set acc (List.replicate (value a bs) 1)) T := by
  have hwa : w ≠ acc := by rintro rfl; simp at hd
  have htw : two ≠ w := by rintro rfl; simp at hd
  have hta' : two ≠ acc := by rintro rfl; simp at hd
  have hpw : p2 ≠ w := by rintro rfl; simp at hd
  have hpa : p2 ≠ acc := by rintro rfl; simp at hd
  have htaw : ta ≠ w := by rintro rfl; simp at hd
  have htaa : ta ≠ acc := by rintro rfl; simp at hd
  have htbw : tb ≠ w := by rintro rfl; simp at hd
  have htba : tb ≠ acc := by rintro rfl; simp at hd
  induction bs generalizing a L with
  | nil =>
    have he : (L.set w []).set acc (List.replicate (value a []) 1) = L := by
      rw [show ([] : List Nat) = L w from hw.symm]
      simp [Lists.set_get_self, value, ← ha]
    refine ⟨1, ?_⟩
    rw [he]
    exact ⟨1, Nat.le_refl _, .loopF hB (by simp [hw, storage, nonEmpty, lastSym])⟩
  | cons b bs ih =>
    let a' := 2 * a + bit b
    have had : a ≤ value a (b :: bs) := le_value a _
    have ha'd : a' ≤ value a (b :: bs) := le_value a' bs
    have hmul := powStep_spec (y := 2) (List.nodup_cons.mp hd).2 ha htwo hp2 hta htb hB
      (by omega : a * 2 + a + 2 ≤ B)
    let M := L.set acc (List.replicate (a * 2) 1)
    have hM : LenOK B M := lenOK_set hB acc (by simp; omega)
    let N := L.set acc (List.replicate a' 1)
    have hN : LenOK B N := lenOK_set hB acc (by simp; omega)
    have hchoose : Runs (LenOK B)
        (.ite w (· == 5) (.push acc 1) (skipP acc)) M N 2 := by
      cases b with
      | false =>
        have he : N = M := by simp [N, M, a', bit, Nat.mul_comm]
        rw [he]
        exact (runs_skip acc hM).iteF hM (by
          simp [M, Lists.set_ne _ _ hwa, hw, storage, lastSym, bit])
      | true =>
        have he : M.set acc (M acc ++ [1]) = N := by
          simp [M, N, a', bit, Lists.set_set_u, Nat.mul_comm,
            ← List.replicate_append_replicate]
        have hr := runs_push (i := acc) (e := 1) hM (by rw [he]; exact hN)
        rw [he] at hr
        exact hr.iteT hM (by
          simp [M, Lists.set_ne _ _ hwa, hw, storage, lastSym, bit])
    let P := N.set w (storage bs)
    have hpop : N.set w (N w).dropLast = P := by
      simp [N, P, Lists.set_ne _ _ hwa, hw, storage]
    have hP : LenOK B P := by
      apply lenOK_set hN
      have := hB w
      simp [hw, storage] at this ⊢
      omega
    have hrpop := runs_pop (i := w) hN (by rw [hpop]; exact hP)
    rw [hpop] at hrpop
    have hrbody := hmul.seq (hchoose.seq hrpop)
    obtain ⟨T, hr⟩ := ih (a := a') (L := P)
      (by simp [P])
      (by simp [P, N, Lists.set_ne _ _ hwa.symm])
      (by simp [P, N, Lists.set_ne _ _ htw, Lists.set_ne _ _ hta', htwo])
      (by simp [P, N, Lists.set_ne _ _ hpw, Lists.set_ne _ _ hpa, hp2])
      (by simp [P, N, Lists.set_ne _ _ htaw, Lists.set_ne _ _ htaa, hta])
      (by simp [P, N, Lists.set_ne _ _ htbw, Lists.set_ne _ _ htba, htb])
      hP hcap
    have he : (P.set w []).set acc (List.replicate (value a' bs) 1) =
        (L.set w []).set acc (List.replicate (value a (b :: bs)) 1) := by
      funext i
      by_cases hiw : i = w <;> by_cases hia : i = acc <;>
        simp_all [P, N, Lists.set, value, a']
    rw [he] at hr
    obtain ⟨t1, _, hx1⟩ := hrbody
    obtain ⟨t2, _, hx2⟩ := hr
    exact ⟨t1 + 1 + t2, t1 + 1 + t2, Nat.le_refl _,
      .loopC hB (by cases b <;> simp [hw, storage, nonEmpty, lastSym, bit]) hx1 hx2⟩

def readP {k : Nat} (src count w acc two p2 ta tb : Fin k) : LProg k :=
  .seq (takeP src w count) (horner w acc two p2 ta tb)

/-- Read one little-endian word. The remaining bit stream and every unrelated
register are preserved. The space premise concerns the decoded value of this
one word; it does not require decoding the rest of the source. -/
theorem read_runs {k : Nat} {src count w acc two p2 ta tb : Fin k}
    (hd : [src, count, w, acc, two, p2, ta, tb].Nodup)
    {B : Nat} {L : Lists k} (bits tail : List Bool)
    (hs : L src = storage (bits ++ tail))
    (hc : L count = List.replicate bits.length 1)
    (hw : L w = []) (ha : L acc = [])
    (htwo : L two = [1, 1]) (hp2 : L p2 = [])
    (hta : L ta = []) (htb : L tb = [])
    (hB : LenOK B L) (hcap : 3 * value 0 bits.reverse + 4 ≤ B) :
    ∃ T, Runs (LenOK B) (readP src count w acc two p2 ta tb) L
      ((((L.set src (storage tail)).set count []).set w []).set acc
        (List.replicate (value 0 bits.reverse) 1)) T := by
  have hsw : src ≠ w := by rintro rfl; simp at hd
  have hsc : src ≠ count := by rintro rfl; simp at hd
  have hwc : w ≠ count := by rintro rfl; simp at hd
  have hwa : w ≠ acc := by rintro rfl; simp at hd
  have hac : acc ≠ count := by rintro rfl; simp at hd
  have has : acc ≠ src := by rintro rfl; simp at hd
  let M := ((L.set src (storage tail)).set w (bits.map bit)).set count []
  obtain ⟨T1, ht⟩ := take_runs (src := src) (dst := w) (count := count) (by simp [hsw, hsc, hwc]) (L := L)
    (bits.map bit) (storage tail)
    (by simpa [storage] using hs)
    (by simpa using hc) hB (by
      have := hB src
      simp [hs, storage, hw] at this ⊢
      omega)
  have ht' : Runs (LenOK B) (takeP src w count) L M T1 := by simpa [M, hw] using ht
  have hM : LenOK B M := by
    have hlen := hB src
    simp [hs, storage] at hlen
    have h1 := lenOK_set hB src (l := storage tail) (by simp [storage]; omega)
    have h2 := lenOK_set h1 w (l := bits.map bit) (by simp; omega)
    exact lenOK_set h2 count (by simp; omega)
  have hother : ∀ i ∈ [acc, two, p2, ta, tb], M i = L i := by
    intro i hi
    have his : i ≠ src := by
      intro he; subst i
      have hn := (List.nodup_cons.mp hd).1
      exact hn (by simp_all)
    have hic : i ≠ count := by
      intro he; subst i
      have hn := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
      exact hn (by simp_all)
    have hiw : i ≠ w := by
      intro he; subst i
      have hn := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).1
      exact hn hi
    simp [M, Lists.set_ne _ _ his, Lists.set_ne _ _ hic, Lists.set_ne _ _ hiw]
  obtain ⟨T2, hh⟩ := horner_runs
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2
    (a := 0) (L := M) bits.reverse
    (by simp [M, storage, Lists.set_ne _ _ hwc])
    (by simpa [hother acc (by simp)] using ha)
    (by rw [hother two (by simp)]; exact htwo)
    (by rw [hother p2 (by simp)]; exact hp2)
    (by rw [hother ta (by simp)]; exact hta)
    (by rw [hother tb (by simp)]; exact htb) hM hcap
  have he : (M.set w []).set acc (List.replicate (value 0 bits.reverse) 1) =
      (((L.set src (storage tail)).set count []).set w []).set acc
        (List.replicate (value 0 bits.reverse) 1) := by
    funext i
    by_cases hiw : i = w <;> by_cases hic : i = count <;>
      by_cases hia : i = acc <;> simp_all [M, Lists.set]
  rw [he] at hh
  exact ⟨T1 + T2, ht'.seq hh⟩

/-- The list invariant transfers to every intermediate tape-program state,
including scans and copies inside the compiled instructions. -/
theorem runs_tape {k B T : Nat} {p : LProg k} {L L' : Lists k}
    (h : Runs (LenOK B) p L L' T) (τ : Tapes k) (hτ : Rep L τ) :
    ∃ t τ', t ≤ T * lcost B ∧ Exec (TFits B) p.compile τ t (.cont τ') ∧ Rep L' τ' := by
  obtain ⟨t, ht, hx⟩ := h
  obtain ⟨t', o, ht', he, hr⟩ := (compile_exec (fun _ h => h) hx).1 τ hτ
  cases o with
  | cont τ' => exact ⟨t', τ', Nat.le_trans ht' (Nat.mul_le_mul_right _ ht), he, hr⟩
  | stop b τ' => exact False.elim hr

end Complexity.BinaryWord
