import Complexity.BinaryWord

/-! Space-annotated division and fixed-width writing for local unary fields. -/

namespace Complexity.BinaryWord

theorem unary_nonEmpty {k : Nat} {i : Fin k} {L : Lists k} {n : Nat}
    (h : L i = List.replicate (n + 1) 1) : nonEmpty (lastSym (L i)) = true := by
  have hn : lastSym (L i) ≠ 3 := by
    intro he
    have hz := congrArg List.length (lastSym_eq_three.mp he)
    simp [h] at hz
  simpa [nonEmpty] using hn

theorem pop_unary {k B n : Nat} {i : Fin k} {L : Lists k}
    (h : L i = List.replicate (n + 1) 1) (hB : LenOK B L) :
    Runs (LenOK B) (.pop i) L (L.set i (List.replicate n 1)) 1 := by
  have he : (L i).dropLast = List.replicate n 1 := by simp [h]
  have hr := runs_pop (i := i) hB (by
    apply lenOK_set hB
    have := hB i
    simp [h] at this
    simp [he]; omega)
  simpa only [he] using hr

def halfBody {k : Nat} (a q flag : Fin k) : LProg k :=
  .seq (.pop a) (.ite a nonEmpty (.seq (.pop a) (.push q 1)) (.push flag 1))

def halfP {k : Nat} (a q flag : Fin k) : LProg k :=
  .loop a nonEmpty (halfBody a q flag)

/-- Drain pairs of unary cells, returning the quotient and an empty/singleton
parity flag. The quotient register may already hold `q0` cells. -/
theorem half_runs {k : Nat} {a q flag : Fin k} (hd : [a, q, flag].Nodup)
    {B n q0 : Nat} {L : Lists k}
    (ha : L a = List.replicate n 1) (hq : L q = List.replicate q0 1)
    (hf : L flag = []) (hB : LenOK B L) (hcap : q0 + n / 2 + 3 ≤ B) :
    ∃ T, Runs (LenOK B) (halfP a q flag) L
      (((L.set a []).set q (List.replicate (q0 + n / 2) 1)).set flag
        (List.replicate (n % 2) 1)) T := by
  have haq : a ≠ q := by rintro rfl; simp at hd
  have haf : a ≠ flag := by rintro rfl; simp at hd
  have hqf : q ≠ flag := by rintro rfl; simp at hd
  induction n using Nat.strongRecOn generalizing q0 L with
  | ind n ih =>
    cases n with
    | zero =>
      have he : ((L.set a []).set q (List.replicate (q0 + 0 / 2) 1)).set flag
          (List.replicate (0 % 2) 1) = L := by
        simp only [Nat.zero_div, Nat.add_zero, Nat.zero_mod, List.replicate_zero]
        funext i
        by_cases hia : i = a <;> by_cases hiq : i = q <;> by_cases hif : i = flag <;>
          simp_all [Lists.set]
      refine ⟨1, ?_⟩
      rw [he]
      exact ⟨1, Nat.le_refl _, .loopF hB (by simp [ha, nonEmpty, lastSym])⟩
    | succ m =>
      let M := L.set a (List.replicate m 1)
      have hM : LenOK B M := lenOK_set hB a (by
        have := hB a; simp [ha] at this; simp; omega)
      have hp1 := pop_unary ha hB
      cases m with
      | zero =>
        let N := M.set flag [1]
        have hN : LenOK B N := lenOK_set hM flag (by simp; omega)
        have hrpush : Runs (LenOK B) (.push flag 1) M N 1 := by
          simpa [M, N, Lists.set_ne _ _ haf.symm, hf] using
            (runs_push (i := flag) (e := 1) hM (by
              simpa [M, N, Lists.set_ne _ _ haf.symm, hf] using hN))
        have hrbody := hp1.seq (hrpush.iteF (i := a) (c := nonEmpty) (p := .seq (.pop a) (.push q 1)) hM (by simp [nonEmpty, lastSym]))
        have he : (((L.set a []).set q (List.replicate (q0 + 1 / 2) 1)).set flag
            (List.replicate (1 % 2) 1)) = N := by
          funext i
          by_cases hia : i = a <;> by_cases hiq : i = q <;> by_cases hif : i = flag <;>
            simp_all [N, M, Lists.set]
        have hout : Runs (LenOK B) (halfP a q flag) N N 1 :=
          ⟨1, Nat.le_refl _, .loopF hN (by simp [N, M, Lists.set_ne _ _ haf, nonEmpty, lastSym])⟩
        obtain ⟨t1, _, hx1⟩ := hrbody
        obtain ⟨t2, _, hx2⟩ := hout
        rw [he]
        exact ⟨t1 + 1 + t2, t1 + 1 + t2, Nat.le_refl _,
          .loopC hB (unary_nonEmpty ha) hx1 hx2⟩
      | succ m =>
        let N := L.set a (List.replicate m 1)
        have hN : LenOK B N := lenOK_set hB a (by
          have := hB a; simp [ha] at this; simp; omega)
        have hp2 : Runs (LenOK B) (.pop a) M N 1 := by
          simpa [M, N, Lists.set_set_u] using pop_unary
            (L := M) (i := a) (n := m) (by simp [M]) hM
        let P := N.set q (List.replicate (q0 + 1) 1)
        have hP : LenOK B P := lenOK_set hN q (by simp; omega)
        have hqN : N q = List.replicate q0 1 := by
          simp [N, Lists.set_ne _ _ haq.symm, hq]
        have hepush : N.set q (N q ++ [1]) = P := by
          simp [P, hqN, ← List.replicate_append_replicate]
        have hpush := runs_push (i := q) (e := 1) hN (by rw [hepush]; exact hP)
        rw [hepush] at hpush
        have hrbody := hp1.seq ((hp2.seq hpush).iteT (i := a) (c := nonEmpty) (q := .push flag 1) hM
          (unary_nonEmpty (i := a) (L := M) (n := m) (by simp [M])))
        obtain ⟨T, hr⟩ := ih m (by omega) (q0 := q0 + 1) (L := P)
          (by simp [P, N, Lists.set_ne _ _ haq])
          (by simp [P])
          (by simp [P, N, Lists.set_ne _ _ hqf.symm, Lists.set_ne _ _ haf.symm, hf])
          hP (by omega)
        have he : ((P.set a []).set q (List.replicate (q0 + 1 + m / 2) 1)).set flag
            (List.replicate (m % 2) 1) =
            ((L.set a []).set q (List.replicate (q0 + (m + 1 + 1) / 2) 1)).set flag
              (List.replicate ((m + 1 + 1) % 2) 1) := by
          have hdv : (m + 1 + 1) / 2 = m / 2 + 1 := by omega
          have hmod : (m + 1 + 1) % 2 = m % 2 := by omega
          funext i
          by_cases hia : i = a <;> by_cases hiq : i = q <;> by_cases hif : i = flag <;>
            simp_all [P, N, Lists.set, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        rw [he] at hr
        obtain ⟨t1, _, hx1⟩ := hrbody
        obtain ⟨t2, _, hx2⟩ := hr
        exact ⟨t1 + 1 + t2, t1 + 1 + t2, Nat.le_refl _,
          .loopC hB (unary_nonEmpty ha) hx1 hx2⟩

def digitP {k : Nat} (a q flag out : Fin k) : LProg k :=
  .seq (halfP a q flag)
    (.seq (.ite flag nonEmpty (.push out 1) (.push out 0))
      (.seq (.pop flag) (moveAll q a)))

/-- Emit a single low bit and replace the local value by its quotient by two.
The two arithmetic scratch registers are restored to empty. -/
theorem digit_runs {k : Nat} {a q flag out : Fin k}
    (hd : [a, q, flag, out].Nodup) {B n : Nat} {L : Lists k}
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (hB : LenOK B L) (hcap : n + 3 ≤ B) (hout : (L out).length + 3 ≤ B) :
    ∃ T, Runs (LenOK B) (digitP a q flag out) L
      ((((L.set a (List.replicate (n / 2) 1)).set q []).set flag []).set out
        (L out ++ [n % 2])) T := by
  have haq : a ≠ q := by rintro rfl; simp at hd
  have haf : a ≠ flag := by rintro rfl; simp at hd
  have hao : a ≠ out := by rintro rfl; simp at hd
  have hqf : q ≠ flag := by rintro rfl; simp at hd
  have hqo : q ≠ out := by rintro rfl; simp at hd
  have hfo : flag ≠ out := by rintro rfl; simp at hd
  have hm : n % 2 < 2 := Nat.mod_lt _ (by decide)
  let H := ((L.set a []).set q (List.replicate (n / 2) 1)).set flag
    (List.replicate (n % 2) 1)
  obtain ⟨T1, hr1⟩ := half_runs (a := a) (q := q) (flag := flag)
    (by simp [haq, haf, hqf]) (q0 := 0) ha hq hf hB (by omega)
  have hH : LenOK B H := by
    have h1 := lenOK_set hB a (l := []) (by simp; omega)
    have h2 := lenOK_set h1 q (l := List.replicate (n / 2) 1) (by simp; omega)
    exact lenOK_set h2 flag (by simp; omega)
  have hHo : H out = L out := by
    simp [H, Lists.set_ne _ _ hfo.symm, Lists.set_ne _ _ hqo.symm,
      Lists.set_ne _ _ hao.symm]
  let M := H.set out (L out ++ [n % 2])
  have hM : LenOK B M := lenOK_set hH out (by simp; omega)
  have hr2 : Runs (LenOK B)
      (.ite flag nonEmpty (.push out 1) (.push out 0)) H M 2 := by
    by_cases hm1 : n % 2 = 1
    · have hp := runs_push (i := out) (e := 1) hH (by simpa [M, hHo, hm1] using hM)
      have he : H.set out (H out ++ [1]) = M := by simp [M, hHo, hm1]
      rw [he] at hp
      exact hp.iteT hH (by simp [H, hm1, nonEmpty, lastSym])
    · have hm0 : n % 2 = 0 := by omega
      have hp := runs_push (i := out) (e := 0) hH (by simpa [M, hHo, hm0] using hM)
      have he : H.set out (H out ++ [0]) = M := by simp [M, hHo, hm0]
      rw [he] at hp
      exact hp.iteF hH (by simp [H, hm0, nonEmpty, lastSym])
  let N := M.set flag []
  have hN : LenOK B N := lenOK_set hM flag (by simp; omega)
  have hpop : M.set flag (M flag).dropLast = N := by
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hmod with hh | hh <;> simp [M, H, N, Lists.set_ne _ _ hfo, hh]
  have hr3 := runs_pop (i := flag) hM (by rw [hpop]; exact hN)
  rw [hpop] at hr3
  have hNa : N a = [] := by
    simp [N, M, H, Lists.set_ne _ _ haf, Lists.set_ne _ _ hao, Lists.set_ne _ _ haq]
  have hNq : N q = List.replicate (n / 2) 1 := by
    simp [N, M, H, Lists.set_ne _ _ hqf, Lists.set_ne _ _ hqo]
  have hmove := runs_moveAll (L := N) haq.symm (Q := LenOK B)
    (fun i j _ _ => lenOK_moving hN haq.symm (by simp [hNa, hNq]; omega) i j)
  have he : N.moveAll q a =
      (((L.set a (List.replicate (n / 2) 1)).set q []).set flag []).set out
        (L out ++ [n % 2]) := by
    funext i
    by_cases hia : i = a <;> by_cases hiq : i = q <;>
      by_cases hif : i = flag <;> by_cases hio : i = out <;>
      simp_all [N, M, H, Lists.moveAll, Lists.set]
  rw [he] at hmove
  have hr1' : Runs (LenOK B) (halfP a q flag) L H T1 := by
    simpa only [Nat.zero_add] using hr1
  exact ⟨_, hr1'.seq (hr2.seq (hr3.seq hmove))⟩

def lowWord : Nat → Nat → List Nat
  | 0, _ => []
  | width + 1, n => n % 2 :: lowWord width (n / 2)

theorem lowWord_length (width n : Nat) : (lowWord width n).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [lowWord, ih]

def emitBody {k : Nat} (a q flag count out : Fin k) : LProg k :=
  .seq (digitP a q flag out) (.pop count)

def emitP {k : Nat} (a q flag count out : Fin k) : LProg k :=
  .loop count nonEmpty (emitBody a q flag count out)

/-- Emit exactly the counter's number of low bits, including high zero bits.
The initial local value fits that width, so it is completely drained. -/
theorem emit_runs {k : Nat} {a q flag count out : Fin k}
    (hd : [a, q, flag, count, out].Nodup) {B width n : Nat} {L : Lists k}
    (hn : n < 2 ^ width)
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (hc : L count = List.replicate width 1)
    (hB : LenOK B L) (hcap : n + 3 ≤ B)
    (hout : (L out).length + width + 2 ≤ B) :
    ∃ T, Runs (LenOK B) (emitP a q flag count out) L
      (((((L.set a []).set q []).set flag []).set count []).set out
        (L out ++ lowWord width n)) T := by
  have haq : a ≠ q := by rintro rfl; simp at hd
  have haf : a ≠ flag := by rintro rfl; simp at hd
  have hac : a ≠ count := by rintro rfl; simp at hd
  have hao : a ≠ out := by rintro rfl; simp at hd
  have hqf : q ≠ flag := by rintro rfl; simp at hd
  have hqc : q ≠ count := by rintro rfl; simp at hd
  have hqo : q ≠ out := by rintro rfl; simp at hd
  have hfc : flag ≠ count := by rintro rfl; simp at hd
  have hfo : flag ≠ out := by rintro rfl; simp at hd
  have hco : count ≠ out := by rintro rfl; simp at hd
  induction width generalizing n L with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    have he : ((((L.set a []).set q []).set flag []).set count []).set out
        (L out ++ lowWord 0 n) = L := by
      funext i
      by_cases hia : i = a <;> by_cases hiq : i = q <;> by_cases hif : i = flag <;>
        by_cases hic : i = count <;> by_cases hio : i = out <;>
        simp_all [Lists.set, lowWord]
    refine ⟨1, ?_⟩
    rw [he]
    exact ⟨1, Nat.le_refl _, .loopF hB (by simp [hc, nonEmpty, lastSym])⟩
  | succ width ih =>
    let D := (((L.set a (List.replicate (n / 2) 1)).set q []).set flag []).set out
      (L out ++ [n % 2])
    obtain ⟨T1, hr1⟩ := digit_runs (a := a) (q := q) (flag := flag) (out := out)
      (by simp [haq, haf, hao, hqf, hqo, hfo]) ha hq hf hB hcap (by omega)
    have hD : LenOK B D := by
      have h1 := lenOK_set hB a (l := List.replicate (n / 2) 1) (by simp; omega)
      have h2 := lenOK_set h1 q (l := []) (by simp; omega)
      have h3 := lenOK_set h2 flag (l := []) (by simp; omega)
      exact lenOK_set h3 out (by simp; omega)
    have hDc : D count = List.replicate (width + 1) 1 := by
      simp [D, Lists.set_ne _ _ hco, Lists.set_ne _ _ hfc.symm,
        Lists.set_ne _ _ hqc.symm, Lists.set_ne _ _ hac.symm, hc]
    let P := D.set count (List.replicate width 1)
    have hP : LenOK B P := lenOK_set hD count (by
      have := hB count; simp [hc] at this; simp; omega)
    have hrpop := pop_unary hDc hD
    have hrbody := hr1.seq hrpop
    have hn' : n / 2 < 2 ^ width := by rw [Nat.pow_succ] at hn; omega
    obtain ⟨T2, hr⟩ := ih (n := n / 2) (L := P) hn'
      (by simp [P, D, Lists.set_ne _ _ hac, Lists.set_ne _ _ hao,
        Lists.set_ne _ _ haf, Lists.set_ne _ _ haq])
      (by simp [P, D, Lists.set_ne _ _ hqc, Lists.set_ne _ _ hqo, Lists.set_ne _ _ hqf])
      (by simp [P, D, Lists.set_ne _ _ hfc, Lists.set_ne _ _ hfo])
      (by simp [P]) hP (by omega)
      (by simp [P, D, Lists.set_ne _ _ hco.symm]; omega)
    have he : ((((P.set a []).set q []).set flag []).set count []).set out
        (P out ++ lowWord width (n / 2)) =
        ((((L.set a []).set q []).set flag []).set count []).set out
          (L out ++ lowWord (width + 1) n) := by
      funext i
      by_cases hia : i = a <;> by_cases hiq : i = q <;> by_cases hif : i = flag <;>
        by_cases hic : i = count <;> by_cases hio : i = out <;>
        simp_all [P, D, Lists.set, lowWord, List.append_assoc]
    rw [he] at hr
    obtain ⟨t1, _, hx1⟩ := hrbody
    obtain ⟨t2, _, hx2⟩ := hr
    exact ⟨t1 + 1 + t2, t1 + 1 + t2, Nat.le_refl _,
      .loopC hB (unary_nonEmpty hc) hx1 hx2⟩

theorem set_swap {k : Nat} (L : Lists k) {i j : Fin k} (h : i ≠ j)
    (s t : List Nat) : (L.set i s).set j t = (L.set j t).set i s := by
  funext x
  by_cases hi : x = i <;> by_cases hj : x = j <;> simp_all [Lists.set]

def writeP {k : Nat} (a q flag count bits dst : Fin k) : LProg k :=
  .seq (emitP a q flag count bits) (moveAll bits dst)

/-- Prepend one fixed-width word to the stream on `dst`. Only one local value
is expanded in unary; the rest of the stream stays in binary throughout. -/
theorem write_runs {k : Nat} {a q flag count bits dst : Fin k}
    (hd : [a, q, flag, count, bits, dst].Nodup) {B width n : Nat} {L : Lists k}
    (hn : n < 2 ^ width)
    (ha : L a = List.replicate n 1) (hq : L q = []) (hf : L flag = [])
    (hc : L count = List.replicate width 1) (hb : L bits = [])
    (hB : LenOK B L) (hcap : n + 3 ≤ B)
    (hout : (L dst).length + width + 2 ≤ B) :
    ∃ T, Runs (LenOK B) (writeP a q flag count bits dst) L
      ((((((L.set a []).set q []).set flag []).set count []).set bits []).set dst
        (L dst ++ (lowWord width n).reverse)) T := by
  have hda : dst ≠ a := by rintro rfl; simp at hd
  have hdq : dst ≠ q := by rintro rfl; simp at hd
  have hdf : dst ≠ flag := by rintro rfl; simp at hd
  have hdc : dst ≠ count := by rintro rfl; simp at hd
  have hdb : dst ≠ bits := by rintro rfl; simp at hd
  let M := ((((L.set a []).set q []).set flag []).set count []).set bits (lowWord width n)
  have hd' : [a, q, flag, count, bits].Nodup := by
    simp_all
  obtain ⟨T1, hr⟩ := emit_runs hd' hn ha hq hf hc hB hcap
    (by simp [hb]; omega : (L bits).length + width + 2 ≤ B)
  have hr' : Runs (LenOK B) (emitP a q flag count bits) L M T1 := by
    simpa only [hb, List.nil_append] using hr
  have hM : LenOK B M := by
    have h1 := lenOK_set hB a (l := []) (by simp; omega)
    have h2 := lenOK_set h1 q (l := []) (by simp; omega)
    have h3 := lenOK_set h2 flag (l := []) (by simp; omega)
    have h4 := lenOK_set h3 count (l := []) (by simp; omega)
    exact lenOK_set h4 bits (by rw [lowWord_length]; omega)
  have hMd : M dst = L dst := by
    simp [M, Lists.set_ne _ _ hda, Lists.set_ne _ _ hdq,
      Lists.set_ne _ _ hdf, Lists.set_ne _ _ hdc, Lists.set_ne _ _ hdb]
  have hMb : M bits = lowWord width n := by simp [M]
  have hm := runs_moveAll (L := M) hdb.symm (Q := LenOK B)
    (fun i j _ _ => lenOK_moving hM hdb.symm
      (by rw [hMd, hMb, lowWord_length]; exact hout) i j)
  have he : M.moveAll bits dst =
      (((((L.set a []).set q []).set flag []).set count []).set bits []).set dst
        (L dst ++ (lowWord width n).reverse) := by
    simp only [Lists.moveAll, hMd, hMb]
    rw [set_swap _ hdb, show M.set bits [] =
      ((((L.set a []).set q []).set flag []).set count []).set bits [] from
        Lists.set_set_u _ _ _ _]
  rw [he] at hm
  exact ⟨_, hr'.seq hm⟩

end Complexity.BinaryWord
