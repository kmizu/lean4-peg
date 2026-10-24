import Complexity.NMacros

/-! Header-counted transfers of fixed-size chunks and copies into two outputs. -/
namespace Complexity.NCountedTransfer
variable {K : Nat}

def words (i j c : Fin K) (hij : i ≠ j) : Nat → NProg K
  | 0 => nskip c
  | n+1 => .seq (nmv i j hij) (words i j c hij n)

theorem words_runs (i j c : Fin K) (hij : i ≠ j) (vs R D : List Nat) (S : Lists K)
    (hi : S i = R ++ vs.reverse) (hj : S j = D) :
    NRuns (words i j c hij vs.length) S ((S.set i R).set j (D ++ vs)) (2 * vs.length + 2) := by
  induction vs generalizing S D with
  | nil =>
    have he : (S.set i R).set j (D ++ []) = S := by
      funext x
      by_cases hx : x = i
      · subst x; simp [Lists.set,hij,hi]
      · by_cases hy : x = j
        · subst x; simp [Lists.set,hj]
        · simp [Lists.set,hx,hy]
    rw [he]
    exact nruns_skip c S
  | cons v vs ih =>
    have hp := nruns_mv i j hij S (l := R ++ vs.reverse) (v := v) (by simpa [List.append_assoc] using hi)
    let A := (S.set j (S j ++ [v])).set i (R ++ vs.reverse)
    have hr := ih (D ++ [v]) A (by simp [A]) (by simp [A,Lists.set,Ne.symm hij,hj])
    have he : (A.set i R).set j ((D ++ [v]) ++ vs) = (S.set i R).set j (D ++ v :: vs) := by
      funext x
      by_cases hx : x = i
      · subst x; simp [A,Lists.set,hij]
      · by_cases hy : x = j
        · subst x; simp [Lists.set,List.append_assoc]
        · simp [A,Lists.set,hx,hy]
    rw [he] at hr
    exact (hp.seq hr).mono (by simp; omega)

def counted (i j c : Fin K) (hij : i ≠ j) (stride : Nat) : NProg K :=
  .loop c .pos (.seq (words i j c hij stride) (.prim (.dec c)))

theorem counted_runs (i j c : Fin K) (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c)
    (stride : Nat) (chunks : List (List Nat)) (hl : ∀ chunk ∈ chunks, chunk.length = stride)
    (R D C : List Nat) (S : Lists K)
    (hi : S i = R ++ chunks.flatten.reverse) (hj : S j = D) (hc : S c = C ++ [chunks.length]) :
    NRuns (counted i j c hij stride) S
      (((S.set i R).set j (D ++ chunks.flatten)).set c (C ++ [0]))
      (chunks.length * (2 * stride + 4) + 1) := by
  induction chunks generalizing S D with
  | nil =>
    have he : ((S.set i R).set j (D ++ ([] : List Nat))).set c (C ++ [0]) = S := by
      funext x
      by_cases hx : x = c
      · subst x; simp [Lists.set,hc]
      · by_cases hy : x = j
        · subst x; simp [Lists.set,hj,hjc]
        · by_cases hz : x = i
          · subst x; simp [Lists.set,hi,hij,hic]
          · simp [Lists.set,hx,hy,hz]
    simp only [List.flatten_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] at he ⊢
    rw [he]
    exact nruns_loop_exit (by simp [hc])
  | cons chunk chunks ih =>
    have hlen := hl chunk (by simp)
    let A := (S.set i (R ++ chunks.flatten.reverse)).set j (D ++ chunk)
    have hm := words_runs i j c hij chunk (R ++ chunks.flatten.reverse) D S
      (by simpa [List.flatten_cons,List.reverse_append,List.append_assoc] using hi) hj
    rw [hlen] at hm
    change NRuns _ S A _ at hm
    have hd := nruns_dec c A (l := C) (v := chunks.length+1) (by
      simp [A,Lists.set,Ne.symm hic,Ne.symm hjc,hc])
    simp only [Nat.add_sub_cancel] at hd
    let B := A.set c (C ++ [chunks.length])
    have hr := ih (fun chunk h => hl chunk (by simp [h])) (D ++ chunk) B
      (by simp [B,A,Lists.set,hic,hij]) (by simp [B,A,Lists.set,hjc]) (by simp [B])
    have he : ((B.set i R).set j ((D ++ chunk) ++ chunks.flatten)).set c (C ++ [0]) =
        ((S.set i R).set j (D ++ (chunk :: chunks).flatten)).set c (C ++ [0]) := by
      funext x
      by_cases hx : x = c
      · subst x; simp [Lists.set]
      · by_cases hy : x = j
        · subst x; simp [Lists.set,hjc,List.flatten_cons,List.append_assoc]
        · by_cases hz : x = i
          · subst x; simp [B,Lists.set,hic,hij]
          · simp [B,A,Lists.set,hx,hy,hz]
    rw [he] at hr
    obtain ⟨t,ht,hb⟩ := hm.seq hd
    obtain ⟨u,hu,hr⟩ := hr
    refine ⟨t+1+u,?_,.loopC trivial (by simp [hc]) hb hr⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def copyBody (i j k : Fin K) (hij : i ≠ j) (hik : i ≠ k) : NProg K :=
  .seq (.prim (.dup i j hij)) (.seq (.prim (.dup i k hik)) (.prim (.pop i)))
def copyAll (i j k : Fin K) (hij : i ≠ j) (hik : i ≠ k) : NProg K :=
  .loop i .nonempty (copyBody i j k hij hik)

theorem copyAll_runs (i j k : Fin K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (vs D E : List Nat) (S : Lists K) (hi : S i = vs.reverse) (hj : S j = D) (hk : S k = E) :
    NRuns (copyAll i j k hij hik) S
      (((S.set i []).set j (D ++ vs)).set k (E ++ vs)) (4 * vs.length + 1) := by
  induction vs generalizing S D E with
  | nil =>
    have he : ((S.set i []).set j (D ++ [])).set k (E ++ []) = S := by
      funext x
      by_cases hx : x = k
      · subst x; simp [Lists.set,hk]
      · by_cases hy : x = j
        · subst x; simp [Lists.set,hj,hjk]
        · by_cases hz : x = i
          · subst x; simp [Lists.set,hi,hij,hik]
          · simp [Lists.set,hx,hy,hz]
    rw [he]
    exact nruns_loop_exit (by simp [hi,NTest.eval])
  | cons v vs ih =>
    let A := S.set j (D ++ [v])
    let B := A.set k (E ++ [v])
    let C := B.set i vs.reverse
    have h₁ : NRuns (.prim (.dup i j hij)) S A 1 := by
      simpa only [hj] using nruns_dup i j hij S (l := vs.reverse) (v := v) (by simpa using hi)
    have h₂ : NRuns (.prim (.dup i k hik)) A B 1 := by
      have hr := nruns_dup i k hik A (l := vs.reverse) (v := v) (by simp [A,Lists.set,hij,hi])
      simpa only [A,Lists.set_ne _ _ (Ne.symm hjk),hk] using hr
    have h₃ : NRuns (.prim (.pop i)) B C 1 := by
      exact nruns_pop i B (l := vs.reverse) (v := v) (by simp [B,A,Lists.set,hik,hij,hi])
    have hr := ih (D ++ [v]) (E ++ [v]) C (by simp [C])
      (by simp [C,B,A,Lists.set,Ne.symm hij,hjk])
      (by simp [C,B,A,Lists.set,Ne.symm hik])
    have he : ((C.set i []).set j ((D ++ [v]) ++ vs)).set k ((E ++ [v]) ++ vs) =
        ((S.set i []).set j (D ++ v :: vs)).set k (E ++ v :: vs) := by
      funext x
      by_cases hx : x = k
      · subst x; simp [Lists.set,List.append_assoc]
      · by_cases hy : x = j
        · subst x; simp [Lists.set,hjk,List.append_assoc]
        · by_cases hz : x = i
          · subst x; simp [Lists.set,hij,hik]
          · simp [C,B,A,Lists.set,hx,hy,hz]
    rw [he] at hr
    obtain ⟨t,ht,hb⟩ := h₁.seq (h₂.seq h₃)
    obtain ⟨u,hu,hr⟩ := hr
    exact ⟨t+1+u,by simp; omega,.loopC trivial (by simp [hi,NTest.eval]) hb hr⟩

end Complexity.NCountedTransfer
