import Shallot.Peg.Separation.Reduce
import MacroPeg.HigherOrder.KExp.FixedMap

namespace Shallot.PegSeparation

open Complexity Shallot.Packrat Shallot.Packrat.Machine Shallot.MacroPeg.KExp

/-- A token loader shares the recognizer's input, length, and temporary registers. -/
def tokenState (g : Grammar) (S : Lists (NK g)) (w : List Bool) (out : List Nat) (m : Nat) : Lists (NK g) :=
  ((S.set (inpR g) (w.map bitElem).reverse).set (tmpR g) out).set (lenR g) [m]

def readToken (g : Grammar) : Nat → List Bool → NProg (NK g)
  | 0, acc => .seq (npushC (tmpR g) (symbolCode (tokChar (bitsTokL acc)))) (.prim (.inc (lenR g)))
  | r + 1, acc => .ite (inpR g) .nonempty
      (.ite (inpR g) .zero
        (.seq (.prim (.pop (inpR g))) (readToken g r (acc ++ [false])))
        (.seq (.prim (.pop (inpR g))) (readToken g r (acc ++ [true]))))
      (nskip (inpR g))

theorem tokenState_input (g : Grammar) (S : Lists (NK g)) (w : List Bool) (out : List Nat) (m : Nat) :
    tokenState g S w out m (inpR g) = (w.map bitElem).reverse := by
  simp only [tokenState]; lists_at <;> simp_all [inpR, tmpR, lenR, Fin.mk.injEq]

theorem tokenState_tmp (g : Grammar) (S : Lists (NK g)) (w : List Bool) (out : List Nat) (m : Nat) :
    tokenState g S w out m (tmpR g) = out := by
  simp only [tokenState]; lists_at <;> simp_all [tmpR, lenR, Fin.mk.injEq]

theorem tokenState_len (g : Grammar) (S : Lists (NK g)) (w : List Bool) (out : List Nat) (m : Nat) :
    tokenState g S w out m (lenR g) = [m] := by simp [tokenState]

/-- A short final group is consumed without emitting a token, as in `ofBits`. -/
theorem readToken_spec (g : Grammar) (S : Lists (NK g)) (r : Nat) (acc w : List Bool) (out : List Nat) (m : Nat) :
    NRuns (readToken g r acc) (tokenState g S w out m)
      (tokenState g S (w.drop r)
        (out ++ if r ≤ w.length then [symbolCode (tokChar (bitsTokL (acc ++ w.take r)))] else [])
        (m + if r ≤ w.length then 1 else 0)) (130 + 4 * r) := by
  induction r generalizing acc w out m with
  | zero =>
    have hp := nruns_pushC (tmpR g) (tokenState g S w out m) (symbolCode (tokChar (bitsTokL acc)))
    rw [tokenState_tmp] at hp
    have hl : (tokenState g S w out m).set (tmpR g) (out ++ [symbolCode (tokChar (bitsTokL acc))]) (lenR g) = [m] := by
      rw [Lists.set_ne _ _ (by packrat_regs), tokenState_len]
    have hi := nruns_inc (lenR g) _ (l := []) (v := m) hl
    have hs : ((tokenState g S w out m).set (tmpR g) (out ++ [symbolCode (tokChar (bitsTokL acc))])).set
        (lenR g) [m + 1] = tokenState g S w (out ++ [symbolCode (tokChar (bitsTokL acc))]) (m + 1) := by
      simp only [tokenState]; lists_eq <;> simp_all [inpR, tmpR, lenR, Fin.mk.injEq]
    simp only [List.nil_append] at hi
    rw [hs] at hi
    have hb : symbolCode (tokChar (bitsTokL acc)) ≤ 125 := by
      have := tokChar_le (bitsTokL acc); unfold symbolCode; omega
    simpa [readToken] using (hp.seq hi).mono (show symbolCode (tokChar (bitsTokL acc)) + 1 + 1 ≤ 130 by omega)
  | succ r ih =>
    cases w with
    | nil =>
      have hc : NTest.nonempty.eval (tokenState g S [] out m (inpR g)) = false := by rw [tokenState_input]; rfl
      have hh : NRuns (readToken g (r + 1) acc) (tokenState g S [] out m) (tokenState g S [] out m) 3 :=
        (nruns_skip (inpR g) (tokenState g S [] out m)).iteF hc
      simpa [readToken] using hh.mono (show 2 + 1 ≤ 130 + 4 * (r + 1) by omega)
    | cons b w =>
      have hp : tokenState g S (b :: w) out m (inpR g) = (w.map bitElem).reverse ++ [bitElem b] := by
        rw [tokenState_input]; simp
      have hc : NTest.nonempty.eval (tokenState g S (b :: w) out m (inpR g)) = true := by
        rw [hp]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp))
      have hpop := nruns_pop (inpR g) (tokenState g S (b :: w) out m) hp
      have hs : (tokenState g S (b :: w) out m).set (inpR g) (w.map bitElem).reverse = tokenState g S w out m := by
        simp only [tokenState]; lists_eq <;> simp_all [inpR, tmpR, lenR, Fin.mk.injEq]
      rw [hs] at hpop
      have hr := hpop.seq (ih (acc ++ [b]) w out m)
      have he : (tokenState g S (List.drop r w)
          (out ++ if r ≤ w.length then [symbolCode (tokChar (bitsTokL ((acc ++ [b]) ++ List.take r w)))] else [])
          (m + if r ≤ w.length then 1 else 0)) =
          tokenState g S ((b :: w).drop (r + 1))
          (out ++ if r + 1 ≤ (b :: w).length then [symbolCode (tokChar (bitsTokL (acc ++ (b :: w).take (r + 1))))] else [])
          (m + if r + 1 ≤ (b :: w).length then 1 else 0) := by
        simp [List.append_assoc]
      rw [he] at hr
      cases b with
      | false =>
        have hz : NTest.zero.eval (tokenState g S (false :: w) out m (inpR g)) = true := by rw [hp]; simp [bitElem]
        simpa [readToken] using (hr.iteT (q := _) hz |>.iteT (q := _) hc).mono (by omega)
      | true =>
        have hz : NTest.zero.eval (tokenState g S (true :: w) out m (inpR g)) = false := by rw [hp]; simp [bitElem]
        simpa [readToken] using (hr.iteF (p := _) hz |>.iteT (q := _) hc).mono (by omega)

def tokenLoop (g : Grammar) : NProg (NK g) := .loop (inpR g) .nonempty (readToken g 4 [])

theorem loop_continue {K : Nat} {i : Fin K} {c : NTest} {p : NProg K}
    {S S₁ S₂ : Lists K} {T₁ T₂ : Nat} (hc : c.eval (S i) = true)
    (hp : NRuns p S S₁ T₁) (hl : NRuns (.loop i c p) S₁ S₂ T₂) :
    NRuns (.loop i c p) S S₂ (T₁ + 1 + T₂) := by
  obtain ⟨t₁, ht₁, hx₁⟩ := hp
  obtain ⟨t₂, ht₂, hx₂⟩ := hl
  exact ⟨t₁ + 1 + t₂, by omega, .loopC trivial hc hx₁ hx₂⟩

/-- Tokenize the entire initial bit stream, dropping only its incomplete final group. -/
theorem tokenLoop_spec (g : Grammar) (S : Lists (NK g)) (w : List Bool) (out : List Nat) (m : Nat) :
    NRuns (tokenLoop g) (tokenState g S w out m)
      (tokenState g S [] (out ++ ((ofBits w).map (fun t => symbolCode (tokChar t))))
        (m + (ofBits w).length)) (200 * w.length + 1) := by
  generalize hn : w.length = n
  induction n using Nat.strongRecOn generalizing w out m with
  | _ n ih =>
    subst n
    cases w with
    | nil =>
      have hx := nruns_loop_exit (i := inpR g) (c := .nonempty) (p := readToken g 4 [])
        (S := tokenState g S [] out m) (by rw [tokenState_input]; rfl)
      simpa [tokenLoop, ofBits] using hx
    | cons b w =>
      have hc : NTest.nonempty.eval (tokenState g S (b :: w) out m (inpR g)) = true := by
        rw [tokenState_input]; exact eval_nonempty_ne (by simp)
      by_cases h4 : 4 ≤ (b :: w).length
      · rcases w with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, w⟩⟩⟩ <;> try (simp only [List.length_cons, List.length_nil] at h4; omega)
        have hr := readToken_spec g S 4 [] (b :: b₁ :: b₂ :: b₃ :: w) out m
        simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
          List.nil_append, if_pos h4] at hr
        have hi := ih w.length (by simp; omega) w
          (out ++ [symbolCode (tokChar (bitsTokL [b, b₁, b₂, b₃]))]) (m + 1) rfl
        have hx := loop_continue hc hr hi
        simpa [tokenLoop, ofBits, bitsTokL, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hx.mono (show 130 + 4 * 4 + 1 + (200 * w.length + 1) ≤
            200 * (b :: b₁ :: b₂ :: b₃ :: w).length + 1 by simp; omega)
      · have hr := readToken_spec g S 4 [] (b :: w) out m
        simp only [if_neg h4] at hr
        have hd : (b :: w).drop 4 = [] := List.drop_eq_nil_of_le (by omega)
        rw [hd] at hr
        simp only [List.append_nil, Nat.add_zero] at hr
        have he := nruns_loop_exit (i := inpR g) (c := .nonempty) (p := readToken g 4 [])
          (S := tokenState g S [] out m) (by rw [tokenState_input]; rfl)
        have hx := loop_continue hc hr he
        have ho : ofBits (b :: w) = [] := by
          rcases w with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, w⟩⟩⟩ <;> simp_all [ofBits]
        simpa [tokenLoop, ho] using hx.mono (show 130 + 4 * 4 + 1 + 1 ≤ 200 * (b :: w).length + 1 by simp; omega)

def tokenWord (w : List Bool) : List Char := (ofBits w).map tokChar

def loadTokens (g : Grammar) : NProg (NK g) :=
  .seq (.prim (.pushZ (lenR g))) (.seq (tokenLoop g)
    (.seq (replaceRow (tmpR g) (inpR g) (workR g) (by packrat_regs) (by packrat_regs))
      (.prim (.pushZ (inpR g)))))

def tokenLoaded (g : Grammar) (w : List Bool) : Lists (NK g) :=
  ((nInit (NK g) w).set (lenR g) [(tokenWord w).length]).set (inpR g) (inputRow (tokenWord w))

theorem nruns_loadTokens (g : Grammar) (w : List Bool) :
    NRuns (loadTokens g) (nInit (NK g) w) (tokenLoaded g w) (220 * (w.length + 1)) := by
  have hwi : workR g ≠ inpR g := by packrat_regs
  have hwt : workR g ≠ tmpR g := by packrat_regs
  have hwl : workR g ≠ lenR g := by packrat_regs
  have pz := nruns_pushZ (lenR g) (nInit (NK g) w)
  have hstart : (nInit (NK g) w).set (lenR g) (nInit (NK g) w (lenR g) ++ [0]) =
      tokenState g (nInit (NK g) w) w [] 0 := by
    simp only [tokenState]
    lists_eq <;> simp_all [inpR, tmpR, lenR, nInit, Fin.mk.injEq]
  rw [hstart] at pz
  have lp := tokenLoop_spec g (nInit (NK g) w) w [] 0
  simp only [List.nil_append, Nat.zero_add] at lp
  let S := tokenState g (nInit (NK g) w) [] ((ofBits w).map (fun t => symbolCode (tokChar t))) (ofBits w).length
  have hw : S (workR g) = [] := by
    simp only [S, tokenState, Lists.set_ne _ _ hwl, Lists.set_ne _ _ hwt, Lists.set_ne _ _ hwi]
    simp [nInit, workR]
  have mv := nruns_replaceRow (tmpR g) (inpR g) (workR g) (by packrat_regs) (by packrat_regs)
    (by packrat_regs) S hw
  let S₁ := (S.set (inpR g) (S (tmpR g))).set (tmpR g) []
  have ez := nruns_pushZ (inpR g) S₁
  have hend : S₁.set (inpR g) (S₁ (inpR g) ++ [0]) = tokenLoaded g w := by
    simp only [S₁, S, tokenState, tokenLoaded, tokenWord, inputRow, List.map_map, Function.comp_def, List.length_map]
    lists_eq <;> simp_all [inpR, tmpR, lenR, nInit, Fin.mk.injEq]
  rw [hend] at ez
  have hlen : (S (tmpR g)).length = (ofBits w).length := by dsimp only [S]; rw [tokenState_tmp]; simp
  have hle := ofBits_length_le w
  refine (pz.seq (lp.seq (mv.seq ez))).mono ?_
  have hzero : S (inpR g) = [] := by dsimp only [S]; rw [tokenState_input]; rfl
  rw [hlen, hzero]
  simp only [List.length_nil]
  omega

/-- The complete PEG recognizer with the same token decoding as Macro PEG. -/
def tokenProgram (g : Grammar) : NProg (NK g) :=
  .seq (loadTokens g) (.seq (initTable g) (.seq (iterateBound g) (finish g)))

def tokenBudget (g : Grammar) (N : Nat) : Nat :=
  220 * (N + 1) + programCoeff g (fun _ => '0') * (N + 1) ^ 3

def tokenLanguage (g : Grammar) : Lang :=
  fun w => ∃ t, Derives g (.nt g.start) (tokenWord w) (.ok t [])

/-- From the actual bit input, the token recognizer halts with precisely the PEG answer. -/
theorem tokenProgram_halts (g : Grammar) (w : List Bool) :
    ∃ b S', NHalts (tokenProgram g) (nInit (NK g) w) b S' (tokenBudget g w.length) ∧
      (b = true ↔ tokenLanguage g w) := by
  have li := nruns_loadTokens g w
  have hi : tokenLoaded g w (inpR g) = inputRow (tokenWord w) := by simp [tokenLoaded]
  have hl : tokenLoaded g w (lenR g) = [(tokenWord w).length] := by
    simp only [tokenLoaded, Lists.set_ne _ _ (show lenR g ≠ inpR g by packrat_regs), Lists.set_same]
  have ht : tokenLoaded g w (tmpR g) = [] := by
    simp only [tokenLoaded, Lists.set_ne _ _ (show tmpR g ≠ inpR g by packrat_regs),
      Lists.set_ne _ _ (show tmpR g ≠ lenR g by packrat_regs)]
    simp [nInit, tmpR]
  have ho : ∀ j, tokenLoaded g w (oldR g j) = [] := by
    intro j
    simp only [tokenLoaded, Lists.set_ne _ _ (show oldR g j ≠ inpR g by packrat_regs),
      Lists.set_ne _ _ (show oldR g j ≠ lenR g by packrat_regs)]
    simp [nInit, oldR]
  have hn : ∀ j, tokenLoaded g w (nextR g j) = [] := by
    intro j
    simp only [tokenLoaded, Lists.set_ne _ _ (show nextR g j ≠ inpR g by packrat_regs),
      Lists.set_ne _ _ (show nextR g j ≠ lenR g by packrat_regs)]
    simp [nInit, nextR]
  obtain ⟨S₁, zi, h₁⟩ := nruns_initialize g (tokenWord w) (tokenLoaded g w) hi hl ht ho hn
  obtain ⟨S₂, it, h₂, _⟩ := nruns_iterateBound g (tokenWord w) 0 S₁ h₁
  simp only [Nat.zero_add] at h₂
  obtain ⟨S₃, fi⟩ := nhalts_finish g (tokenWord w) (bound g (tokenWord w)) S₂ h₂
  refine ⟨_, S₃, (li.seqH (zi.seqH (it.seqH fi))).mono ?_, ?_⟩
  · have hp := programCost_le g (fun _ => '0') (tokenWord w).length
    have hn : (tokenWord w).length ≤ w.length := by simpa [tokenWord] using ofBits_length_le w
    have hpow := Nat.mul_le_mul_left (programCoeff g (fun _ => '0'))
      (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 3)
    unfold programCost at hp
    unfold tokenBudget
    omega
  · simpa only [decide_eq_true_eq, tokenLanguage] using start_full_iff g (tokenWord w)

/-- PEG languages are in P under exactly the token encoding used by `FirstLanguage`. -/
theorem tokenLanguage_in_P (g : Grammar) : KEXP 0 (tokenLanguage g) := by
  apply nprog_in_P (K := NK g) (by unfold NK; omega) (tokenProgram g) (tokenLanguage g) (tokenBudget g)
  · exact isPoly_add (isPoly_mul (isPoly_const 220) (isPoly_add isPoly_id (isPoly_const 1)))
      (isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add isPoly_id (isPoly_const 1)) 3))
  · intro w
    exact tokenProgram_halts g w

end Shallot.PegSeparation
