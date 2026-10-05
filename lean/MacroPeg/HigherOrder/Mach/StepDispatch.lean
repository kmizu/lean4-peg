import MacroPeg.HigherOrder.Mach.StepSimple

/-!
# Dispatching on the token and on the frame

`caseTop` on an empty stack runs its default (`caseTop_empty`). From programs for the tokens of an expression
(`TokOK`) the program `exprP ts` reads an expression (`exprP_frame`); from programs for the frames (`FrameOK`) the
program `stepP fs` does one step of the reading machine (`stepP_ok`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

variable {K : Nat}

theorem caseTop_empty (i : Fin K) : ∀ (ps : List (NProg K)) (S : Lists K), S i = [] → ∀ (b : Bool),
    NHalts (caseTop i ps (.halt b)) S b S (2 * ps.length + 1)
  | [], S, _, b => nhalts_halt b S
  | p :: ps, S, hS, b => by
    have h₁ := nruns_prim (.dec i) S
    have e : NPrim.apply (.dec i) S = S := by
      simp only [NPrim.apply, mapTop]
      rw [hS]; simp only [List.dropLast_nil, List.getLast?_nil, Option.map_none, Option.toList_none,
        List.append_nil]
      rw [← hS, Lists.set_get_self]
    rw [e] at h₁
    have h₂ := caseTop_empty i ps S hS b
    exact ((h₁.seqH h₂).iteF (by rw [hS]; rfl)).mono (by simp; omega)

/-! ## Reading an expression: dispatch on the token -/

/-- Read an expression, given a program for each of the tokens `0`–`12`. -/
def exprP (ts : List (NProg NK)) : NProg NK := caseTop TK ts (.halt false)

theorem readExpr_other (s : PSt) (K r : List Nat) {k : Nat} (htk : s.tk = k :: r) (hk : 13 ≤ k) :
    readExpr s K = s.fail := by
  unfold readExpr
  split <;> first | rfl | (rename_i h; rw [htk] at h; simp at h <;> omega)

theorem readExpr_nil (s : PSt) (K : List Nat) (htk : s.tk = []) : readExpr s K = s.fail := by
  unfold readExpr; rw [htk]

theorem enc_ctl_tk (s : PSt) (K r : List Nat) :
    (enc { s with ctl := K }).set TK r.reverse = enc { s with ctl := K, tk := r } :=
  (enc_with_tk { s with ctl := K } r).symm

theorem exprP_frame (ts : List (NProg NK)) (hlen : ts.length = 13) (s : PSt) (K : List Nat) (hc : s.ctl = 0 :: K)
    {T : Nat} (hts : ∀ k (hk : k < ts.length) r, s.tk = k :: r → TokOK ts[k] s K r T) :
    FrameOK (exprP ts) s K (T + 30) := by
  have hp : pstep s = readExpr s K := by simp only [pstep, hc]
  rcases htk : s.tk with _ | ⟨k, r⟩
  · have he := readExpr_nil s K htk
    have x := caseTop_empty TK ts (enc { s with ctl := K }) (by show s.tk.reverse = []; rw [htk]; rfl) false
    exact ⟨fun h => absurd h (by rw [hp, he]; simp [PSt.fail]), fun _ => ⟨_, x.mono (by omega)⟩⟩
  · have hS : (enc { s with ctl := K }) TK = r.reverse ++ [k] := by show s.tk.reverse = _; rw [htk]; simp
    by_cases hk : k < 13
    · have ht := hts k (by omega) r htk
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [hp] at h ⊢
        have x := caseTop_runs TK ts (.halt false) k (by omega) _ _ hS _ _ (by rw [enc_ctl_tk]; exact ht.1 h)
        exact x.mono (by omega)
      · rw [hp] at h
        obtain ⟨S', x⟩ := ht.2 h
        exact ⟨S', (caseTop_halts TK ts (.halt false) k (by omega) _ _ hS false S' _
          (by rw [enc_ctl_tk]; exact x)).mono (by omega)⟩
    · have he := readExpr_other s K r htk (by omega)
      have hS' : (enc { s with ctl := K }) TK = r.reverse ++ [(k - 13) + ts.length] := by
        rw [hS, hlen]; congr 2; omega
      have x := caseTop_default TK ts (.halt false) (k - 13) _ _ hS' false _ 1 (nhalts_halt false _)
      exact ⟨fun h => absurd h (by rw [hp, he]; simp [PSt.fail]), fun _ => ⟨_, x.mono (by omega)⟩⟩

/-! ## One step: dispatch on the frame -/

/-- The program `p` does one step of the reading machine from `s`. -/
def StepOK (p : NProg NK) (s : PSt) (T : Nat) : Prop :=
  ((pstep s).ok = true → NRuns p (enc s) (enc (pstep s)) T) ∧
    ((pstep s).ok = false → ∃ S', NHalts p (enc s) false S' T)

/-- One step, given a program for each of the frames `0`–`18`. -/
def stepP (fs : List (NProg NK)) : NProg NK := caseTop CTL fs (.halt false)

theorem pstep_other (s : PSt) {k : Nat} {K : List Nat} (hc : s.ctl = k :: K) (hk : 19 ≤ k) : pstep s = s.fail := by
  unfold pstep
  split <;> first | rfl | (rename_i h; rw [hc] at h; simp at h <;> omega)

theorem stepP_ok (fs : List (NProg NK)) (hlen : fs.length = 19) (s : PSt) (hne : s.ctl ≠ []) {T : Nat}
    (hfs : ∀ k (hk : k < fs.length) K, s.ctl = k :: K → FrameOK fs[k] s K T) : StepOK (stepP fs) s (T + 40) := by
  rcases hc : s.ctl with _ | ⟨k, K⟩
  · exact absurd hc hne
  · have hS : (enc s) CTL = K.reverse ++ [k] := by show s.ctl.reverse = _; rw [hc]; simp
    have hset : (enc s).set CTL K.reverse = enc { s with ctl := K } := (enc_with_ctl s K).symm
    by_cases hk : k < 19
    · have hf := hfs k (by omega) K hc
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact (caseTop_runs CTL fs (.halt false) k (by omega) _ _ hS _ _ (by rw [hset]; exact hf.1 h)).mono
          (by omega)
      · obtain ⟨S', x⟩ := hf.2 h
        exact ⟨S', (caseTop_halts CTL fs (.halt false) k (by omega) _ _ hS false S' _
          (by rw [hset]; exact x)).mono (by omega)⟩
    · have he := pstep_other s hc (by omega)
      have hS' : (enc s) CTL = K.reverse ++ [(k - 19) + fs.length] := by rw [hS, hlen]; congr 2; omega
      have x := caseTop_default CTL fs (.halt false) (k - 19) _ _ hS' false _ 1 (nhalts_halt false _)
      exact ⟨fun h => absurd h (by rw [he]; simp [PSt.fail]), fun _ => ⟨_, x.mono (by omega)⟩⟩

/-! ## The reading loop -/

theorem pot_tk (s : PSt) : s.tk.length ≤ pot s := by unfold pot; omega

/-- A step keeps the verdict, or stops the machine. -/
theorem pstep_ok_or (s : PSt) : (pstep s).ok = s.ok ∨ (pstep s).ctl = [] := by
  unfold pstep readExpr readType binDone unDone
  repeat' split
  all_goals simp [PSt.fail, PSt.leaf]

/-- Run the reading machine to its end: `n` rounds of `p` (at least the potential plus one) reach `pruns s n`, or
stop rejecting where the machine fails. -/
theorem readLoop (p : NProg NK) (N T : Nat)
    (hstep : ∀ s, MInv s → s.ok = true → s.ctl ≠ [] → s.tk.length + tsize s ≤ N → StepOK p s T) :
    ∀ (n : Nat) (s : PSt), pot s + 1 ≤ n → MInv s → s.ok = true → pot s + tsize s + n ≤ N →
      ((pruns s n).ok = true → NRuns (.loop CTL .nonempty p) (enc s) (enc (pruns s n)) (n * (T + 1) + 1)) ∧
      ((pruns s n).ok = false → ∃ S', NHalts (.loop CTL .nonempty p) (enc s) false S' (n * (T + 1) + 1))
  | 0, _, h, _, _, _ => absurd h (by omega)
  | n + 1, s, hn, hi, hs, hN => by
    by_cases hc : s.ctl = []
    · rw [pruns_halted hc]
      have hex : NTest.nonempty.eval ((enc s) CTL) = false := by show NTest.nonempty.eval s.ctl.reverse = false; rw [hc]; rfl
      exact ⟨fun _ => (nruns_loop_exit hex).mono (by omega), fun h => absurd hs (by rw [h]; simp)⟩
    · have hin : NTest.nonempty.eval ((enc s) CTL) = true := by
        show NTest.nonempty.eval s.ctl.reverse = true
        exact eval_nonempty_ne (by simpa using hc)
      have hst := hstep s hi hs hc (by have := pot_tk s; omega)
      rw [pruns_succ]
      by_cases hok : (pstep s).ok = true
      · have x₁ := hst.1 hok
        by_cases hc₁ : (pstep s).ctl = []
        · rw [pruns_halted hc₁]
          have hex : NTest.nonempty.eval ((enc (pstep s)) CTL) = false := by
            show NTest.nonempty.eval (pstep s).ctl.reverse = false; rw [hc₁]; rfl
          refine ⟨fun _ => (NRuns.loopStep hin x₁ (nruns_loop_exit hex)).mono ?_, fun h => absurd hok (by rw [h]; simp)⟩
          rw [Nat.succ_mul]; omega
        · have hlow : pot (pstep s) < pot s := (pstep_lowers s hc).resolve_left hc₁
          have hsz := pstep_size s
          have ih := readLoop p N T hstep n (pstep s) (by omega) (pstep_minv hi) hok (by omega)
          refine ⟨fun h => (NRuns.loopStep hin x₁ (ih.1 h)).mono ?_, fun h => ?_⟩
          · rw [Nat.succ_mul]; omega
          · obtain ⟨S', x⟩ := ih.2 h
            obtain ⟨t₁, ht₁, e₁⟩ := x₁
            obtain ⟨t₂, ht₂, e₂⟩ := x
            exact ⟨S', t₁ + 1 + t₂, by rw [Nat.succ_mul]; omega, .loopC trivial hin e₁ e₂⟩
      · have hf : (pstep s).ok = false := by simpa using hok
        obtain ⟨S', x⟩ := hst.2 hf
        have hc₁ : (pstep s).ctl = [] := by
          rcases pstep_ok_or s with h | h
          · rw [h, hs] at hf; cases hf
          · exact h
        rw [pruns_halted hc₁]
        exact ⟨fun h => absurd hf (by rw [h]; simp), fun _ => ⟨S', (NHalts.loopIn hin x).mono (by rw [Nat.succ_mul]; omega)⟩⟩

end Shallot.MacroPeg.Mach
