import Complexity.Undec.TMSRSim

/-!
# Acceptance of a one-tape table reduces to reachability in a string rewriting system

`tm_sr`: a one-tape table `T` (rows of the right shape) reaches state `0` from the input `w` iff the start word
`tmStart T w` rewrites to the accepting word `tmAcc T` in `tmSRS T`.

- (→) every step is matched by rewrites (`fwd_step`), and once state `0` is reached everything but the state symbol
  is erased (`erase_zw`);
- (←) every word reachable from the start is the word of a reachable configuration with some trailing blanks, unless
  state `0` was reached (`Inv`, `inv_star`); the accepting word is no configuration's word.
-/

namespace Complexity.Undec

open Complexity

variable {T : TTable}

/-! ## Rewriting in context -/

/-- Rewrites compose. -/
theorem star_trans {R : SRS} {x y z : Word} (h1 : SRStar R x y) (h2 : SRStar R y z) : SRStar R x z := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact SRStar.step h (ih h2)

/-- Rewrites inside a context. -/
theorem star_ctx {R : SRS} {x y : Word} (P S : Word) (h : SRStar R x y) : SRStar R (P ++ x ++ S) (P ++ y ++ S) := by
  induction h with
  | refl => exact SRStar.refl _
  | step h _ ih =>
    cases h with
    | rw u v l r hr =>
      exact SRStar.step (step_of hr (u := P ++ u) (v := v ++ S) (by simp) (by simp)) ih

/-- Everything right of the accepting state is erased. -/
theorem erase_right (T : TTable) : ∀ Rs : Word, (∀ z ∈ Rs, z < bnd T + 2) →
    SRStar (tmSRS T) (stS T 0 :: Rs) [stS T 0]
  | [], _ => SRStar.refl _
  | x :: Rs, h =>
    SRStar.step (step_of (eraseR_mem (h x (by simp))) (u := []) (v := Rs) (by simp) (by simp))
      (erase_right T Rs (fun z hz => h z (by simp [hz])))

/-- Everything left of the accepting state is erased. -/
theorem erase_left (T : TTable) : ∀ Ls : Word, (∀ z ∈ Ls, z < bnd T + 2) →
    SRStar (tmSRS T) (Ls ++ [stS T 0]) [stS T 0]
  | [], _ => SRStar.refl _
  | x :: Ls, h => by
    have ih := star_ctx [x] [] (erase_left T Ls (fun z hz => h z (by simp [hz])))
    simp only [List.append_nil] at ih
    refine star_trans (by simpa using ih) (SRStar.step ?_ (SRStar.refl _))
    exact step_of (eraseL_mem (h x (by simp))) (u := []) (v := []) (by simp) (by simp)

/-- The word of a configuration in state `0` rewrites to the accepting word. -/
theorem erase_zw (T : TTable) {L R : List Nat} (hL : ∀ z ∈ L, z < bnd T) (hR : ∀ z ∈ R, z < bnd T) :
    SRStar (tmSRS T) (zw T 0 L R) [stS T 0] := by
  have h1 := star_ctx (lbS T :: L) [] (erase_right T (R ++ [rbS T]) (by
    intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · have := hR z hz; omega
    · unfold rbS; omega))
  have h2 := erase_left T (lbS T :: L) (by
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · unfold lbS; omega
    · have := hL z hz; omega)
  refine star_trans ?_ h2
  simpa [zw] using h1

/-! ## The invariant of reachable words -/

/-- A reachable word: state `0` was reached, or it is the word of a reachable configuration with trailing blanks. -/
def Inv (T : TTable) (w : List Bool) (x : Word) : Prop :=
  (∃ n, (frun T (finit 1 w) n).state = 0) ∨ ∃ n j, x = cword T (padC (frun T (finit 1 w) n) j)

/-- The start word satisfies the invariant. -/
theorem inv_start (T : TTable) (w : List Bool) : Inv T w (tmStart T w) :=
  Or.inr ⟨0, 0, by simp [tmStart, frun, finit_one, padC, mk]⟩

/-- Every rewrite keeps the invariant. -/
theorem inv_step (hT : Univ.RowsOK T) (hk : T.k = 1) {w : List Bool} {x y : Word} (hx : Inv T w x)
    (h : SRStep (tmSRS T) x y) : Inv T w y := by
  rcases hx with hx | ⟨n, j, rfl⟩
  · exact Or.inl hx
  · obtain ⟨q, p, t, hc, hp, ht, _⟩ := frun_good hT hk w n
    by_cases hq0 : q = 0
    · exact Or.inl ⟨n, by rw [hc, hq0]; rfl⟩
    · have hp' : p ≤ (t ++ List.replicate j 0).length := by simp; omega
      have ht' : ∀ z ∈ t ++ List.replicate j 0, z < bnd T := by
        intro z hz
        simp only [List.mem_append, List.mem_replicate] at hz
        rcases hz with hz | ⟨_, rfl⟩
        · exact ht z hz
        · unfold bnd; omega
      rcases back_step hT hk hq0 hp' ht' h (by rw [hc]; rfl) with hy | hy
      · obtain ⟨j', hj⟩ := fstep_pad hT hk hp j
        refine Or.inr ⟨n + 1, j', ?_⟩
        show y = cword T (padC (fstep T (frun T (finit 1 w) n)) j')
        rw [hc, ← hj, hy]; rfl
      · refine Or.inr ⟨n, j + 1, ?_⟩
        rw [hc, hy]
        simp [padC, mk, List.replicate_succ']

/-- Every reachable word satisfies the invariant. -/
theorem inv_star (hT : Univ.RowsOK T) (hk : T.k = 1) {w : List Bool} {x y : Word} (h : SRStar (tmSRS T) x y) :
    Inv T w x → Inv T w y := by
  induction h with
  | refl => exact id
  | step hs _ ih => exact fun hx => ih (inv_step hT hk hx hs)

/-- The accepting word is the word of no configuration. -/
theorem cword_ne_acc (T : TTable) (c : FCfg) : cword T c ≠ tmAcc T := by
  intro h
  simp [cword, zw, tmAcc, stS, lbS] at h

/-- Every run is matched by rewrites. -/
theorem fwd_run (hT : Univ.RowsOK T) (hk : T.k = 1) (w : List Bool) :
    ∀ n, SRStar (tmSRS T) (tmStart T w) (cword T (frun T (finit 1 w) n))
  | 0 => SRStar.refl _
  | n + 1 => star_trans (fwd_run hT hk w n) (fwd_step hT hk (frun_good hT hk w n))

/-! ## The reduction -/

/-- **Acceptance of a one-tape table is reachability in its rewriting system.** -/
theorem tm_sr (T : TTable) (hT : Univ.RowsOK T) (hk : T.k = 1) (w : List Bool) :
    (∃ t, (frun T (finit 1 w) t).state = 0) ↔ SRStar (tmSRS T) (tmStart T w) (tmAcc T) := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨q, p, t, hc, _, ht, _⟩ := frun_good hT hk w n
    have h := fwd_run hT hk w n
    rw [hc] at h hn
    simp only [mk] at hn
    subst hn
    refine star_trans h ?_
    exact erase_zw T (fun z hz => ht z (List.mem_of_mem_take hz)) (fun z hz => ht z (List.mem_of_mem_drop hz))
  · intro h
    rcases inv_star hT hk h (inv_start T w) with h' | ⟨n, j, h'⟩
    · exact h'
    · exact absurd h'.symm (cword_ne_acc T _)

/-! ## Symbols -/

/-- All rules use symbols below `tmSyms T`. -/
theorem tmSRS_below (T : TTable) : RulesBelow (tmSyms T) (tmSRS T) := by
  intro p hp
  have hb : 3 ≤ bnd T := by unfold bnd; omega
  rcases mem_tmSRS hp with ⟨q, a, r, hq, ha, _, _, hr, hc⟩ | ⟨q, hq, _, _, rfl⟩ | ⟨x, hx, rfl | rfl⟩
  · have hm := List.mem_of_getElem? hr
    have h1 := row_state_lt hm
    have h2 := row_wr_lt hm
    cases hmv : mv r with
    | R =>
      rw [cellRules_R hmv] at hc
      simp only [List.mem_singleton] at hc
      subst hc
      refine ⟨?_, ?_⟩ <;> intro z hz <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hz <;>
        simp only [tmSyms, stS] at hz ⊢ <;> omega
    | S =>
      rw [cellRules_S hmv] at hc
      simp only [List.mem_singleton] at hc
      subst hc
      refine ⟨?_, ?_⟩ <;> intro z hz <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hz <;>
        simp only [tmSyms, stS] at hz ⊢ <;> omega
    | L =>
      rw [cellRules_L hmv] at hc
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
      rcases hc with rfl | ⟨c, hc, rfl⟩
      · refine ⟨?_, ?_⟩ <;> intro z hz <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hz <;>
          simp only [tmSyms, stS, lbS] at hz ⊢ <;> omega
      · refine ⟨?_, ?_⟩ <;> intro z hz <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hz <;>
          simp only [tmSyms, stS] at hz ⊢ <;> omega
  · refine ⟨?_, ?_⟩ <;> intro z hz <;> simp only [endRule, List.mem_cons, List.not_mem_nil, or_false] at hz <;>
      simp only [tmSyms, stS, rbS] at hz ⊢ <;> omega
  · refine ⟨?_, ?_⟩ <;> intro z hz <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hz <;>
      simp only [tmSyms, stS] at hz ⊢ <;> omega
  · refine ⟨?_, ?_⟩ <;> intro z hz <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hz <;>
      simp only [tmSyms, stS] at hz ⊢ <;> omega

/-- The start word uses symbols below `tmSyms T`. -/
theorem tmStart_below (T : TTable) (w : List Bool) : ∀ a ∈ tmStart T w, a < tmSyms T := by
  intro z hz
  have hb : 3 ≤ bnd T := by unfold bnd; omega
  simp only [tmStart, finit_one, cword, mk, zw, List.headD_cons, List.take_zero, List.drop_zero, List.nil_append,
    List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hz
  simp only [tmSyms]
  rcases hz with rfl | rfl | ⟨b, _, rfl⟩ | rfl
  · unfold lbS; omega
  · unfold stS; omega
  · cases b <;> simp [bitSym] <;> omega
  · unfold rbS; omega

/-- The accepting word uses symbols below `tmSyms T`. -/
theorem tmAcc_below (T : TTable) : ∀ a ∈ tmAcc T, a < tmSyms T := by
  intro z hz
  have hb : 3 ≤ bnd T := by unfold bnd; omega
  simp only [tmAcc, List.mem_singleton] at hz
  subst hz
  unfold tmSyms stS; omega

/-- Every rule has a nonempty left side and a nonempty right side. -/
theorem tmSRS_nonempty (T : TTable) : ∀ p ∈ tmSRS T, p.1 ≠ [] ∧ p.2 ≠ [] := by
  intro p hp
  rcases mem_tmSRS hp with ⟨q, a, r, _, _, _, _, _, hc⟩ | ⟨q, _, _, _, rfl⟩ | ⟨x, _, rfl | rfl⟩
  · cases hmv : mv r with
    | R => rw [cellRules_R hmv] at hc; simp only [List.mem_singleton] at hc; subst hc; simp
    | S => rw [cellRules_S hmv] at hc; simp only [List.mem_singleton] at hc; subst hc; simp
    | L =>
      rw [cellRules_L hmv] at hc
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
      rcases hc with rfl | ⟨c, _, rfl⟩ <;> simp
  · simp [endRule]
  · simp
  · simp

end Complexity.Undec
