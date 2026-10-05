import MacroPeg.HigherOrder.ExpSpace.Address

/-!
# The simulation: order-2 Macro PEG is 2-EXPTIME-hard

A tape value `T` represents the tape `t : address ↦ bit` (`RepT`) when, for every address parser `A` representing
`v`, the test `T A` at the start of the input succeeds iff `t v`. The initial tape and writing keep this
(`T0_rep`, `wr_rep`). The rule of state `q`, called with a head and a tape representing a configuration all of whose
branches are finite, succeeds without consuming the input iff the configuration accepts (`sim`); hence the grammar
consumes the whole encoding of `w` iff the machine accepts `w` (`atm2_reduction`).
-/

namespace Shallot.MacroPeg.ExpSpace

open Shallot.MacroPeg (ATM Dir Kind sitesStr)
open Shallot.MacroPeg.HO

/-! ## Tests built from tests -/

section Tests

variable {g : HGrammar}

theorem test_guard_test {C X Y : HExp} {x : List Char} {c b₁ b₂ : Bool} (hC : Test g C x c) (hX : Test g X x b₁)
    (hY : Test g Y x b₂) : Test g (.alt (.seq (HExp.andP C) X) (.seq (.notP C) Y)) x (if c then b₁ else b₂) := by
  cases c with
  | true =>
    obtain ⟨y, hy⟩ := hC
    cases b₁ with
    | true => obtain ⟨z, hz⟩ := hX; exact ⟨_, HO.guard_pos hy hz⟩
    | false => exact HO.guard_pos hy hX
  | false =>
    cases b₂ with
    | true => obtain ⟨z, hz⟩ := hY; exact ⟨_, HO.guard_neg hC hz⟩
    | false => exact HO.guard_neg hC hY

theorem test_bitC (b : Bool) (x : List Char) : Test g (bitC b) x b := by
  cases b
  · exact hobs_fail
  · exact ⟨_, hobs_eps⟩

/-- A β-step. -/
theorem hobs_beta {τ : HO.Ty} {B A : HExp} {x : List Char} {r : Option (List Char)} (h : HObs g (HExp.inst A 0 B) x r) :
    HObs g (.app (.lam τ B) A) x r :=
  hobs_expand rfl h

theorem test_beta {τ : HO.Ty} {B A : HExp} {x : List Char} {b : Bool} (h : Test g (HExp.inst A 0 B) x b) :
    Test g (.app (.lam τ B) A) x b := by
  cases b with
  | true => obtain ⟨y, hy⟩ := h; exact ⟨y, hobs_beta hy⟩
  | false => exact hobs_beta h

end Tests

section Tapes

variable (M : ATM) (w : List Bool)

local notation "G" => g2 M
local notation "n" => w.length
local notation "L" => sfxS w 0

/-- `T` represents the tape `t`. -/
def RepT (T : HExp) (t : List Bool → Bool) : Prop :=
  HExp.Cl 0 T ∧ ∀ A v, RepA M w A v → Test G (.app T A) L (t v)

variable {M w}

theorem inst_rcall (A : HExp) (k i : Nat) (as : List HExp) :
    HExp.inst A k (rcall i as) = rcall i (as.map (HExp.inst A k)) := by
  simp only [rcall, inst_apps]; rfl

/-- **The initial tape.** -/
theorem T0_rep : RepT M w (T0 M) (initTape w) := by
  refine ⟨cl_rcall (k := 1) (fun a ha => by simp at ha; rw [ha]; show 0 < 1; omega), fun A v hA => ?_⟩
  apply test_beta
  simp only [HExp.andP, HExp.inst, inst_rcall, List.map_cons, List.map_nil]
  have h := sc_ok hA n 0 (by omega)
  simp only [List.drop_zero] at h
  show Test G (HExp.andP (rcall (rSC M) [A])) L (initTape w v)
  unfold initTape
  cases hb : (v.zip w).any (fun p => p.1 && p.2) with
  | true => rw [hb] at h; obtain ⟨y, hy⟩ := h; exact ⟨_, hobs_and_some hy⟩
  | false => rw [hb] at h; exact hobs_and_none h

/-- **Writing**: the closure `wrE M H T b` represents `t` with `b` written at the head. -/
theorem wr_rep {H T : HExp} {vh : List Bool} {t : List Bool → Bool} (hH : RepA M w H vh) (hT : RepT M w T t)
    (b : Bool) : RepT M w (wrE M H T b) (fun a => if a = vh then b else t a) := by
  have hH1 : HExp.Cl 1 H := HExp.Cl.mono hH.1 (Nat.zero_le 1)
  have hT1 : HExp.Cl 1 T := HExp.Cl.mono hT.1 (Nat.zero_le 1)
  have hbc : ∀ k, HExp.Cl k (bitC b) := fun k => by cases b <;> exact trivial
  refine ⟨?_, fun A v hA => ?_⟩
  · have heq : HExp.Cl 1 (rcall (rEQ M) [.var 0, H]) := cl_rcall (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · show 0 < 1; omega
      · exact hH1)
    exact ⟨⟨heq, hbc 1⟩, ⟨heq, ⟨hT1, show 0 < 1 by omega⟩⟩⟩
  apply test_beta
  have hiH : HExp.inst A 0 H = H := inst_of_cl A hH.1 (Nat.zero_le 0)
  have hiT : HExp.inst A 0 T = T := inst_of_cl A hT.1 (Nat.zero_le 0)
  have hib : HExp.inst A 0 (bitC b) = bitC b := by cases b <;> rfl
  simp only [HExp.andP, HExp.inst, inst_rcall, List.map_cons, List.map_nil, hiH, hiT, hib]
  have he := eq_ok hA hH n 0 (by omega)
  simp only [List.drop_zero] at he
  have h := test_guard_test (C := rcall (rEQ M) [A, H]) he (test_bitC (g := G) b L) (hT.2 A v hA)
  by_cases hv : v = vh
  · simpa [HExp.andP, hv] using h
  · simpa [HExp.andP, hv] using h

end Tapes

/-! ## Branches and the simulation -/

section Machine

variable (M : ATM) (w : List Bool)

local notation "G" => g2 M
local notation "n" => w.length
local notation "L" => sfxS w 0

/-- Accept: succeed without consuming; reject: fail. -/
def res (b : Bool) : Option (List Char) := if b then some (sfxS w 0) else none

/-- The successor configuration's rule, for every representation of its head and tape. -/
def Next (c : Cfg) (tr : Nat × Bool × Dir) (b : Bool) : Prop :=
  ∀ H' T', RepA M w H' (succOf c tr).h → RepT M w T' (succOf c tr).t →
    HObs G (rcall (succOf c tr).q [H', T']) L (res w b)


variable {M w}

theorem all_test {H : HExp} {v : List Bool} (hH : RepA M w H v) :
    Test G (rcall (rALL1 M) [H]) L (v.all id) := by simpa using all1_ok hH n 0 (by omega)

theorem none_test {H : HExp} {v : List Bool} (hH : RepA M w H v) :
    Test G (rcall (rALL0 M) [H]) L (v.all (! ·)) := by simpa using all0_ok hH n 0 (by omega)

theorem guard_test_pos {C X Y : HExp} {x : List Char} {r : Option (List Char)} (hC : Test G C x true)
    (hX : HObs G X x r) : HObs G (.alt (.seq (HExp.andP C) X) (.seq (.notP C) Y)) x r := by
  obtain ⟨y, hy⟩ := hC; exact HO.guard_pos hy hX

theorem guard_test_neg {C X Y : HExp} {x : List Char} {r : Option (List Char)} (hC : Test G C x false)
    (hY : HObs G Y x r) : HObs G (.alt (.seq (HExp.andP C) X) (.seq (.notP C) Y)) x r := HO.guard_neg hC hY

/-- One branch: write, move (staying at the ends), continue. -/
theorem br_ok {c : Cfg} {H T : HExp} (hH : RepA M w H c.h) (hT : RepT M w T c.t) (tr : Nat × Bool × Dir) {b : Bool}
    (hnext : Next M w c tr b) : HObs G (brE M H H T tr) L (res w b) := by
  obtain ⟨q', b', d⟩ := tr
  have hwr := wr_rep hH hT b'
  cases d with
  | left =>
    unfold brE
    cases hz : c.h.all (! ·) with
    | true =>
      have hc := none_test hH; rw [hz] at hc
      refine guard_test_pos hc (hnext H _ ?_ hwr)
      simp only [succOf, moveH, vdec, hz, ↓reduceIte]; exact hH
    | false =>
      have hc := none_test hH; rw [hz] at hc
      refine guard_test_neg hc (hnext _ _ ?_ hwr)
      simp only [succOf, moveH, vdec, hz, Bool.false_eq_true, ↓reduceIte]; exact dec_rep hH
  | right =>
    unfold brE
    cases ho : c.h.all id with
    | true =>
      have hc := all_test hH; rw [ho] at hc
      refine guard_test_pos hc (hnext H _ ?_ hwr)
      simp only [succOf, moveH, vinc, ho, ↓reduceIte]; exact hH
    | false =>
      have hc := all_test hH; rw [ho] at hc
      refine guard_test_neg hc (hnext _ _ ?_ hwr)
      simp only [succOf, moveH, vinc, ho, Bool.false_eq_true, ↓reduceIte]; exact inc_rep hH

theorem chain_all {c : Cfg} {H T : HExp} (hH : RepA M w H c.h) (hT : RepT M w T c.t) :
    ∀ trs : List (Nat × Bool × Dir), (∀ tr ∈ trs, ∃ b, Val M (succOf c tr) b ∧ Next M w c tr b) →
      ∃ bs, ValList M (trs.map (succOf c)) bs ∧ HObs G (allChainH (trs.map (brE M H H T))) L (res w (bs.all id))
  | [], _ => ⟨[], .nil, hobs_eps⟩
  | tr :: trs, hall => by
    obtain ⟨b, hv, hn⟩ := hall tr List.mem_cons_self
    obtain ⟨bs, hvs, hrest⟩ := chain_all hH hT trs (fun t ht => hall t (List.mem_cons_of_mem _ ht))
    refine ⟨b :: bs, .cons _ _ _ _ hv hvs, ?_⟩
    have hbr := br_ok hH hT tr hn
    simp only [List.map_cons, allChainH]
    cases b with
    | true => exact hobs_seq_ok (hobs_and_some hbr) (by simpa [res] using hrest)
    | false => exact hobs_seq_fail (hobs_and_none hbr)

theorem chain_any {c : Cfg} {H T : HExp} (hH : RepA M w H c.h) (hT : RepT M w T c.t) :
    ∀ trs : List (Nat × Bool × Dir), (∀ tr ∈ trs, ∃ b, Val M (succOf c tr) b ∧ Next M w c tr b) →
      ∃ bs, ValList M (trs.map (succOf c)) bs ∧ HObs G (anyChainH (trs.map (brE M H H T))) L (res w (bs.any id))
  | [], _ => ⟨[], .nil, hobs_fail⟩
  | tr :: trs, hall => by
    obtain ⟨b, hv, hn⟩ := hall tr List.mem_cons_self
    obtain ⟨bs, hvs, hrest⟩ := chain_any hH hT trs (fun t ht => hall t (List.mem_cons_of_mem _ ht))
    refine ⟨b :: bs, .cons _ _ _ _ hv hvs, ?_⟩
    have hbr := br_ok hH hT tr hn
    simp only [List.map_cons, anyChainH]
    cases b with
    | true => exact hobs_alt_ok (by simpa [res] using hbr)
    | false => exact hobs_alt_fail (by simpa [res] using hbr) (by simpa [res] using hrest)

theorem state_call {q : Nat} (hq : q < M.states) {H T : HExp} (hH : HExp.Cl 0 H) (hT : HExp.Cl 0 T)
    {r : Option (List Char)} (h : HObs G (stateE M q H T H T) L r) : HObs G (rcall q [H, T]) L r :=
  hobs_call (g2_state M hq) rfl (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hH
      · exact hT)
    (by rw [show [H, T].reverse = [T, H] from rfl, inst_state]; exact h)

/-- **The simulation.** -/
theorem sim (hM : M.WF) : ∀ c, Halts M c → c.q < M.states →
    ∃ b, Val M c b ∧ ∀ H T, RepA M w H c.h → RepT M w T c.t → HObs G (rcall c.q [H, T]) L (res w b) := by
  intro c hc
  induction hc with
  | mk c _ ih =>
    intro hq
    have hnext : ∀ tr ∈ M.delta c.q (c.t c.h), ∃ b, Val M (succOf c tr) b ∧ Next M w c tr b := by
      intro tr htr
      have hmem : succOf c tr ∈ succs M c := List.mem_map_of_mem htr
      exact ih _ hmem (hM.2 _ _ tr htr)
    have hvals := vals_exist M c _ (fun tr htr => (hnext tr htr).imp fun _ h => h.1)
    have hrun : ∀ {H T : HExp} {r : Option (List Char)}, RepA M w H c.h → RepT M w T c.t →
        HObs G (transE M c.q (c.t c.h) H H T) L r → HObs G (rcall c.q [H, T]) L r := by
      intro H T r hH hT htr
      apply state_call hq hH.1 hT.1
      have hread := hT.2 H c.h hH
      unfold stateE
      cases hb : c.t c.h with
      | true => rw [hb] at hread htr; exact guard_test_pos hread htr
      | false => rw [hb] at hread htr; exact guard_test_neg hread htr
    cases hk : M.kind c.q with
    | acc =>
      refine ⟨true, .acc c hk, fun H T hH hT => hrun hH hT ?_⟩
      simp only [transE, hk, res, if_pos]; exact hobs_eps
    | rej =>
      refine ⟨false, .rej c hk, fun H T hH hT => hrun hH hT ?_⟩
      simp only [transE, hk, res, Bool.false_eq_true, ↓reduceIte]; exact hobs_fail
    | univ =>
      obtain ⟨bs, hbs⟩ := hvals
      refine ⟨bs.all id, .univ c bs hk hbs, fun H T hH hT => hrun hH hT ?_⟩
      obtain ⟨bs', hbs', hobs⟩ := chain_all hH hT _ hnext
      rw [valList_functional M hbs' hbs] at hobs
      simp only [transE, hk]; exact hobs
    | exist =>
      obtain ⟨bs, hbs⟩ := hvals
      refine ⟨bs.any id, .exist c bs hk hbs, fun H T hH hT => hrun hH hT ?_⟩
      obtain ⟨bs', hbs', hobs⟩ := chain_any hH hT _ hnext
      rw [valList_functional M hbs' hbs] at hobs
      simp only [transE, hk]; exact hobs

theorem star_any_all : ∀ x : List Char, HObs G (.star .any) x (some []) := fun x =>
  hobs_of_peg (e := .star .any) trivial (Shallot.MacroPeg.star_any_all (g := (⟨[]⟩ : Shallot.MacroPeg.MGrammar)) x)

/-- **The reduction.** If every branch of `M` on `w` is finite, the order-2 grammar `g2 M` consumes the whole encoding
of `w` iff `M` accepts `w` with its exponentially long tape. -/
theorem atm2_reduction (hM : M.WF) (hh : Halts M (init M w)) :
    HObs G (start2 M) (sitesStr w 0) (some []) ↔ Accepts M w := by
  have hL : sfxS w 0 = sitesStr w 0 := by simp [sfxS]
  obtain ⟨b, hv, hobs⟩ := sim (w := w) hM (init M w) hh hM.1
  have hcall := hobs H0 (T0 M) H0_rep T0_rep
  cases b with
  | true =>
    simp only [res, if_pos] at hcall
    have hstart : HObs G (start2 M) (sitesStr w 0) (some []) := by
      rw [← hL]; exact hobs_seq_ok hcall (star_any_all _)
    exact ⟨fun _ => hv, fun _ => hstart⟩
  | false =>
    simp only [res, Bool.false_eq_true, ↓reduceIte] at hcall
    have hstart : HObs G (start2 M) (sitesStr w 0) none := by rw [← hL]; exact hobs_seq_fail hcall
    constructor
    · intro h; have := hobs_det h hstart; cases this
    · intro h; have := val_functional M hv true h; cases this

end Machine

end Shallot.MacroPeg.ExpSpace
