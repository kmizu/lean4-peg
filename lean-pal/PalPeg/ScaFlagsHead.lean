import PalPeg.ScaHeadGen
import PalPeg.ScaHeadDecompose
import PalPeg.BorderJobHead

/-!
# The flags head program on the flags head VM pushes `BorderJobHead.dualFlags`

`DualFlagController` (`ScaGsCoroutine.stepFlagController`) runs
`BorderController(k, flags = true, tailOrigin = "TextOrigin")` with its `Report` / `FinishFlags`
children on the flags head VM `ScaHeadVM.stepFlags`. This file relates that run to the list-level
border job of `BorderJobHead` (`headJob`, `flagStream`, `dualFlags`).

## Results

* `flags_head_dualFlags`: from `flagsInitialVM y lo up (Ctl.ofOutcome (next (flagsInitial 8) none))`,
  `iterFlags n` reaches a returned control whose flags are
  `BorderJobHead.dualFlags y (bdec y dec) 8 lo up`, given the `Decompose` contract
  (`DecomposeContract 8 dec`) and L1 (`nextLen s < L` at every stage length); under `CostHyp`
  (`cut_short`, `cut_charge`, `DecomposeCost 8 cD`) with `n ≤ (3·cD + 3000)·|y| + 4·up + 10`.
* `flags_head_linear` (`up ≤ |y|`: `n ≤ (3·cD + 3004)·|y| + 10`), `flags_head_palindromes`
  (with `StageOK` for `bdec y dec`, via `BorderJobHead.dualFlags_eq`: the palindrome bits).
* §7 discharges both `Decompose` hypotheses with `ScaHeadDecompose.decompose_run`
  (`decomposeContract_gs`, `decomposeCost_gs`, `cD = 1698`): `flags_head_gs`,
  `flags_head_gs_palindromes` (`n ≤ 8098·|y| + 10`) assume only L1 / `StageOK` for the program's
  own decomposition.

`bdec y dec L` is `dec (y.take L)` with `StageMatcher`'s effective period when there is none
(`p₁ = |v| + 1`, `r = 0`): the head then always takes the reset shift, which is `gsShift`'s reset
branch only for such a `(p₁, r)` (`gsShift k 0 0 0 = 0`).

## Layout

1. **The flags VM** (`iterFlags`, lifting a child run into its caller, one lemma per event).
2. **Transfer from the matcher VM.** The shared generators (`Initialize`, `ResetShift`,
   `PeriodShift`, `First`, `Second`, `Decompose`) emit only `move`/`copy`/`equal`/`less`/`symbols`.
   On those events `stepFlags` is `stepMatch` (same positions, control, word) as long as the heads
   read by `symbols` are forward (`rev = false`) and not flag-blind. A run proved on `stepMatch`
   therefore transfers to `stepFlags` (`iterFlags_of_iterStep`), tracking the orientation bits
   (`RevOK`/`EvOK`, closed frame families `shared_closed`, `shift_closed`). `Decompose` enters with
   stale orientations of `P`, `B`: its first five events are run by hand (`dec_prefix`), after which
   `A`, `B`, `P`, `Cut` are forward. `ResetShift k true` is re-proved with `B` allowed at the end of
   the word (`resetShift_run'`; at the frontier `B = OriginalEnd`).
3. **The flag stream, one report at a time** (`reportOut`, `fsRun`, `flagStream_append`).
4. **`FinishFlags` and `Report`** on the flags VM (`finish_run`, `report_run`).
5. **The border controller.** Invariants `Base` (heads kept across stages; `top = Cursor + 1`) and
   `Heads` (a stage at the list-level state `⟨pos, q⟩` of `BorderJob.ovStep`). Segments:
   `scan_hit`, `scan_miss`, `match_guard`, `shift_run` (`reset_run`, `period_run`), `prefix_run`,
   `report_call`, `front_run`; the stage scan equals `ovRun` (`scan_run`, by induction on its fuel,
   the potential `100·(9L − Φ) + 4·top` paying for the steps); `shrink_run` (`End := nextLen s`),
   `stage_start` (`Decompose`, sites 7-17), `stage_exit`, the stage loop `stages_run`
   (= `BorderJobHead.headJob`).
6. **The whole program** and its corollaries.
7. **Instantiation** with `ScaHeadDecompose.decompose_run`.
-/

set_option autoImplicit false

namespace PalPeg.ScaFlagsHead

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen

/-! ## 1. The flags VM -/

/-- `n` steps of the flags VM. -/
def iterFlags : ℕ → HVM → Option HVM
  | 0, v => some v
  | n + 1, v => (stepFlags v).bind (iterFlags n)

theorem iterFlags_add (m n : ℕ) (v : HVM) :
    iterFlags (m + n) v = (iterFlags m v).bind (iterFlags n) := by
  induction m generalizing v with
  | zero => simp [iterFlags]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [iterFlags]
    cases stepFlags v with
    | none => rfl
    | some w => simp [ih]

theorem iterFlags_trans {m n : ℕ} {u v w : HVM} (h1 : iterFlags m u = some v)
    (h2 : iterFlags n v = some w) : iterFlags (m + n) u = some w := by
  rw [iterFlags_add, h1, Option.bind_some, h2]

theorem iterFlags_one {v w : HVM} (h : stepFlags v = some w) : iterFlags 1 v = some w := by
  simp [iterFlags, h]

theorem stepFlags_ctl {v w : HVM} (h : stepFlags v = some w) :
    ∃ cs e, v.ctl = .pending cs e ∧ ∃ d, w.ctl = (Ctl.pending cs e).resume tests d := by
  unfold stepFlags at h
  split at h
  · rename_i cs e hv
    refine ⟨cs, e, hv, ?_⟩
    rw [← hv]
    cases e <;> simp at h
    all_goals first
      | (obtain ⟨π, -, rfl⟩ := h; exact ⟨false, rfl⟩)
      | (subst h; exact ⟨_, rfl⟩)
      | (obtain ⟨-, rfl⟩ := h; exact ⟨_, rfl⟩)
  · simp at h

theorem stepFlags_lift (f : Frame) (v : HVM) (cs : Config) (e : Event) (hv : v.ctl = .pending cs e)
    (hcs : cs ≠ []) :
    stepFlags { v with ctl := .pending (f :: cs) e } = (stepFlags v).map (liftVM f) := by
  have hr : ∀ d, (Ctl.pending (f :: cs) e).resume tests d =
      liftCtl f ((Ctl.pending cs e).resume tests d) := fun d => resume_lift f _ d cs e hcs
  unfold stepFlags
  rw [hv]
  simp only [hr]
  cases e <;> simp [liftVM, HVM.inRange, HVM.len, HVM.view] <;> simp_all
  all_goals rfl

theorem nonEmpty_stepFlags {v w : HVM} (hv : NonEmptyCtl v.ctl) (h : stepFlags v = some w) :
    NonEmptyCtl w.ctl := by
  obtain ⟨cs, e, hc, d, hw⟩ := stepFlags_ctl h
  rw [hw]; exact nonEmpty_ofOutcome cs _

theorem iterFlags_lift (f : Frame) :
    ∀ (n : ℕ) (v w : HVM), NonEmptyCtl v.ctl → iterFlags n v = some w →
      iterFlags n (liftVM f v) = some (liftVM f w)
  | 0, v, w, _, h => by simp [iterFlags] at h; subst h; rfl
  | n + 1, v, w, hv, h => by
    simp only [iterFlags] at h ⊢
    cases hs : stepFlags v with
    | none => simp [hs] at h
    | some v1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨cs, e, hc, -⟩ := stepFlags_ctl hs
      have hne : cs ≠ [] := by rw [hc] at hv; exact hv
      have hl : liftVM f v = { v with ctl := .pending (f :: cs) e } := by
        simp only [liftVM, hc, liftCtl]
      rw [hl, stepFlags_lift f v cs e hc hne, hs, Option.map_some, Option.bind_some]
      exact iterFlags_lift f n v1 w (nonEmpty_stepFlags hv hs) h

/-! ### One step, per event kind -/

section StepLemmas
variable {v : HVM} {c : Config}

theorem fstep_copy {t s' : String} (hv : v.ctl = .pending c (.copy t s')) :
    stepFlags v = some { v with
      pos := Function.update v.pos t (v.pos s')
      rev := Function.update v.rev t (v.rev s')
      ctl := (Ctl.pending c (.copy t s')).resume tests false } := by
  simp only [stepFlags, hv]

theorem fstep_less {a b : String} (hv : v.ctl = .pending c (.less a b)) :
    stepFlags v = some { v with
      ctl := (Ctl.pending c (.less a b)).resume tests (decide (v.pos a < v.pos b)) } := by
  simp only [stepFlags, hv]

theorem fstep_equal {a b : String} (hv : v.ctl = .pending c (.equal a b)) :
    stepFlags v = some { v with
      ctl := (Ctl.pending c (.equal a b)).resume tests (decide (v.pos a = v.pos b)) } := by
  simp only [stepFlags, hv]

theorem fstep_move {ms : List Movement} {π : String → ℤ} (hv : v.ctl = .pending c (.move ms))
    (hm : moveSeq flagBlind v.len ms v.pos = some π) :
    stepFlags v = some { v with
      pos := π
      ctl := (Ctl.pending c (.move ms)).resume tests false } := by
  simp only [stepFlags, hv, hm, Option.map_some]

theorem fstep_symbols {a b : String} (hv : v.ctl = .pending c (.symbols a b))
    (ha : a ∉ flagBlind) (hb : b ∉ flagBlind) (hra : v.inRange a) (hrb : v.inRange b) :
    stepFlags v = some { v with
      ctl := (Ctl.pending c (.symbols a b)).resume tests (decide (v.view a = v.view b)) } := by
  simp only [stepFlags, hv, if_pos (And.intro ha (And.intro hb (And.intro hra hrb)))]

theorem fstep_flag {b : Bool} (hv : v.ctl = .pending c (.flag b)) :
    stepFlags v = some { v with
      flags := v.flags ++ [b]
      ctl := (Ctl.pending c (.flag b)).resume tests false } := by
  simp only [stepFlags, hv]

end StepLemmas

/-! ## 2. Transfer from the matcher VM -/

theorem moveSeq_mono {B1 B2 : List String} (hB : ∀ h ∈ B1, h ∈ B2) (len : ℤ) :
    ∀ (ms : List Movement) (π π' : String → ℤ), moveSeq B1 len ms π = some π' →
      moveSeq B2 len ms π = some π'
  | [], π, π', h => h
  | m :: ms, π, π', h => by
    simp only [moveSeq] at h ⊢
    split_ifs at h with h1
    by_cases h2 : m.head ∉ B2 ∧
        ¬(0 ≤ Function.update π m.head (π m.head + m.delta) m.head ∧
          Function.update π m.head (π m.head + m.delta) m.head ≤ len)
    · exact absurd ⟨fun hm => h2.1 (hB _ hm), h2.2⟩ h1
    · rw [if_neg h2]; exact moveSeq_mono hB len ms _ _ h

theorem blind_sub_flagBlind : ∀ h ∈ blind, h ∈ flagBlind := by decide

/-- `stepFlags`'s move succeeds whenever `stepMatch`'s does, with the same result. -/
theorem moveSeq_flags {len : ℤ} {ms : List Movement} {π π' : String → ℤ}
    (h : moveSeq blind len ms π = some π') : moveSeq flagBlind len ms π = some π' :=
  moveSeq_mono blind_sub_flagBlind len ms π π' h

theorem resume_tests_eq (cs : Config) (e : Event) (d : Bool) (he : e.op ≠ "available") :
    (Ctl.pending cs e).resume tests d = (Ctl.pending cs e).resume matchTests d := by
  have : tests.contains e.op = matchTests.contains e.op := by
    cases e <;> simp_all [Event.op, tests, matchTests]
  simp only [Ctl.resume, respond, this]

/-- The orientation invariant: the heads of `S` are forward, the heads outside `T` keep their
orientation `r0`. -/
def RevOK (S T : List String) (r0 r : String → Bool) : Prop :=
  (∀ h ∈ S, r h = false) ∧ ∀ h, h ∉ T → r h = r0 h

/-- Events on which `stepFlags` is `stepMatch`: `symbols` reads forward, non-flag-blind heads of
`S`; `copy` writes a head of `T`, and a head of `S` only from a head of `S`. -/
def EvOK (S T : List String) : Event → Prop
  | .copy t s => t ∈ T ∧ (t ∈ S → s ∈ S)
  | .symbols a b => a ∈ S ∧ b ∈ S ∧ a ∉ flagBlind ∧ b ∉ flagBlind
  | .move _ => True
  | .equal _ _ => True
  | .less _ _ => True
  | _ => False

/-- The orientation bits after an event of the flags VM. -/
def revStep : Event → (String → Bool) → String → Bool
  | .copy t s, r => Function.update r t (r s)
  | _, r => r

theorem revOK_step {S T : List String} {r0 r : String → Bool} {e : Event} (he : EvOK S T e)
    (hr : RevOK S T r0 r) : RevOK S T r0 (revStep e r) := by
  cases e with
  | copy t s =>
    obtain ⟨htT, hts⟩ := he
    refine ⟨fun h hh => ?_, fun h hh => ?_⟩
    · by_cases hth : h = t
      · subst hth; simp only [revStep, Function.update_self]; exact hr.1 _ (hts hh)
      · simp only [revStep, Function.update_of_ne hth]; exact hr.1 h hh
    · have hth : h ≠ t := fun e => hh (e ▸ htT)
      simp only [revStep, Function.update_of_ne hth]; exact hr.2 h hh
  | _ => exact hr

/-- **One step transfers.** -/
theorem stepFlags_of_stepMatch {S T : List String} {r0 r : String → Bool} {w w1 : HVM}
    {cs : Config} {e : Event} (hc : w.ctl = .pending cs e) (he : EvOK S T e)
    (hr : RevOK S T r0 r) (h : stepMatch w = some w1) :
    stepFlags { w with rev := r } = some { w1 with rev := revStep e r } := by
  have hc' : ({ w with rev := r } : HVM).ctl = .pending cs e := hc
  cases e with
  | copy t s =>
    rw [ScaHeadRun.step_copy hc] at h
    cases h
    rw [fstep_copy hc', resume_tests_eq cs _ false (by simp [Event.op])]
    rfl
  | less a b =>
    rw [ScaHeadRun.step_less hc] at h
    cases h
    rw [fstep_less hc', resume_tests_eq cs _ _ (by simp [Event.op])]
    rfl
  | equal a b =>
    rw [ScaHeadRun.step_equal hc] at h
    cases h
    rw [fstep_equal hc', resume_tests_eq cs _ _ (by simp [Event.op])]
    rfl
  | move ms =>
    unfold stepMatch at h
    rw [hc] at h
    simp only at h
    cases hm : moveSeq blind w.len ms w.pos with
    | none => rw [hm] at h; simp at h
    | some π =>
      rw [hm] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rw [fstep_move hc' (moveSeq_flags hm), resume_tests_eq cs _ _ (by simp [Event.op])]
      rfl
  | symbols a b =>
    obtain ⟨haS, hbS, haB, hbB⟩ := he
    unfold stepMatch at h
    rw [hc] at h
    simp only at h
    split_ifs at h with hin
    cases h
    have hva : ({ w with rev := r } : HVM).view a = w.word[(w.pos a).toNat]? := by
      simp [HVM.view, hr.1 a haS]
    have hvb : ({ w with rev := r } : HVM).view b = w.word[(w.pos b).toNat]? := by
      simp [HVM.view, hr.1 b hbS]
    rw [fstep_symbols hc' haB hbB hin.1 hin.2, hva, hvb,
      resume_tests_eq cs _ _ (by simp [Event.op])]
    rfl
  | _ => exact absurd he (by simp [EvOK])

/-! ### Families of frames closed under the coroutine driver -/

section Family
variable (F : Frame → Prop) (E : Event → Prop)

/-- An action stays in the family `F` and emits only `E`-events. -/
def ActOK : Action → Prop
  | .emit e f => E e ∧ F f
  | .call f c => F f ∧ F c
  | .ret _ => True

def OutOK : Outcome → Prop
  | .yielded e cs => E e ∧ ∀ f ∈ cs, F f
  | .returned _ => True

def CtlOK : Ctl → Prop
  | .pending cs e => E e ∧ ∀ f ∈ cs, F f
  | _ => True

/-- Every frame of `F` steps inside `F`, emitting `E`-events. -/
def Closed : Prop := ∀ f r a, F f → stepFrame f r = some a → ActOK F E a

variable {F E}

theorem advance_ok (hcl : Closed F E) :
    ∀ (fuel : ℕ) (f : Frame) (r : Option Bool) (o : Outcome), F f →
      advance fuel f r = some o → OutOK F E o
  | 0, _, _, _, _, h => by simp [advance] at h
  | fuel + 1, f, r, o, hf, h => by
    simp only [advance] at h
    cases hs : stepFrame f r with
    | none => simp [hs] at h
    | some a =>
      rw [hs] at h
      have ha := hcl f r a hf hs
      cases a with
      | emit e f' =>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        exact ⟨ha.1, by simpa using ha.2⟩
      | ret v =>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h; trivial
      | call f' child =>
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        cases hc : advance fuel child none with
        | none => simp [hc] at h
        | some o' =>
          rw [hc] at h
          have ho' := advance_ok hcl fuel child none o' ha.2 hc
          cases o' with
          | yielded e2 cs2 =>
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
            subst h
            exact ⟨ho'.1, by
              intro g hg
              rcases List.mem_cons.mp hg with rfl | hg
              · exact ha.1
              · exact ho'.2 g hg⟩
          | returned v => exact advance_ok hcl fuel f' v o ha.1 h

theorem send_ok (hcl : Closed F E) (fuel : ℕ) :
    ∀ (cs : Config) (r : Option Bool) (o : Outcome), (∀ f ∈ cs, F f) →
      send fuel cs r = some o → OutOK F E o
  | [], _, _, _, h => by simp [send] at h
  | [f], r, o, hf, h => advance_ok hcl fuel f r o (hf f (by simp)) (by simpa [send] using h)
  | f :: g :: rest, r, o, hf, h => by
    unfold send at h
    cases hs : send fuel (g :: rest) r with
    | none => simp [hs] at h
    | some o' =>
      rw [hs] at h
      have ho' := send_ok hcl fuel (g :: rest) r o' (fun x hx => hf x (List.mem_cons_of_mem _ hx)) hs
      cases o' with
      | yielded e2 cs2 =>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        exact ⟨ho'.1, by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hf _ (by simp)
          · exact ho'.2 x hx⟩
      | returned v => exact advance_ok hcl fuel f v o (hf f (by simp)) (by simpa using h)

theorem ctlOK_ofOutcome (hcl : Closed F E) (cs : Config) (r : Option Bool) (hcs : ∀ f ∈ cs, F f) :
    CtlOK F E (Ctl.ofOutcome (next cs r)) := by
  cases h : next cs r with
  | none => trivial
  | some o =>
    have := send_ok hcl defaultFuel cs r o hcs h
    cases o with
    | yielded e cs' => exact this
    | returned v => trivial

theorem ctlOK_resume (hcl : Closed F E) (ts : List String) (d : Bool) (k : Ctl) (hk : CtlOK F E k) :
    CtlOK F E (k.resume ts d) := by
  cases k with
  | pending cs e => exact ctlOK_ofOutcome hcl cs _ hk.2
  | returned v => trivial
  | failed => trivial

/-- **A matcher run of an `F`-program transfers to the flags VM.** -/
theorem iterFlags_of_iterStep (hcl : Closed F E) {S T : List String}
    (hE : ∀ e, E e → EvOK S T e) :
    ∀ (n : ℕ) (w w' : HVM) (r0 r : String → Bool), CtlOK F E w.ctl → RevOK S T r0 r →
      iterStep n w = some w' →
      ∃ r', RevOK S T r0 r' ∧ iterFlags n { w with rev := r } = some { w' with rev := r' }
  | 0, w, w', r0, r, _, hr, h => by
    simp only [iterStep, Option.some.injEq] at h
    subst h
    exact ⟨r, hr, rfl⟩
  | n + 1, w, w', r0, r, hk, hr, h => by
    simp only [iterStep] at h
    cases hs : stepMatch w with
    | none => simp [hs] at h
    | some w1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨cs, e, hc, d, hw1⟩ := stepMatch_ctl hs
      rw [hc] at hk
      have he : EvOK S T e := hE e hk.1
      have h1 := stepFlags_of_stepMatch hc he hr hs
      have hk1 : CtlOK F E w1.ctl := by
        rw [hw1]; exact ctlOK_resume hcl _ _ _ hk
      obtain ⟨r', hr', hrun⟩ :=
        iterFlags_of_iterStep hcl hE n w1 w' r0 (revStep e r) hk1 (revOK_step he hr) h
      refine ⟨r', hr', ?_⟩
      simp only [iterFlags, h1, Option.bind_some]
      exact hrun

end Family

/-! ### The two families used by the border controller -/

/-- Frames of the shared generators. -/
def SharedFrame : Frame → Prop
  | .initialize _ _ => True
  | .resetShift _ _ _ _ _ => True
  | .periodShift _ _ _ => True
  | .first _ _ _ => True
  | .second _ _ => True
  | .decompose _ _ => True
  | _ => False

/-- The heads the decomposition reads (`A`, `B`), and those they are copied from. -/
def decS : List String := ["Origin", "Cut", "A", "P", "B"]

/-- The heads the decomposition writes (`GsHeads.scala:47-403`). -/
def decT : List String := ["Cut", "A", "P", "B", "KP", "First", "KFirst", "Reach", "Second", "Walk"]

/-- Frames of the searching shifts (`ResetShift k true`, `PeriodShift k true`). -/
def ShiftFrame : Frame → Prop
  | .resetShift _ true _ _ _ => True
  | .periodShift _ true _ => True
  | _ => False

/-- The searching shifts read nothing and copy only `Walk := Cut`. -/
def shT : List String := ["Walk"]

theorem shared_closed : Closed SharedFrame (EvOK decS decT) := by
  intro f r a hf h
  cases f with
  | «initialize» k site =>
    rcases site with _|_|_|_|_|_|site <;>
      simp [stepFrame, stepInitialize] at h <;> (try subst h) <;>
      simp [ActOK, EvOK, SharedFrame, decS, decT, mv, flagBlind]
  | resetShift k search ph ne site =>
    rcases site with _|_|_|_|_|_|_|_|_|site <;> rcases r with _|b <;> rcases ne with _|n <;>
      simp [stepFrame, stepResetShift] at h <;> (repeat' split_ifs at h) <;>
      (try simp only [Option.some.injEq] at h) <;> (try obtain ⟨_, rfl⟩ := h) <;> (try subst h) <;>
      simp [ActOK, EvOK, SharedFrame, decS, decT, mv, flagBlind]
  | periodShift k search site =>
    rcases site with _|_|_|site <;> rcases r with _|b <;>
      simp [stepFrame, stepPeriodShift] at h <;> (repeat' split_ifs at h) <;>
      (try simp only [Option.some.injEq] at h) <;> (try obtain ⟨_, rfl⟩ := h) <;> (try subst h) <;>
      simp [ActOK, EvOK, SharedFrame, decS, decT, mv, flagBlind]
  | first k bounded site =>
    rcases site with _|_|_|_|_|_|_|_|_|site <;> rcases r with _|b <;>
      simp [stepFrame, stepFirst] at h <;> (repeat' split_ifs at h) <;>
      (try simp only [Option.some.injEq] at h) <;> (try obtain ⟨_, rfl⟩ := h) <;> (try subst h) <;>
      simp [ActOK, EvOK, SharedFrame, decS, decT, mv, freshResetShift, flagBlind]
  | second k site =>
    rcases site with _|_|_|_|_|_|_|_|_|_|site <;> rcases r with _|b <;>
      simp [stepFrame, stepSecond] at h <;> (repeat' split_ifs at h) <;>
      (try simp only [Option.some.injEq] at h) <;> (try obtain ⟨_, rfl⟩ := h) <;> (try subst h) <;>
      simp [ActOK, EvOK, SharedFrame, decS, decT, mv, freshResetShift, flagBlind]
  | decompose k site =>
    rcases site with _|_|_|_|_|_|_|_|_|_|_|_|_|site <;> rcases r with _|b <;>
      simp [stepFrame, stepDecompose] at h <;> (repeat' split_ifs at h) <;>
      (try simp only [Option.some.injEq] at h) <;> (try obtain ⟨_, rfl⟩ := h) <;> (try subst h) <;>
      simp [ActOK, EvOK, SharedFrame, decS, decT, mv, flagBlind]
  | _ => exact absurd hf (by simp [SharedFrame])

theorem shift_closed : Closed ShiftFrame (EvOK [] shT) := by
  intro f r a hf h
  cases f with
  | resetShift k search ph ne site =>
    cases search
    · exact absurd hf (by simp [ShiftFrame])
    rcases site with _|_|_|_|_|_|_|_|_|site <;> rcases r with _|b <;> rcases ne with _|n <;>
      simp [stepFrame, stepResetShift] at h <;> (repeat' split_ifs at h) <;>
      (try simp only [Option.some.injEq] at h) <;> (try obtain ⟨_, rfl⟩ := h) <;> (try subst h) <;>
      simp [ActOK, EvOK, ShiftFrame, shT, mv]
  | periodShift k search site =>
    cases search
    · exact absurd hf (by simp [ShiftFrame])
    rcases site with _|_|_|site <;> rcases r with _|b <;>
      simp [stepFrame, stepPeriodShift] at h <;> (repeat' split_ifs at h) <;>
      (try simp only [Option.some.injEq] at h) <;> (try obtain ⟨_, rfl⟩ := h) <;> (try subst h) <;>
      simp [ActOK, EvOK, ShiftFrame, shT, mv]
  | _ => exact absurd hf (by simp [ShiftFrame])

/-! ### `ResetShift k true` with `B` up to the end of the word

`ScaHeadGen.resetShift_run` assumes `B + 1 ≤ len`. At the border controller's frontier `B` sits at
`OriginalEnd = len`; the rewind is non-empty there (`q ≥ 1`), and then the last shift never pushes
`B` past its start. Same proof, with the invariant `B ≤ len ∧ (q = 0 → B + 1 ≤ len)`. -/

theorem rs_loop_run' (k : ℕ) (hk : 1 ≤ k) (π : String → ℤ) (L : ℤ) (ne : Bool) (q : ℕ)
    (hne : ne = decide (q ≠ 0)) (hBL : π "B" ≤ L) (hB0 : q = 0 → π "B" + 1 ≤ L) :
    ∀ (m : ℕ) (v : HVM) (j sh : ℕ), j + m = q → sh = j / k → v.ctl = rsLoop k (j % k) ne →
      v.pos = rsPos π j sh → v.len = L →
      π "A" - q = π "Cut" → 0 ≤ π "Cut" → π "A" - j ≤ L → (q : ℤ) ≤ π "B" →
      0 ≤ π "P" → π "P" + (q / k : ℕ) + 1 ≤ L →
      ∃ n, n ≤ 3 * m + 2 ∧
        iterStep n v = some { v with ctl := .returned none, pos := rsPos π q (rsShifts k q : ℕ) }
  | 0, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hBq, hP0, hPL => by
    have hj : j = q := by omega
    subst hj
    have hshq : sh = j / k := hsh
    by_cases hx : (!ne || j % k != 0) = true
    · refine ⟨2, by omega, ?_⟩
      have hBup : π "B" - j + sh + 1 ≤ L := by
        by_cases hj0 : j = 0
        · subst hj0; simp at hshq; subst hshq; have := hB0 rfl; simp; omega
        · have hmod : j % k ≠ 0 := by
            rw [hne] at hx; simp at hx; rcases hx with h0 | h0
            · exact absurd h0 hj0
            · exact h0
          have hk2 : 1 < k := by
            by_contra hk1
            have : k = 1 := by omega
            subst this; exact hmod (Nat.mod_one j)
          have hlt : j / k < j := Nat.div_lt_self (by omega) hk2
          have : (sh : ℤ) + 1 ≤ j := by rw [hshq]; exact_mod_cast hlt
          omega
      rw [rs_exit_shift k (j % k) ne v π j sh hv hp (by omega) hx
        ⟨by positivity, by rw [hshq]; omega⟩ ⟨by omega, by rw [hL]; exact hBup⟩]
      have : (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx; simp at hx
        rcases hx with h0 | h0
        · exact Or.inl h0
        · exact Or.inr h0
      simp only [rsShifts, if_pos this, hshq, Nat.cast_add, Nat.cast_one]
    · refine ⟨1, by omega, ?_⟩
      have hx' : (!ne || j % k != 0) = false := by simpa using hx
      rw [rs_exit_ret k (j % k) ne v π j sh hv hp (by omega) hx']
      have : ¬ (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx'; simp at hx'; omega
      simp only [rsShifts, if_neg this, Nat.add_zero, ← hshq, hp]
  | m + 1, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hBq, hP0, hPL => by
    obtain ⟨hs1, hs2⟩ := modstep j k hk
    have hjq : sh ≤ q / k := by rw [hsh]; exact Nat.div_le_div_right (by omega)
    have hsj : (sh : ℤ) ≤ j := by rw [hsh]; exact_mod_cast Nat.div_le_self j k
    rcases Nat.lt_or_ge (j % k + 1) k with hph | hph
    · obtain ⟨hm1, hd1⟩ := hs1 hph
      have hstep := rs_iter k (j % k) ne v π j sh hv hp (by omega) hph
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      obtain ⟨n, hn, hrun⟩ := rs_loop_run' k hk π L ne q hne hBL hB0 m
        { v with ctl := rsLoop k (j % k + 1) ne, pos := rsPos π (↑j + 1) sh } (j + 1) sh
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hBq
        hP0 hPL
      refine ⟨2 + n, by omega, ?_⟩
      rw [iterStep_add, hstep, Option.bind_some, hrun]
    · have hph' : j % k + 1 = k := by have := Nat.mod_lt j (show 0 < k by omega); omega
      obtain ⟨hm1, hd1⟩ := hs2 hph'
      have hj1 : sh + 1 ≤ q / k := by
        rw [hsh, ← hd1]; exact Nat.div_le_div_right (by omega)
      have hstep := rs_wrap k (j % k) ne v π j sh hv hp (by omega) hph'
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      obtain ⟨n, hn, hrun⟩ := rs_loop_run' k hk π L ne q hne hBL hB0 m
        { v with ctl := rsLoop k 0 ne, pos := rsPos π (↑j + 1) (↑sh + 1) } (j + 1) (sh + 1)
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hBq
        hP0 hPL
      refine ⟨3 + n, by omega, ?_⟩
      rw [iterStep_add, hstep, Option.bind_some, hrun]

/-- **`ResetShift k true`, from its fresh frame**, with `B` allowed at the end of the word when
the rewind is non-empty. -/
theorem resetShift_run' (k : ℕ) (hk : 1 ≤ k) (v : HVM) (q : ℕ)
    (hv : v.ctl = Ctl.ofOutcome (next [.resetShift k true 0 none 0] none))
    (hq : v.pos "A" = v.pos "Cut" + q) (hC : 0 ≤ v.pos "Cut") (hAL : v.pos "A" ≤ v.len)
    (hBq : (q : ℤ) ≤ v.pos "B") (hBL : v.pos "B" ≤ v.len) (hB0 : q = 0 → v.pos "B" + 1 ≤ v.len)
    (hP0 : 0 ≤ v.pos "P") (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len) :
    ∃ n, n ≤ 3 * q + 3 ∧
      iterStep n v = some { v with
        ctl := .returned none
        pos := rsPos v.pos q (rsShifts k q : ℕ) } := by
  rw [rs_start] at hv
  have h1 := rs_first k v hv
  have hne : decide (v.pos "A" ≠ v.pos "Cut") = decide (q ≠ 0) := by
    simp only [decide_eq_decide]; omega
  rw [hne] at h1
  obtain ⟨n, hn, hrun⟩ := rs_loop_run' k hk v.pos v.len (decide (q ≠ 0)) q rfl hBL hB0 q
    { v with ctl := rsLoop k 0 (decide (q ≠ 0)) } 0 0 (by omega) (by simp) (by simp)
    (by simp [rsPos_zero]) rfl (by omega) hC (by simp; omega) hBq hP0 hPL
  refine ⟨1 + n, by omega, ?_⟩
  rw [iterStep_add, h1, Option.bind_some, hrun]

/-! ### The shifts on the flags VM -/

theorem hvm_rev_eta (v : HVM) : ({ v with rev := v.rev } : HVM) = v := rfl

/-- A matcher run of a searching shift, transferred: only `Walk`'s orientation may change. -/
theorem shift_transfer {n : ℕ} {v w : HVM} {cs : Config} (hcs : ∀ f ∈ cs, ShiftFrame f)
    (hv : v.ctl = Ctl.ofOutcome (next cs none)) (h : iterStep n v = some w) :
    ∃ r', (∀ h, h ≠ "Walk" → r' h = v.rev h) ∧ iterFlags n v = some { w with rev := r' } := by
  have hk : CtlOK ShiftFrame (EvOK [] shT) v.ctl := by
    rw [hv]; exact ctlOK_ofOutcome shift_closed cs none hcs
  obtain ⟨r', hr', hrun⟩ := iterFlags_of_iterStep shift_closed (S := []) (T := shT)
    (fun e he => he) n v w v.rev v.rev hk ⟨by simp, fun _ _ => rfl⟩ h
  exact ⟨r', fun h hh => hr'.2 h (by simp [shT, hh]), hrun⟩

/-- **`ResetShift k true` on the flags VM.** -/
theorem resetShift_flags (k : ℕ) (hk : 1 ≤ k) (v : HVM) (q : ℕ)
    (hv : v.ctl = Ctl.ofOutcome (next [.resetShift k true 0 none 0] none))
    (hq : v.pos "A" = v.pos "Cut" + q) (hC : 0 ≤ v.pos "Cut") (hAL : v.pos "A" ≤ v.len)
    (hBq : (q : ℤ) ≤ v.pos "B") (hBL : v.pos "B" ≤ v.len) (hB0 : q = 0 → v.pos "B" + 1 ≤ v.len)
    (hP0 : 0 ≤ v.pos "P") (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len) :
    ∃ n r', n ≤ 3 * q + 3 ∧ (∀ h, h ≠ "Walk" → r' h = v.rev h) ∧
      iterFlags n v = some { v with
        ctl := .returned none
        pos := rsPos v.pos q (rsShifts k q : ℕ)
        rev := r' } := by
  obtain ⟨n, hn, hrun⟩ := resetShift_run' k hk v q hv hq hC hAL hBq hBL hB0 hP0 hPL
  obtain ⟨r', hr', hfl⟩ := shift_transfer (cs := [.resetShift k true 0 none 0])
    (by simp [ShiftFrame]) hv hrun
  exact ⟨n, r', hn, hr', hfl⟩

/-- **`PeriodShift k true` on the flags VM.** -/
theorem periodShift_flags (k : ℕ) (v : HVM) (t : ℕ)
    (hv : v.ctl = Ctl.ofOutcome (next [.periodShift k true 0] none))
    (ht : v.pos "Cut" + t = v.pos "First") (h0 : 0 ≤ v.pos "Cut") (hF : v.pos "First" ≤ v.len)
    (hA : t ≤ v.pos "A") (hA' : v.pos "A" ≤ v.len) (hP : 0 ≤ v.pos "P")
    (hP' : v.pos "P" + t ≤ v.len) :
    ∃ r', (∀ h, h ≠ "Walk" → r' h = v.rev h) ∧
      iterFlags (2 * t + 2) v = some { v with
        ctl := .returned none
        pos := psPos v.pos t
        rev := r' } := by
  have hrun := periodShift_run k v t hv ht h0 hF hA hA' hP hP'
  exact shift_transfer (cs := [.periodShift k true 0]) (by simp [ShiftFrame]) hv hrun

/-! ### `Decompose` on the flags VM -/

/-- **The contract of `Decompose k` on the matcher VM**, taken as a hypothesis (to be discharged
by the proof of the shared generators, `ScaHeadDecompose`). Run from its fresh frame with
`Origin = 0` and `End = L` (`1 ≤ L ≤ len`), it returns `period_exists = (p₁ ≠ 0)`, leaves
`Cut = s` and, when a period exists, `First = s + p₁`, `KFirst = s + k·p₁`, `Reach = s + r`,
where `(s, p₁, r) = dec (word.take L)`; it writes only the heads `decT`. -/
def DecomposeContract (k : ℕ) (dec : List (Fin 2) → ℕ × ℕ × ℕ) : Prop :=
  ∀ (v : HVM) (L : ℕ), v.ctl = Ctl.ofOutcome (next [.decompose k 0] none) →
    v.pos "Origin" = 0 → v.pos "End" = L → 1 ≤ L → (L : ℤ) ≤ v.len →
    ∃ n π, iterStep n v = some { v with
        ctl := .returned (some (decide ((dec (v.word.take L)).2.1 ≠ 0)))
        pos := π } ∧
      π "Cut" = ((dec (v.word.take L)).1 : ℤ) ∧
      ((dec (v.word.take L)).2.1 ≠ 0 →
        π "First" = ((dec (v.word.take L)).1 + (dec (v.word.take L)).2.1 : ℕ) ∧
        π "KFirst" = ((dec (v.word.take L)).1 + k * (dec (v.word.take L)).2.1 : ℕ) ∧
        π "Reach" = ((dec (v.word.take L)).1 + (dec (v.word.take L)).2.2 : ℕ)) ∧
      ∀ h, h ∉ decT → π h = v.pos h

/-- **A linear cost for `Decompose k` on the matcher VM**, taken as a hypothesis of the step
bound: when it returns, it has taken at most `cD·L + cD` steps. -/
def DecomposeCost (k cD : ℕ) : Prop :=
  ∀ (v w : HVM) (L n : ℕ), v.ctl = Ctl.ofOutcome (next [.decompose k 0] none) →
    v.pos "Origin" = 0 → v.pos "End" = L → 1 ≤ L → (L : ℤ) ≤ v.len →
    iterStep n v = some w → (∃ val, w.ctl = .returned val) → n ≤ cD * L + cD

section DecPrefix
variable (k : ℕ)

/-- The first five events of `Decompose`: `Cut := Origin`, then `Initialize`'s
`A := Cut`, `P := Cut`, `P + 1`, `B := P`. -/
def decCtl : ℕ → Ctl
  | 0 => .pending [.decompose k 1] (.copy "Cut" "Origin")
  | 1 => .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut")
  | 2 => .pending [.decompose k 2, .first k false 1, .initialize k 2] (.copy "P" "Cut")
  | 3 => .pending [.decompose k 2, .first k false 1, .initialize k 3] (mv [("P", 1)])
  | 4 => .pending [.decompose k 2, .first k false 1, .initialize k 4] (.copy "B" "P")
  | _ => .pending [.decompose k 2, .first k false 1, .initialize k 5] (.copy "KP" "Cut")

theorem decCtl_start : Ctl.ofOutcome (next [.decompose k 0] none) = decCtl k 0 := rfl

theorem decCtl_pending (i : ℕ) : ∃ cs e, decCtl k i = .pending cs e := by
  unfold decCtl; split <;> exact ⟨_, _, rfl⟩

end DecPrefix

/-- The matcher's first five `Decompose` steps, and the same on the flags VM (which then has the
heads `decS` forward). -/
theorem dec_prefix (k : ℕ) (v : HVM) (hv : v.ctl = decCtl k 0) (hO : v.pos "Origin" = 0)
    (hlen : 1 ≤ v.len) (hrO : v.rev "Origin" = false) :
    ∃ π5 : String → ℤ,
      (∀ j, j < 5 → ∃ vj : HVM, iterStep j v = some vj ∧ vj.ctl = decCtl k j) ∧
      iterStep 5 v = some { v with ctl := decCtl k 5, pos := π5 } ∧
      ∃ r5, RevOK decS decT v.rev r5 ∧
        iterFlags 5 v = some { v with ctl := decCtl k 5, pos := π5, rev := r5 } := by
  let v1 : HVM := { v with pos := Function.update v.pos "Cut" (v.pos "Origin"), ctl := decCtl k 1 }
  let v2 : HVM := { v1 with pos := Function.update v1.pos "A" (v1.pos "Cut"), ctl := decCtl k 2 }
  let v3 : HVM := { v2 with pos := Function.update v2.pos "P" (v2.pos "Cut"), ctl := decCtl k 3 }
  let v4 : HVM := { v3 with pos := Function.update v3.pos "P" (v3.pos "P" + 1), ctl := decCtl k 4 }
  let v5 : HVM := { v4 with pos := Function.update v4.pos "B" (v4.pos "P"), ctl := decCtl k 5 }
  have hv' : v.ctl = .pending [.decompose k 1] (.copy "Cut" "Origin") := hv
  have s1 : stepMatch v = some v1 := by rw [ScaHeadRun.step_copy hv']; rfl
  have s2 : stepMatch v1 = some v2 := by
    rw [ScaHeadRun.step_copy (v := v1) (c := [.decompose k 2, .first k false 1, .initialize k 1]) rfl]
    rfl
  have s3 : stepMatch v2 = some v3 := by
    rw [ScaHeadRun.step_copy (v := v2) (c := [.decompose k 2, .first k false 1, .initialize k 2]) rfl]
    rfl
  have hP3 : v3.pos "P" = 0 := by simp [v3, v2, v1, Function.update, hO]
  have hl3 : v3.len = v.len := rfl
  have s4 : stepMatch v3 = some v4 := by
    rw [ScaHeadRun.step_move (v := v3) (c := [.decompose k 2, .first k false 1, .initialize k 3])
      (ms := [⟨"P", 1⟩]) (π := Function.update v3.pos "P" (v3.pos "P" + 1)) rfl
      (by simp only [moveSeq, blind, hl3]; simp [Function.update, hP3]; omega)]
    rfl
  have s5 : stepMatch v4 = some v5 := by
    rw [ScaHeadRun.step_copy (v := v4) (c := [.decompose k 2, .first k false 1, .initialize k 4]) rfl]
    rfl
  refine ⟨v5.pos, ?_, ?_, ?_⟩
  · intro j hj
    interval_cases j
    · exact ⟨v, rfl, hv⟩
    · exact ⟨v1, by simp [iterStep, s1], rfl⟩
    · exact ⟨v2, by simp [iterStep, s1, s2], rfl⟩
    · exact ⟨v3, by simp [iterStep, s1, s2, s3], rfl⟩
    · exact ⟨v4, by simp [iterStep, s1, s2, s3, s4], rfl⟩
  · simp [iterStep, s1, s2, s3, s4, s5]; rfl
  · -- the same five steps on the flags VM, one by one
    have t : ∀ (w w1 : HVM) (cs : Config) (e : Event) (r : String → Bool),
        w.ctl = .pending cs e → EvOK [] decT e → stepMatch w = some w1 →
        stepFlags { w with rev := r } = some { w1 with rev := revStep e r } :=
      fun w w1 cs e r hc he h => stepFlags_of_stepMatch (r0 := r) hc he ⟨by simp, fun _ _ => rfl⟩ h
    let r1 := revStep (.copy "Cut" "Origin") v.rev
    let r2 := revStep (.copy "A" "Cut") r1
    let r3 := revStep (.copy "P" "Cut") r2
    let r4 := revStep (mv [("P", 1)]) r3
    let r5 := revStep (.copy "B" "P") r4
    have f1 := t v v1 _ _ v.rev hv' (by simp [EvOK, decT]) s1
    have f2 := t v1 v2 [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut") r1 rfl
      (by simp [EvOK, decT]) s2
    have f3 := t v2 v3 [.decompose k 2, .first k false 1, .initialize k 2] (.copy "P" "Cut") r2 rfl
      (by simp [EvOK, decT]) s3
    have f4 := t v3 v4 [.decompose k 2, .first k false 1, .initialize k 3] (mv [("P", 1)]) r3 rfl
      (by simp [EvOK, decT, mv]) s4
    have f5 := t v4 v5 [.decompose k 2, .first k false 1, .initialize k 4] (.copy "B" "P") r4 rfl
      (by simp [EvOK, decT]) s5
    refine ⟨r5, ?_, ?_⟩
    rotate_left
    · show iterFlags 5 { v with rev := v.rev } = _
      simp only [iterFlags]
      rw [f1, Option.bind_some, f2, Option.bind_some, f3, Option.bind_some, f4, Option.bind_some,
        f5, Option.bind_some]
    · refine ⟨fun h hh => ?_, fun h hh => ?_⟩
      · simp only [decS, List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl | rfl | rfl | rfl <;>
          simp [r5, r4, r3, r2, r1, revStep, Function.update, hrO, mv]
      · have h1 : h ≠ "Cut" := fun e => hh (by simp [e, decT])
        have h2 : h ≠ "A" := fun e => hh (by simp [e, decT])
        have h3 : h ≠ "P" := fun e => hh (by simp [e, decT])
        have h4 : h ≠ "B" := fun e => hh (by simp [e, decT])
        simp [r5, r4, r3, r2, r1, revStep, Function.update, h1, h2, h3, h4, mv]

/-- The period data a decomposition leaves in the heads. -/
def DecHeads (k : ℕ) (d : ℕ × ℕ × ℕ) (π : String → ℤ) : Prop :=
  π "Cut" = (d.1 : ℤ) ∧
    (d.2.1 ≠ 0 → π "First" = (d.1 + d.2.1 : ℕ) ∧ π "KFirst" = (d.1 + k * d.2.1 : ℕ) ∧
      π "Reach" = (d.1 + d.2.2 : ℕ))

/-- **`Decompose k` on the flags VM**, from its contract on the matcher VM. The flags VM may
enter with any orientation of the decomposition's heads except `Origin` (forward). -/
theorem decompose_flags {k : ℕ} {dec : List (Fin 2) → ℕ × ℕ × ℕ} (hD : DecomposeContract k dec)
    (v : HVM) (L : ℕ) (hv : v.ctl = Ctl.ofOutcome (next [.decompose k 0] none))
    (hO : v.pos "Origin" = 0) (hE : v.pos "End" = L) (hL1 : 1 ≤ L) (hLl : (L : ℤ) ≤ v.len)
    (hrO : v.rev "Origin" = false) :
    ∃ n π r', (∀ cD, DecomposeCost k cD → n ≤ cD * L + cD) ∧ iterFlags n v = some { v with
        ctl := .returned (some (decide ((dec (v.word.take L)).2.1 ≠ 0)))
        pos := π
        rev := r' } ∧
      DecHeads k (dec (v.word.take L)) π ∧ (∀ h, h ∉ decT → π h = v.pos h) ∧
      r' "Cut" = false ∧ (∀ h, h ∉ decT → r' h = v.rev h) := by
  obtain ⟨n, π, hrun, hC, hper, hkeep⟩ := hD v L hv hO hE hL1 hLl
  obtain ⟨π5, hpre, h5, r5, hr5, hf5⟩ :=
    dec_prefix k v (hv.trans (decCtl_start k)) hO (by omega) hrO
  have hn : 5 ≤ n := by
    by_contra hlt
    obtain ⟨vj, hj, hcj⟩ := hpre n (by omega)
    rw [hj] at hrun
    have hc := congrArg HVM.ctl (Option.some.inj hrun)
    rw [hcj] at hc
    obtain ⟨cs, e, he⟩ := decCtl_pending k n
    rw [he] at hc
    exact Ctl.noConfusion hc
  have hrun' : iterStep (n - 5) { v with ctl := decCtl k 5, pos := π5 } = some { v with
      ctl := .returned (some (decide ((dec (v.word.take L)).2.1 ≠ 0)))
      pos := π } := by
    rw [show n = 5 + (n - 5) by omega, iterStep_add, h5, Option.bind_some] at hrun
    exact hrun
  have hk5 : CtlOK SharedFrame (EvOK decS decT) (decCtl k 5) := by
    simp [decCtl, CtlOK, EvOK, decT, decS, SharedFrame]
  obtain ⟨r', hr', hfl⟩ := iterFlags_of_iterStep shared_closed (S := decS) (T := decT)
    (fun e he => he) (n - 5) _ _ v.rev r5 hk5 hr5 hrun'
  refine ⟨n, π, r', fun cD hc => hc v _ L n hv hO hE hL1 hLl hrun ⟨_, rfl⟩, ?_, ⟨hC, hper⟩, hkeep,
    hr'.1 "Cut" (by simp [decS]), hr'.2⟩
  rw [show n = 5 + (n - 5) by omega, iterFlags_add, hf5, Option.bind_some]
  exact hfl

/-! ## 3. The flag stream, one report at a time -/

section Stream
open BorderJobHead

/-- What `_report` (`stepReport`, flags) does with the report `ℓ` when `Cursor = top - 1`: the
bits it pushes, the new `top` (`Cursor + 1`), and its return value (`true` = stop and finish). -/
def reportOut (lo top ℓ : ℕ) : List Bool × ℕ × Bool :=
  if ℓ < lo then ([], top, true)
  else if ℓ < top then (List.replicate (top - 1 - ℓ) false ++ [true], ℓ, decide (ℓ ≤ lo))
  else ([], top, decide (top ≤ lo))

/-- `flagStream` over a prefix of the reports: the bits, and the `top` to continue with (`none` if
the stream has finished). -/
def fsRun (lo : ℕ) : ℕ → List ℕ → List Bool × Option ℕ
  | top, [] => ([], some top)
  | top, ℓ :: R =>
    if (reportOut lo top ℓ).2.2 then
      ((reportOut lo top ℓ).1 ++ finishBits lo (reportOut lo top ℓ).2.1, none)
    else
      ((reportOut lo top ℓ).1 ++ (fsRun lo (reportOut lo top ℓ).2.1 R).1,
        (fsRun lo (reportOut lo top ℓ).2.1 R).2)

/-- The continuation of the stream after `fsRun`. -/
def fsCont (lo : ℕ) (Rest : List ℕ) : Option ℕ → List Bool
  | none => []
  | some t => flagStream lo t Rest

theorem flagStream_cons_eq (lo top ℓ : ℕ) (R : List ℕ) :
    flagStream lo top (ℓ :: R) = (reportOut lo top ℓ).1 ++
      (if (reportOut lo top ℓ).2.2 then finishBits lo (reportOut lo top ℓ).2.1
       else flagStream lo (reportOut lo top ℓ).2.1 R) := by
  unfold reportOut
  rw [flagStream]
  by_cases h1 : ℓ < lo
  · simp [h1]
  · by_cases h2 : ℓ < top
    · by_cases h3 : ℓ ≤ lo <;> simp [h1, h2, h3]
    · by_cases h3 : top ≤ lo <;> simp [h1, h2, h3]

theorem flagStream_append (lo : ℕ) (Rest : List ℕ) :
    ∀ (R : List ℕ) (top : ℕ),
      flagStream lo top (R ++ Rest) = (fsRun lo top R).1 ++ fsCont lo Rest (fsRun lo top R).2
  | [], top => by simp [fsRun, fsCont]
  | ℓ :: R, top => by
    rw [List.cons_append, flagStream_cons_eq]
    unfold fsRun
    split_ifs with h
    · simp [fsCont]
    · rw [flagStream_append lo Rest R, List.append_assoc]

theorem fsRun_cons (lo top ℓ : ℕ) (R : List ℕ) :
    fsRun lo top (ℓ :: R) =
      if (reportOut lo top ℓ).2.2 then
        ((reportOut lo top ℓ).1 ++ finishBits lo (reportOut lo top ℓ).2.1, none)
      else
        ((reportOut lo top ℓ).1 ++ (fsRun lo (reportOut lo top ℓ).2.1 R).1,
          (fsRun lo (reportOut lo top ℓ).2.1 R).2) := rfl

theorem fsRun_append (lo : ℕ) :
    ∀ (R1 R2 : List ℕ) (top : ℕ), fsRun lo top (R1 ++ R2) =
      match (fsRun lo top R1).2 with
      | none => fsRun lo top R1
      | some t => ((fsRun lo top R1).1 ++ (fsRun lo t R2).1, (fsRun lo t R2).2)
  | [], R2, top => by simp [fsRun]
  | ℓ :: R1, R2, top => by
    rw [List.cons_append, fsRun_cons, fsRun_cons]
    split_ifs with h
    · rfl
    · rw [fsRun_append lo R1 R2]
      cases hc : (fsRun lo (reportOut lo top ℓ).2.1 R1).2 with
      | none => simp [hc]
      | some t => simp

end Stream

/-! ## 4. `FinishFlags` and `Report` on the flags VM -/

theorem cursor_move (len : ℤ) (π : String → ℤ) :
    moveSeq flagBlind len [⟨"Cursor", -1⟩] π = some (Function.update π "Cursor" (π "Cursor" - 1)) := by
  simp [moveSeq, flagBlind]
  rfl

theorem update_update_self (π : String → ℤ) (h : String) (a b : ℤ) :
    Function.update (Function.update π h a) h b = Function.update π h b := by
  funext x; by_cases hx : x = h <;> simp [Function.update, hx]

section Finish

/-- `FinishFlags` waiting at its loop head (`Cursor < Lower`?). -/
def ffHead : Ctl := .pending [.finishFlags 1] (.less "Cursor" "Lower")

theorem ff_start : Ctl.ofOutcome (next [.finishFlags 0] none) = ffHead := rfl

theorem ff_done : (Ctl.pending [.finishFlags 1] (.less "Cursor" "Lower")).resume tests true =
    .returned none := rfl

theorem ff_go : (Ctl.pending [.finishFlags 1] (.less "Cursor" "Lower")).resume tests false =
    .pending [.finishFlags 2] (.equal "Cursor" "Origin") := rfl

theorem ff_test (b : Bool) : (Ctl.pending [.finishFlags 2] (.equal "Cursor" "Origin")).resume tests b =
    .pending [.finishFlags (if b then 3 else 4)] (.flag b) := by cases b <;> rfl

theorem ff_flag (b : Bool) : (Ctl.pending [.finishFlags (if b then 3 else 4)] (.flag b)).resume tests false =
    .pending [.finishFlags 5] (mv [("Cursor", -1)]) := by cases b <;> rfl

theorem ff_back : (Ctl.pending [.finishFlags 5] (mv [("Cursor", -1)])).resume tests false = ffHead := rfl

/-- **`FinishFlags`**: from `Cursor = t - 1`, it pushes `finishBits lo t` (`Cursor = Origin` for
each length `t-1, …, lo`) and returns. -/
theorem finish_run (lo : ℕ) : ∀ (t : ℕ) (v : HVM), v.ctl = ffHead → v.pos "Cursor" = (t : ℤ) - 1 →
    v.pos "Lower" = lo → v.pos "Origin" = 0 →
    iterFlags (4 * (t - lo) + 1) v = some { v with
      ctl := .returned none
      pos := Function.update v.pos "Cursor" (min (t : ℤ) lo - 1)
      flags := v.flags ++ BorderJobHead.finishBits lo t }
  | t, v, hv, hC, hL, hO => by
    by_cases ht : t ≤ lo
    · have e1 := fstep_less hv
      rw [show decide (v.pos "Cursor" < v.pos "Lower") = true by simp; omega, ff_done] at e1
      rw [show 4 * (t - lo) + 1 = 1 by omega, iterFlags_one e1,
        BorderJobHead.finishBits_of_le ht, List.append_nil,
        show min (t : ℤ) lo - 1 = v.pos "Cursor" by omega, Function.update_eq_self]
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have e1 := fstep_less hv
      rw [show decide (v.pos "Cursor" < v.pos "Lower") = false by simp; omega, ff_go] at e1
      have e2 := fstep_equal (v := { v with
        ctl := .pending [.finishFlags 2] (.equal "Cursor" "Origin") }) rfl
      rw [ff_test] at e2
      simp only at e2
      have hb : decide (v.pos "Cursor" = v.pos "Origin") = decide (t' = 0) := by
        simp only [decide_eq_decide]; rw [hC, hO]; push_cast; omega
      rw [hb] at e2
      have e3 := fstep_flag (v := { v with
        ctl := .pending [.finishFlags (if decide (t' = 0) then 3 else 4)] (.flag (decide (t' = 0))) })
        rfl
      rw [ff_flag] at e3
      have e4 : stepFlags { v with
          ctl := .pending [.finishFlags 5] (mv [("Cursor", -1)])
          flags := v.flags ++ [decide (t' = 0)] } = some { v with
          ctl := ffHead
          pos := Function.update v.pos "Cursor" (v.pos "Cursor" - 1)
          flags := v.flags ++ [decide (t' = 0)] } := by
        rw [fstep_move (ms := [⟨"Cursor", -1⟩]) rfl (cursor_move _ _)]; rfl
      have ih := finish_run lo t' { v with
        ctl := ffHead
        pos := Function.update v.pos "Cursor" (v.pos "Cursor" - 1)
        flags := v.flags ++ [decide (t' = 0)] } rfl
        (by simp [hC]) (by simp [Function.update, hL]) (by simp [Function.update, hO])
      have h4 : iterFlags 4 v = some { v with
          ctl := ffHead
          pos := Function.update v.pos "Cursor" (v.pos "Cursor" - 1)
          flags := v.flags ++ [decide (t' = 0)] } := by
        simp only [iterFlags, e1, Option.bind_some, e2, e3, e4]
      rw [show 4 * (t' + 1 - lo) + 1 = 4 + (4 * (t' - lo) + 1) by omega, iterFlags_add, h4,
        Option.bind_some, ih]
      simp only [update_update_self, List.append_assoc, List.singleton_append]
      rw [show BorderJobHead.finishBits lo (t' + 1) = decide (t' = 0) :: BorderJobHead.finishBits lo t' by
        simp [BorderJobHead.finishBits, BorderJobHead.lensDown_succ_of_le (show lo ≤ t' by omega)],
        show min ((t' : ℤ)) lo = min ((t' + 1 : ℕ) : ℤ) lo by omega]

end Finish

section Report

/-- `Report(flags = true)` at its first test (`KP < Lower`?). -/
def repHead : Ctl := .pending [.report true 2] (.less "KP" "Lower")

theorem rep_start : Ctl.ofOutcome (next [.report true 0] none) = repHead := rfl

/-- The fill loop of `_report` (sites 4-8): from `Cursor = ℓ + d` it pushes `d` × `false`, then
`true`, and stops at the final test with `Cursor = ℓ - 1`. -/
theorem fill_run (ℓ : ℕ) : ∀ (d : ℕ) (v : HVM),
    v.ctl = .pending [.report true 4] (.less "KP" "Cursor") →
    v.pos "KP" = ℓ → v.pos "Cursor" = ((ℓ + d : ℕ) : ℤ) →
    iterFlags (3 * d + 3) v = some { v with
      ctl := .pending [.report true 9] (.less "Cursor" "Lower")
      pos := Function.update v.pos "Cursor" ((ℓ : ℤ) - 1)
      flags := v.flags ++ (List.replicate d false ++ [true]) }
  | 0, v, hv, hK, hC => by
    have e1 : stepFlags v = some { v with ctl := .pending [.report true 7] (.flag true) } := by
      rw [fstep_less hv, show decide (v.pos "KP" < v.pos "Cursor") = false by simp; omega]; rfl
    have e2 : stepFlags { v with ctl := .pending [.report true 7] (.flag true) } =
        some { v with
          ctl := .pending [.report true 8] (mv [("Cursor", -1)])
          flags := v.flags ++ [true] } := by
      rw [fstep_flag rfl]; rfl
    have e3 : stepFlags { v with
          ctl := .pending [.report true 8] (mv [("Cursor", -1)])
          flags := v.flags ++ [true] } = some { v with
          ctl := .pending [.report true 9] (.less "Cursor" "Lower")
          pos := Function.update v.pos "Cursor" ((ℓ : ℤ) - 1)
          flags := v.flags ++ [true] } := by
      rw [fstep_move (ms := [⟨"Cursor", -1⟩]) rfl (cursor_move _ _)]
      simp only [hC, Nat.add_zero]; rfl
    simp only [iterFlags, e1, Option.bind_some, e2, e3, List.replicate_zero, List.nil_append]
  | d + 1, v, hv, hK, hC => by
    have e1 : stepFlags v = some { v with ctl := .pending [.report true 5] (.flag false) } := by
      rw [fstep_less hv, show decide (v.pos "KP" < v.pos "Cursor") = true by simp; omega]; rfl
    have e2 : stepFlags { v with ctl := .pending [.report true 5] (.flag false) } =
        some { v with
          ctl := .pending [.report true 6] (mv [("Cursor", -1)])
          flags := v.flags ++ [false] } := by
      rw [fstep_flag rfl]; rfl
    have e3 : stepFlags { v with
          ctl := .pending [.report true 6] (mv [("Cursor", -1)])
          flags := v.flags ++ [false] } = some { v with
          ctl := .pending [.report true 4] (.less "KP" "Cursor")
          pos := Function.update v.pos "Cursor" (v.pos "Cursor" - 1)
          flags := v.flags ++ [false] } := by
      rw [fstep_move (ms := [⟨"Cursor", -1⟩]) rfl (cursor_move _ _)]; rfl
    have ih := fill_run ℓ d { v with
          ctl := .pending [.report true 4] (.less "KP" "Cursor")
          pos := Function.update v.pos "Cursor" (v.pos "Cursor" - 1)
          flags := v.flags ++ [false] } rfl (by simp [Function.update, hK])
      (by simp [hC]; push_cast; ring)
    have h3 : iterFlags 3 v = some { v with
          ctl := .pending [.report true 4] (.less "KP" "Cursor")
          pos := Function.update v.pos "Cursor" (v.pos "Cursor" - 1)
          flags := v.flags ++ [false] } := by
      simp only [iterFlags, e1, Option.bind_some, e2, e3]
    rw [show 3 * (d + 1) + 3 = 3 + (3 * d + 3) by ring, iterFlags_add, h3, Option.bind_some, ih]
    simp only [update_update_self, List.append_assoc, List.replicate_succ, List.cons_append,
      List.singleton_append, List.nil_append]

/-- **`Report(flags = true)`** with `KP = ℓ`, `Cursor = top - 1`, `Lower = lo`: it pushes
`(reportOut lo top ℓ).1`, leaves `Cursor = (reportOut lo top ℓ).2.1 - 1`, and returns
`(reportOut lo top ℓ).2.2`. -/
theorem report_run (lo top ℓ : ℕ) (v : HVM) (hv : v.ctl = repHead) (hK : v.pos "KP" = ℓ)
    (hC : v.pos "Cursor" = (top : ℤ) - 1) (hL : v.pos "Lower" = lo) :
    ∃ n, n ≤ 3 * (top - (reportOut lo top ℓ).2.1) + 6 ∧ iterFlags n v = some { v with
      ctl := .returned (some (reportOut lo top ℓ).2.2)
      pos := Function.update v.pos "Cursor" (((reportOut lo top ℓ).2.1 : ℤ) - 1)
      flags := v.flags ++ (reportOut lo top ℓ).1 } := by
  have hv' : v.ctl = .pending [.report true 2] (.less "KP" "Lower") := hv
  by_cases h1 : ℓ < lo
  · have e1 : stepFlags v = some { v with ctl := .returned (some true) } := by
      rw [fstep_less hv', show decide (v.pos "KP" < v.pos "Lower") = true by simp; omega]; rfl
    refine ⟨1, by simp [reportOut, h1], ?_⟩
    rw [iterFlags_one e1]
    simp only [reportOut, if_pos h1, List.append_nil]
    rw [← hC, Function.update_eq_self]
  · have e1 : stepFlags v = some { v with ctl := .pending [.report true 3] (.less "Cursor" "KP") } := by
      rw [fstep_less hv', show decide (v.pos "KP" < v.pos "Lower") = false by simp; omega]; rfl
    by_cases h2 : ℓ < top
    · have e2 : stepFlags { v with ctl := .pending [.report true 3] (.less "Cursor" "KP") } =
          some { v with ctl := .pending [.report true 4] (.less "KP" "Cursor") } := by
        rw [fstep_less rfl, show decide (v.pos "Cursor" < v.pos "KP") = false by simp; omega]; rfl
      have hf := fill_run ℓ (top - 1 - ℓ) { v with ctl := .pending [.report true 4] (.less "KP" "Cursor") }
        rfl hK (by simp only [hC]; push_cast [show ℓ + (top - 1 - ℓ) = top - 1 by omega]; omega)
      have e3 : stepFlags { v with
            ctl := .pending [.report true 9] (.less "Cursor" "Lower")
            pos := Function.update v.pos "Cursor" ((ℓ : ℤ) - 1)
            flags := v.flags ++ (List.replicate (top - 1 - ℓ) false ++ [true]) } =
          some { v with
            ctl := .returned (some (decide (ℓ ≤ lo)))
            pos := Function.update v.pos "Cursor" ((ℓ : ℤ) - 1)
            flags := v.flags ++ (List.replicate (top - 1 - ℓ) false ++ [true]) } := by
        rw [fstep_less rfl]
        have : decide (Function.update v.pos "Cursor" ((ℓ : ℤ) - 1) "Cursor" <
            Function.update v.pos "Cursor" ((ℓ : ℤ) - 1) "Lower") = decide (ℓ ≤ lo) := by
          simp only [Function.update_self, Function.update_of_ne (show "Lower" ≠ "Cursor" by decide),
            hL, decide_eq_decide]; omega
        simp only [this]; rfl
      refine ⟨2 + (3 * (top - 1 - ℓ) + 3) + 1, by simp [reportOut, h1, h2]; omega, ?_⟩
      have h2' : iterFlags 2 v = some { v with ctl := .pending [.report true 4] (.less "KP" "Cursor") } := by
        simp only [iterFlags, e1, Option.bind_some, e2]
      rw [iterFlags_add, iterFlags_add, h2', Option.bind_some, hf, Option.bind_some, iterFlags_one e3]
      simp only [reportOut, if_neg h1, if_pos h2]
    · have e2 : stepFlags { v with ctl := .pending [.report true 3] (.less "Cursor" "KP") } =
          some { v with ctl := .pending [.report true 9] (.less "Cursor" "Lower") } := by
        rw [fstep_less rfl, show decide (v.pos "Cursor" < v.pos "KP") = true by simp; omega]; rfl
      have e3 : stepFlags { v with ctl := .pending [.report true 9] (.less "Cursor" "Lower") } =
          some { v with ctl := .returned (some (decide (top ≤ lo))) } := by
        rw [fstep_less rfl]
        have : decide (v.pos "Cursor" < v.pos "Lower") = decide (top ≤ lo) := by
          simp only [hC, hL, decide_eq_decide]; omega
        simp only [this]; rfl
      refine ⟨3, by simp [reportOut, h1, h2], ?_⟩
      simp only [iterFlags, e1, Option.bind_some, e2, e3]
      simp only [reportOut, if_neg h1, if_neg h2, List.append_nil]
      rw [← hC, Function.update_eq_self]

end Report

/-! ## 5. The border controller (`k = 8`, `flags = true`, `tailOrigin = "TextOrigin"`) -/

section Helpers
variable {v : HVM} {cs : Config} {c' : Ctl}

theorem fcopy' {t s : String} (hv : v.ctl = .pending cs (.copy t s))
    (hr : (Ctl.pending cs (.copy t s)).resume tests false = c') :
    stepFlags v = some { v with
      pos := Function.update v.pos t (v.pos s)
      rev := Function.update v.rev t (v.rev s)
      ctl := c' } := by
  rw [fstep_copy hv, hr]

theorem fless' {a b : String} {d : Bool} (hv : v.ctl = .pending cs (.less a b))
    (hd : decide (v.pos a < v.pos b) = d) (hr : (Ctl.pending cs (.less a b)).resume tests d = c') :
    stepFlags v = some { v with ctl := c' } := by
  rw [fstep_less hv, hd, hr]

theorem fequal' {a b : String} {d : Bool} (hv : v.ctl = .pending cs (.equal a b))
    (hd : decide (v.pos a = v.pos b) = d) (hr : (Ctl.pending cs (.equal a b)).resume tests d = c') :
    stepFlags v = some { v with ctl := c' } := by
  rw [fstep_equal hv, hd, hr]

theorem fmove' {ms : List Movement} {π : String → ℤ} (hv : v.ctl = .pending cs (.move ms))
    (hm : moveSeq flagBlind v.len ms v.pos = some π)
    (hr : (Ctl.pending cs (.move ms)).resume tests false = c') :
    stepFlags v = some { v with pos := π, ctl := c' } := by
  rw [fstep_move hv hm, hr]

theorem fsym' {a b : String} {d : Bool} (hv : v.ctl = .pending cs (.symbols a b))
    (ha : a ∉ flagBlind) (hb : b ∉ flagBlind) (hra : v.inRange a) (hrb : v.inRange b)
    (hd : decide (v.view a = v.view b) = d)
    (hr : (Ctl.pending cs (.symbols a b)).resume tests d = c') :
    stepFlags v = some { v with ctl := c' } := by
  rw [fstep_symbols hv ha hb hra hrb, hd, hr]

theorem iterFlags_succ {n : ℕ} {v w u : HVM} (h : stepFlags v = some w)
    (h2 : iterFlags n w = some u) : iterFlags (n + 1) v = some u := by
  simp only [iterFlags, h, Option.bind_some, h2]

theorem moveSeq_cons_ok {Bl : List String} {len : ℤ} {m : Movement} {ms : List Movement}
    {π : String → ℤ} (h : m.head ∉ Bl → 0 ≤ π m.head + m.delta ∧ π m.head + m.delta ≤ len) :
    moveSeq Bl len (m :: ms) π = moveSeq Bl len ms (Function.update π m.head (π m.head + m.delta)) := by
  simp only [moveSeq, Function.update_self]
  rw [if_neg]
  intro hc
  exact hc.2 (h hc.1)

theorem moveSeq_nil' {Bl : List String} {len : ℤ} {π : String → ℤ} : moveSeq Bl len [] π = some π := rfl

end Helpers

/-- The list-level views of a stage: the text `(y.take L).reverse` read at `i` is `y[L-1-i]`. -/
theorem take_rev_get (y : List (Fin 2)) {L i : ℕ} (hL : L ≤ y.length) (hi : i < L) :
    ((y.take L).reverse)[i]? = y[L - 1 - i]? := by
  rw [List.getElem?_reverse (by simp; omega), List.length_take, Nat.min_eq_left hL,
    List.getElem?_take_of_lt (by omega)]

theorem take_drop_get (y : List (Fin 2)) {L s q : ℕ} (h : s + q < L) :
    ((y.take L).drop s)[q]? = y[s + q]? := by
  rw [List.getElem?_drop, List.getElem?_take_of_lt h]

theorem take_take_get (y : List (Fin 2)) {L s j : ℕ} (hj : j < s) (hs : s ≤ L) :
    ((y.take L).take s)[j]? = y[j]? := by
  rw [List.getElem?_take_of_lt hj, List.getElem?_take_of_lt (by omega)]

/-- The heads that persist across stages. `top = Cursor + 1` is the stream position. -/
structure Base (y : List (Fin 2)) (lo L top : ℕ) (v : HVM) : Prop where
  word : v.word = y
  origin : v.pos "Origin" = 0
  rOrigin : v.rev "Origin" = false
  end_ : v.pos "End" = L
  tail : v.pos "Tail" = (y.length : ℤ) - L
  rTail : v.rev "Tail" = true
  oend : v.pos "OriginalEnd" = y.length
  rOend : v.rev "OriginalEnd" = true
  lower : v.pos "Lower" = lo
  cursor : v.pos "Cursor" = (top : ℤ) - 1
  le : L ≤ y.length

/-- The heads that persisting heads are read through. -/
def baseHeads : List String :=
  ["Origin", "End", "Tail", "OriginalEnd", "Lower", "Cursor"]

theorem Base.congr {y : List (Fin 2)} {lo L top : ℕ} {v w : HVM} (h : Base y lo L top v)
    (hw : w.word = v.word) (hp : ∀ x ∈ baseHeads, w.pos x = v.pos x)
    (hr : ∀ x ∈ baseHeads, w.rev x = v.rev x) : Base y lo L top w where
  word := hw.trans h.word
  origin := (hp "Origin" (by simp [baseHeads])).trans h.origin
  rOrigin := (hr "Origin" (by simp [baseHeads])).trans h.rOrigin
  end_ := (hp "End" (by simp [baseHeads])).trans h.end_
  tail := (hp "Tail" (by simp [baseHeads])).trans h.tail
  rTail := (hr "Tail" (by simp [baseHeads])).trans h.rTail
  oend := (hp "OriginalEnd" (by simp [baseHeads])).trans h.oend
  rOend := (hr "OriginalEnd" (by simp [baseHeads])).trans h.rOend
  lower := (hp "Lower" (by simp [baseHeads])).trans h.lower
  cursor := (hp "Cursor" (by simp [baseHeads])).trans h.cursor
  le := h.le

theorem Base.len {y : List (Fin 2)} {lo L top : ℕ} {v : HVM} (h : Base y lo L top v) :
    v.len = y.length := by simp [HVM.len, h.word]

/-- The heads of a stage `(L, s, pe, p₁, r)` at the list-level scan state `⟨pos, q⟩`
(`BorderJob.ovStep`): `P = Tail + pos`, `KP = L - pos`, `A = s + q`, `B = P + s + q`. -/
structure Heads (y : List (Fin 2)) (L s : ℕ) (pe : Bool) (p₁ r pos q : ℕ) (v : HVM) : Prop where
  cut : v.pos "Cut" = s
  rCut : v.rev "Cut" = false
  per : pe = true → v.pos "First" = (s : ℤ) + p₁ ∧ v.pos "KFirst" = (s : ℤ) + 8 * p₁ ∧
    v.pos "Reach" = (s : ℤ) + r
  second : v.pos "Second" = (y.length : ℤ) - max 1 (2 * s)
  p : v.pos "P" = (y.length : ℤ) - L + pos
  rP : v.rev "P" = true
  kp : v.pos "KP" = (L : ℤ) - pos
  a : v.pos "A" = (s : ℤ) + q
  rA : v.rev "A" = false
  b : v.pos "B" = (y.length : ℤ) - L + pos + s + q
  rB : v.rev "B" = true
  front : pos + s + q ≤ L

/-- The heads a stage reads. -/
def stageHeads : List String :=
  ["Cut", "First", "KFirst", "Reach", "Second", "P", "KP", "A", "B"]

theorem Heads.congr {y : List (Fin 2)} {L s : ℕ} {pe : Bool} {p₁ r pos q : ℕ} {v w : HVM}
    (h : Heads y L s pe p₁ r pos q v) (hp : ∀ x ∈ stageHeads, w.pos x = v.pos x)
    (hr : ∀ x ∈ stageHeads, w.rev x = v.rev x) : Heads y L s pe p₁ r pos q w where
  cut := (hp "Cut" (by simp [stageHeads])).trans h.cut
  rCut := (hr "Cut" (by simp [stageHeads])).trans h.rCut
  per := fun hpe => by
    obtain ⟨h1, h2, h3⟩ := h.per hpe
    exact ⟨(hp "First" (by simp [stageHeads])).trans h1, (hp "KFirst" (by simp [stageHeads])).trans h2,
      (hp "Reach" (by simp [stageHeads])).trans h3⟩
  second := (hp "Second" (by simp [stageHeads])).trans h.second
  p := (hp "P" (by simp [stageHeads])).trans h.p
  rP := (hr "P" (by simp [stageHeads])).trans h.rP
  kp := (hp "KP" (by simp [stageHeads])).trans h.kp
  a := (hp "A" (by simp [stageHeads])).trans h.a
  rA := (hr "A" (by simp [stageHeads])).trans h.rA
  b := (hp "B" (by simp [stageHeads])).trans h.b
  rB := (hr "B" (by simp [stageHeads])).trans h.rB
  front := h.front

/-- The dual flag controller's frame while its border controller runs. -/
abbrev fc4 : Frame := .flagController "dual_flag_controller" 8 "TextOrigin" 4

/-- A control point of the border controller, inside the dual flag controller. -/
def bctl (fs : Bool) (pe : Option Bool) (site : ℕ) (e : Event) : Ctl :=
  .pending [fc4, .borderController 8 true "TextOrigin" fs pe site] e

section Scan
variable (y : List (Fin 2)) (lo L s : ℕ) (pe : Bool) (p₁ r : ℕ)

/-- The scan loop head (site 19): `B < OriginalEnd`? -/
def scanCtl (fs : Bool) (pe : Bool) : Ctl := bctl fs (some pe) 19 (.less "B" "OriginalEnd")

/-- A comparison that succeeds is one `ovStep` with `q + 1`. -/
theorem scan_hit (fs : Bool) (top pos q : ℕ) (v : HVM) (hv : v.ctl = scanCtl fs pe)
    (hB : Base y lo L top v) (hH : Heads y L s pe p₁ r pos q v) (hnf : pos + s + q < L)
    (heq : y[L - 1 - (pos + s + q)]? = y[s + q]?) :
    ∃ w, iterFlags 3 v = some w ∧ w.ctl = scanCtl fs pe ∧ Base y lo L top w ∧
      Heads y L s pe p₁ r pos (q + 1) w ∧ w.flags = v.flags := by
  have hm := hB.le
  have hlen := hB.len
  have e1 : stepFlags v = some { v with ctl := bctl fs (some pe) 20 (.symbols "A" "B") } :=
    fless' (d := true) hv (by rw [hH.b, hB.oend]; simp; omega) rfl
  have hvA : v.view "A" = y[s + q]? := by
    simp only [HVM.view, hH.rA, hH.a, hB.word, Bool.false_eq_true, if_false]
    congr 1 <;> omega
  have hvB : v.view "B" = y[L - 1 - (pos + s + q)]? := by
    simp only [HVM.view, hH.rB, hH.b, hB.word, if_true, HVM.len]
    congr 1 <;> omega
  have e2 : stepFlags { v with ctl := bctl fs (some pe) 20 (.symbols "A" "B") } =
      some { v with ctl := bctl fs (some pe) 21 (mv [("A", 1), ("B", 1)]) } :=
    fsym' (d := true) rfl (by decide) (by decide)
      (by simp only [HVM.inRange, HVM.len, hH.a, hB.word]; omega)
      (by simp only [HVM.inRange, HVM.len, hH.b, hB.word]; omega)
      (by show decide (v.view "A" = v.view "B") = true; rw [hvA, hvB, heq]; simp) rfl
  have e3 : stepFlags { v with ctl := bctl fs (some pe) 21 (mv [("A", 1), ("B", 1)]) } =
      some { v with
        pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B" (v.pos "B" + 1)
        ctl := scanCtl fs pe } := by
    refine fmove' (ms := [⟨"A", 1⟩, ⟨"B", 1⟩]) rfl ?_ rfl
    show moveSeq flagBlind v.len _ v.pos = _
    rw [moveSeq_cons_ok (by intro _; simp only [hH.a, hlen]; omega),
      moveSeq_cons_ok (by intro _; simp [Function.update, hH.b, hlen]; omega), moveSeq_nil']
    simp [Function.update]
  refine ⟨{ v with
      pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B" (v.pos "B" + 1)
      ctl := scanCtl fs pe }, ?_, rfl, ?_, ?_, rfl⟩
  · simp only [iterFlags, e1, Option.bind_some, e2, e3]
  · exact hB.congr rfl (fun x hx => by
      simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Function.update]) (fun _ _ => rfl)
  · exact {
      cut := by simp [Function.update, hH.cut]
      rCut := hH.rCut
      per := fun h => by simpa [Function.update] using hH.per h
      second := by simp [Function.update, hH.second]
      p := by simp [Function.update, hH.p]
      rP := hH.rP
      kp := by simp [Function.update, hH.kp]
      a := by simp [Function.update, hH.a]; ring
      rA := hH.rA
      b := by simp [Function.update, hH.b]; ring
      rB := hH.rB
      front := by omega }

/-- `shiftDecision` (`GsHeads.scala:525-528`): with a period, test `A < KFirst`; without, call
`ResetShift`. -/
def decisionCtl (fs pe : Bool) : Ctl :=
  if pe then bctl fs (some true) 32 (.less "A" "KFirst")
  else .pending [fc4, .borderController 8 true "TextOrigin" fs (some false) 35,
    .resetShift 8 true 0 none 1] (.equal "A" "Cut")

theorem decision_22 (fs pe : Bool) :
    (bctl fs (some pe) 22 (.equal "B" "OriginalEnd")).resume tests false = decisionCtl fs pe := by
  cases pe <;> rfl

theorem decision_31 (fs pe : Bool) :
    (bctl fs (some pe) 31 (.copy "B" "OriginalEnd")).resume tests false = decisionCtl fs pe := by
  cases pe <;> rfl

/-- A comparison that fails goes to the shift decision. -/
theorem scan_miss (fs : Bool) (top pos q : ℕ) (v : HVM) (hv : v.ctl = scanCtl fs pe)
    (hB : Base y lo L top v) (hH : Heads y L s pe p₁ r pos q v) (hnf : pos + s + q < L)
    (hne : y[L - 1 - (pos + s + q)]? ≠ y[s + q]?) :
    iterFlags 3 v = some { v with ctl := decisionCtl fs pe } := by
  have hm := hB.le
  have e1 : stepFlags v = some { v with ctl := bctl fs (some pe) 20 (.symbols "A" "B") } :=
    fless' (d := true) hv (by rw [hH.b, hB.oend]; simp; omega) rfl
  have hvA : v.view "A" = y[s + q]? := by
    simp only [HVM.view, hH.rA, hH.a, hB.word, Bool.false_eq_true, if_false]
    congr 1 <;> omega
  have hvB : v.view "B" = y[L - 1 - (pos + s + q)]? := by
    simp only [HVM.view, hH.rB, hH.b, hB.word, if_true, HVM.len]
    congr 1 <;> omega
  have e2 : stepFlags { v with ctl := bctl fs (some pe) 20 (.symbols "A" "B") } =
      some { v with ctl := bctl fs (some pe) 22 (.equal "B" "OriginalEnd") } :=
    fsym' (d := false) rfl (by decide) (by decide)
      (by simp only [HVM.inRange, HVM.len, hH.a, hB.word]; omega)
      (by simp only [HVM.inRange, HVM.len, hH.b, hB.word]; omega)
      (by show decide (v.view "A" = v.view "B") = false; rw [hvA, hvB]; simpa using fun h => hne h.symm)
      rfl
  have e3 : stepFlags { v with ctl := bctl fs (some pe) 22 (.equal "B" "OriginalEnd") } =
      some { v with ctl := decisionCtl fs pe } :=
    fequal' (d := false) rfl
      (by show decide (v.pos "B" = v.pos "OriginalEnd") = false; rw [hH.b, hB.oend]; simp; omega)
      (decision_22 fs pe)
  simp only [iterFlags, e1, Option.bind_some, e2, e3]

/-- The match head (site 18): `Second < P` is the stage guard `L < pos + max 1 (2s)`. -/
def matchCtl (fs pe : Bool) : Ctl := bctl fs (some pe) 18 (.less "Second" "P")

/-- The start of the stage shrink (site 36). -/
def shrinkCtl (fs pe : Bool) : Ctl := bctl fs (some pe) 36 (.copy "Second" "Origin")

theorem match_guard (fs : Bool) (top pos q : ℕ) (v : HVM) (hv : v.ctl = matchCtl fs pe)
    (hB : Base y lo L top v) (hH : Heads y L s pe p₁ r pos q v) :
    stepFlags v = some { v with
      ctl := if L < pos + max 1 (2 * s) then shrinkCtl fs pe else scanCtl fs pe } := by
  by_cases hg : L < pos + max 1 (2 * s)
  · rw [if_pos hg]
    exact fless' (d := true) hv (by rw [hH.second, hH.p]; simp; omega) rfl
  · rw [if_neg hg]
    exact fless' (d := false) hv (by rw [hH.second, hH.p]; simp; omega) rfl

theorem nonEmpty_liftCtl (f : Frame) (c : Ctl) : NonEmptyCtl (liftCtl f c) := by
  cases c with
  | pending cs e => simp [liftCtl, NonEmptyCtl]
  | returned val =>
    show NonEmptyCtl (Ctl.ofOutcome (advance defaultFuel f val))
    cases h : advance defaultFuel f val with
    | none => trivial
    | some o =>
      cases o with
      | yielded e cs => exact advance_yield_ne _ f val e cs h
      | returned _ => trivial
  | failed => trivial

/-- A child's run inside two callers. -/
theorem lift2_run {n : ℕ} {v w : HVM} (f g : Frame) (hv : NonEmptyCtl v.ctl)
    (h : iterFlags n v = some w) :
    iterFlags n (liftVM f (liftVM g v)) = some (liftVM f (liftVM g w)) :=
  iterFlags_lift f n _ _ (nonEmpty_liftCtl g v.ctl) (iterFlags_lift g n v w hv h)

theorem hvm_ctl_eta (v : HVM) (c : Ctl) (h : v.ctl = c) : ({ v with ctl := c } : HVM) = v := by
  subst h; rfl

/-- The reset shift inside the border controller: one `ovStep` shift without a period. -/
theorem reset_run (fs : Bool) (top pos q : ℕ) (v : HVM)
    (hv : v.ctl = .pending [fc4, .borderController 8 true "TextOrigin" fs (some pe) 35,
      .resetShift 8 true 0 none 1] (.equal "A" "Cut"))
    (hB : Base y lo L top v) (hH : Heads y L s pe p₁ r pos q v) (hq0 : q = 0 → pos + s < L) :
    ∃ n w, n ≤ 3 * q + 3 ∧ iterFlags n v = some w ∧ w.ctl = matchCtl fs pe ∧ Base y lo L top w ∧
      Heads y L s pe p₁ r (pos + rsShifts 8 q) 0 w ∧ w.flags = v.flags := by
  have hm := hB.le
  have hlen := hB.len
  have hfr := hH.front
  let vc : HVM := { v with ctl := Ctl.ofOutcome (next [.resetShift 8 true 0 none 0] none) }
  have hvcpos : vc.pos = v.pos := rfl
  have hvclen : vc.len = y.length := hlen
  obtain ⟨n, r', hn, hr', hrun⟩ := resetShift_flags 8 (by norm_num) vc q rfl
    (by rw [hvcpos, hH.a, hH.cut]) (by rw [hvcpos, hH.cut]; positivity)
    (by rw [hvcpos, hH.a, hvclen]; omega) (by rw [hvcpos, hH.b]; omega)
    (by rw [hvcpos, hH.b, hvclen]; omega)
    (by intro h0; rw [hvcpos, hH.b, hvclen]; have := hq0 h0; omega)
    (by rw [hvcpos, hH.p]; omega)
    (by
      rw [hvcpos, hH.p, hvclen]
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · have := hq0 h0; subst h0; simp; omega
      · have : q / 8 < q := Nat.div_lt_self h0 (by norm_num)
        omega)
  let bc : Frame := .borderController 8 true "TextOrigin" fs (some pe) 35
  have hl := lift2_run fc4 bc (nonEmpty_ofOutcome [.resetShift 8 true 0 none 0] none) hrun
  have hl0 : liftVM fc4 (liftVM bc vc) = v := by
    simp only [liftVM, vc]; exact hvm_ctl_eta v _ (hv.trans rfl)
  rw [hl0] at hl
  have ht : rsShifts 8 q ≤ max 1 q := by
    rw [rsShifts_eq 8 q (by norm_num)]
    exact max_le (le_max_left _ _) (PalPeg.ceilDiv_le_max (by norm_num))
  refine ⟨n, _, hn, hl, rfl, ?_, ?_, rfl⟩
  · refine hB.congr rfl (fun x hx => ?_) (fun x hx => ?_)
    · simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
      show rsPos v.pos q _ x = v.pos x
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rsPos]
    · exact hr' x (by
        simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · have hrv : ∀ x, x ≠ "Walk" → (liftVM fc4 (liftVM bc { vc with
        ctl := .returned none, pos := rsPos vc.pos q (rsShifts 8 q : ℕ), rev := r' })).rev x =
        v.rev x := fun x hx => hr' x hx
    have hpv : (liftVM fc4 (liftVM bc { vc with
        ctl := .returned none, pos := rsPos vc.pos q (rsShifts 8 q : ℕ), rev := r' })).pos =
        rsPos v.pos q (rsShifts 8 q : ℕ) := rfl
    exact {
      cut := by rw [hpv]; simp [rsPos, hH.cut]
      rCut := by rw [hrv _ (by decide)]; exact hH.rCut
      per := fun h => by rw [hpv]; simpa [rsPos] using hH.per h
      second := by rw [hpv]; simp [rsPos, hH.second]
      p := by rw [hpv]; simp [rsPos, hH.p]; ring
      rP := by rw [hrv _ (by decide)]; exact hH.rP
      kp := by rw [hpv]; simp [rsPos, hH.kp]; ring
      a := by rw [hpv]; simp [rsPos, hH.a]
      rA := by rw [hrv _ (by decide)]; exact hH.rA
      b := by rw [hpv]; simp [rsPos, hH.b]; ring
      rB := by rw [hrv _ (by decide)]; exact hH.rB
      front := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · have := hq0 h0; subst h0; simp at ht; omega
        · have : max 1 q = q := by omega
          omega }

/-- The period shift inside the border controller: `pos + p₁`, `q - p₁`. -/
theorem period_run (fs : Bool) (top pos q : ℕ) (v : HVM)
    (hv : v.ctl = .pending [fc4, .borderController 8 true "TextOrigin" fs (some true) 34,
      .periodShift 8 true 1] (.copy "Walk" "Cut"))
    (hB : Base y lo L top v) (hH : Heads y L s true p₁ r pos q v) (hq : p₁ ≤ q) :
    ∃ n w, n ≤ 2 * p₁ + 2 ∧ iterFlags n v = some w ∧ w.ctl = matchCtl fs true ∧ Base y lo L top w ∧
      Heads y L s true p₁ r (pos + p₁) (q - p₁) w ∧ w.flags = v.flags := by
  have hm := hB.le
  have hlen := hB.len
  have hfr := hH.front
  obtain ⟨hF, -, -⟩ := hH.per rfl
  let vc : HVM := { v with ctl := Ctl.ofOutcome (next [.periodShift 8 true 0] none) }
  have hvcpos : vc.pos = v.pos := rfl
  have hvclen : vc.len = y.length := hlen
  obtain ⟨r', hr', hrun⟩ := periodShift_flags 8 vc p₁ rfl
    (by rw [hvcpos, hH.cut, hF]) (by rw [hvcpos, hH.cut]; positivity)
    (by rw [hvcpos, hF, hvclen]; omega) (by rw [hvcpos, hH.a]; omega)
    (by rw [hvcpos, hH.a, hvclen]; omega) (by rw [hvcpos, hH.p]; omega)
    (by rw [hvcpos, hH.p, hvclen]; omega)
  let bc : Frame := .borderController 8 true "TextOrigin" fs (some true) 34
  have hl := lift2_run fc4 bc (nonEmpty_ofOutcome [.periodShift 8 true 0] none) hrun
  have hl0 : liftVM fc4 (liftVM bc vc) = v := by
    simp only [liftVM, vc]; exact hvm_ctl_eta v _ (hv.trans rfl)
  rw [hl0] at hl
  refine ⟨_, _, le_rfl, hl, rfl, ?_, ?_, rfl⟩
  · refine hB.congr rfl (fun x hx => ?_) (fun x hx => ?_)
    · simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
      show psPos v.pos p₁ x = v.pos x
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [psPos]
    · exact hr' x (by
        simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · have hrv : ∀ x, x ≠ "Walk" → (liftVM fc4 (liftVM bc { vc with
        ctl := .returned none, pos := psPos vc.pos p₁, rev := r' })).rev x = v.rev x :=
      fun x hx => hr' x hx
    have hpv : (liftVM fc4 (liftVM bc { vc with
        ctl := .returned none, pos := psPos vc.pos p₁, rev := r' })).pos = psPos v.pos p₁ := rfl
    exact {
      cut := by rw [hpv]; simp [psPos, hH.cut]
      rCut := by rw [hrv _ (by decide)]; exact hH.rCut
      per := fun h => by rw [hpv]; simpa [psPos] using hH.per h
      second := by rw [hpv]; simp [psPos, hH.second]
      p := by rw [hpv]; simp [psPos, hH.p]; ring
      rP := by rw [hrv _ (by decide)]; exact hH.rP
      kp := by rw [hpv]; simp [psPos, hH.kp]; ring
      a := by rw [hpv]; simp [psPos, hH.a]; omega
      rA := by rw [hrv _ (by decide)]; exact hH.rA
      b := by rw [hpv]; simp [psPos, hH.b]; omega
      rB := by rw [hrv _ (by decide)]; exact hH.rB
      front := by omega }

/-- The call of `ResetShift k true` (site 35). -/
def resetCtl (fs pe : Bool) : Ctl :=
  .pending [fc4, .borderController 8 true "TextOrigin" fs (some pe) 35, .resetShift 8 true 0 none 1]
    (.equal "A" "Cut")

/-- The call of `PeriodShift k true` (site 34). -/
def periodCtl (fs : Bool) : Ctl :=
  .pending [fc4, .borderController 8 true "TextOrigin" fs (some true) 34, .periodShift 8 true 1]
    (.copy "Walk" "Cut")

/-- The cost of a reset shift is paid by its potential. -/
theorem reset_phi (pos q : ℕ) :
    3 * q + 8 ≤ 32 * (Phi 8 ⟨pos + rsShifts 8 q, 0⟩ - Phi 8 ⟨pos, q⟩) := by
  simp only [Phi, rsShifts]; split_ifs <;> omega

/-- **The shift decision and the shift**: one `ovStep` shift, `⟨pos + gsShift, gsNextQ⟩`. Without
a period (`pe = false`) the stage's `(p₁, r)` must make `gsShift` the reset branch. Its cost is
paid by the potential `Φ = 9·pos + q`. -/
theorem shift_run (fs : Bool) (top pos q : ℕ) (v : HVM) (hv : v.ctl = decisionCtl fs pe)
    (hB : Base y lo L top v) (hH : Heads y L s pe p₁ r pos q v) (hq0 : q = 0 → pos + s < L)
    (hpe : pe = false → ¬(8 * p₁ ≤ q ∧ q ≤ r)) (hp₁ : 0 < p₁) :
    ∃ n w, n ≤ 32 * (Phi 8 ⟨pos + gsShift 8 p₁ r q, gsNextQ 8 p₁ r q⟩ - Phi 8 ⟨pos, q⟩) ∧
      iterFlags n v = some w ∧ w.ctl = matchCtl fs pe ∧ Base y lo L top w ∧
      Heads y L s pe p₁ r (pos + gsShift 8 p₁ r q) (gsNextQ 8 p₁ r q) w ∧ w.flags = v.flags := by
  have hreset : ¬(8 * p₁ ≤ q ∧ q ≤ r) → ∀ w : HVM, w.pos = v.pos → w.rev = v.rev →
      w.word = v.word → w.flags = v.flags → w.ctl = resetCtl fs pe →
      ∃ n w', n + 5 ≤ 32 * (Phi 8 ⟨pos + gsShift 8 p₁ r q, gsNextQ 8 p₁ r q⟩ - Phi 8 ⟨pos, q⟩) ∧
        iterFlags n w = some w' ∧ w'.ctl = matchCtl fs pe ∧ Base y lo L top w' ∧
        Heads y L s pe p₁ r (pos + gsShift 8 p₁ r q) (gsNextQ 8 p₁ r q) w' ∧ w'.flags = v.flags := by
    intro hn w hwp hwr hww hwf hwc
    have hBw : Base y lo L top w := hB.congr hww (fun x _ => by rw [hwp]) (fun x _ => by rw [hwr])
    have hHw : Heads y L s pe p₁ r pos q w := hH.congr (fun x _ => by rw [hwp]) (fun x _ => by rw [hwr])
    obtain ⟨n, w', hn', h1, h2, h3, h4, h5⟩ := reset_run y lo L s pe p₁ r fs top pos q w hwc hBw hHw hq0
    have hs : gsShift 8 p₁ r q = rsShifts 8 q := by
      rw [rsShifts_eq 8 q (by norm_num)]; simp [gsShift, hn]
    have hq : gsNextQ 8 p₁ r q = 0 := by simp [gsNextQ, hn]
    rw [hs, hq]
    exact ⟨n, w', by have := reset_phi pos q; omega, h1, h2, h3, h4, h5.trans hwf⟩
  cases pe with
  | false =>
    obtain ⟨n, w', hn, h1, h2, h3, h4, h5⟩ :=
      hreset (hpe rfl) v rfl rfl rfl rfl (by simpa [decisionCtl, resetCtl] using hv)
    exact ⟨n, w', by omega, h1, h2, h3, h4, h5⟩
  | true =>
    obtain ⟨hF, hKF, hR⟩ := hH.per rfl
    have hv' : v.ctl = bctl fs (some true) 32 (.less "A" "KFirst") := by simpa [decisionCtl] using hv
    by_cases h1 : q < 8 * p₁
    · have e1 : stepFlags v = some { v with ctl := resetCtl fs true } :=
        fless' (d := true) hv' (by rw [hH.a, hKF]; simp; omega) rfl
      obtain ⟨n, w', hn, h1', h2, h3, h4, h5⟩ :=
        hreset (by omega) { v with ctl := resetCtl fs true } rfl rfl rfl rfl rfl
      exact ⟨n + 1, w', by omega, iterFlags_succ e1 h1', h2, h3, h4, h5⟩
    · have e1 : stepFlags v = some { v with ctl := bctl fs (some true) 33 (.less "Reach" "A") } :=
        fless' (d := false) hv' (by rw [hH.a, hKF]; simp; omega) rfl
      by_cases h2 : r < q
      · have e2 : stepFlags { v with ctl := bctl fs (some true) 33 (.less "Reach" "A") } =
            some { v with ctl := resetCtl fs true } :=
          fless' (d := true) rfl
            (by show decide (v.pos "Reach" < v.pos "A") = true; rw [hH.a, hR]; simp; omega) rfl
        obtain ⟨n, w', hn, h1', h2', h3, h4, h5⟩ :=
          hreset (by omega) { v with ctl := resetCtl fs true } rfl rfl rfl rfl rfl
        exact ⟨n + 1 + 1, w', by omega, iterFlags_succ e1 (iterFlags_succ e2 h1'), h2', h3, h4, h5⟩
      · have e2 : stepFlags { v with ctl := bctl fs (some true) 33 (.less "Reach" "A") } =
            some { v with ctl := periodCtl fs } :=
          fless' (d := false) rfl
            (by show decide (v.pos "Reach" < v.pos "A") = false; rw [hH.a, hR]; simp; omega) rfl
        have hp1 : p₁ ≤ q := by omega
        obtain ⟨n, w', hn, h1', h2', h3, h4, h5⟩ := period_run y lo L s p₁ r fs top pos q
          { v with ctl := periodCtl fs } rfl
          (hB.congr rfl (fun _ _ => rfl) (fun _ _ => rfl)) (hH.congr (fun _ _ => rfl) (fun _ _ => rfl))
          hp1
        have hs : gsShift 8 p₁ r q = p₁ := by simp [gsShift]; omega
        have hq : gsNextQ 8 p₁ r q = q - p₁ := by simp [gsNextQ]; omega
        rw [hs, hq]
        refine ⟨n + 1 + 1, w', ?_, iterFlags_succ e1 (iterFlags_succ e2 h1'), h2', h3, h4, h5⟩
        simp only [Phi]; omega

theorem update2_self (π : String → ℤ) (a b : String) (x z : ℤ) (hx : π a = x) (hz : π b = z) :
    Function.update (Function.update π a x) b z = π := by
  funext t
  by_cases h1 : t = b
  · subst h1; simp [hz]
  · by_cases h2 : t = a
    · subst h2; simp [Function.update, h1, hx]
    · simp [Function.update, h1, h2]

/-- The prefix check at the frontier (sites 25-27): `Walk` runs over `u = x.take s` (forward) and
`B` over the text from `P` (reversed), stopping at the first mismatch. -/
theorem prefix_run (fs : Bool) (top pos : ℕ) (hps : pos + s < L) :
    ∀ (d c : ℕ) (v : HVM), c + d = s → v.ctl = bctl fs (some pe) 25 (.less "Walk" "Cut") →
      Base y lo L top v → v.pos "Cut" = s → v.pos "Walk" = c → v.rev "Walk" = false →
      v.pos "B" = (y.length : ℤ) - L + pos + c → v.rev "B" = true →
      ∃ n c', n ≤ 3 * d + 2 ∧ c ≤ c' ∧ c' ≤ s ∧
        (c' = s ↔ ∀ j, c ≤ j → j < s → y[L - 1 - (pos + j)]? = y[j]?) ∧
        iterFlags n v = some { v with
          ctl := bctl fs (some pe) 28 (.equal "Walk" "Cut")
          pos := Function.update (Function.update v.pos "Walk" c') "B"
            ((y.length : ℤ) - L + pos + c') }
  | 0, c, v, hcd, hv, hB, hC, hW, hrW, hBp, hrB => by
    have e1 : stepFlags v = some { v with ctl := bctl fs (some pe) 28 (.equal "Walk" "Cut") } :=
      fless' (d := false) hv (by rw [hW, hC]; simp; omega) rfl
    refine ⟨1, c, by omega, le_rfl, by omega, ⟨fun _ j h1 h2 => by omega, fun _ => by omega⟩, ?_⟩
    rw [iterFlags_one e1]
    congr 2
    exact (update2_self _ _ _ _ _ hW hBp).symm
  | d + 1, c, v, hcd, hv, hB, hC, hW, hrW, hBp, hrB => by
    have hm := hB.le
    have hlen := hB.len
    have e1 : stepFlags v = some { v with ctl := bctl fs (some pe) 26 (.symbols "Walk" "B") } :=
      fless' (d := true) hv (by rw [hW, hC]; simp; omega) rfl
    have hvW : v.view "Walk" = y[c]? := by
      simp only [HVM.view, hrW, hW, hB.word, Bool.false_eq_true, if_false]
      congr 1
    have hvB : v.view "B" = y[L - 1 - (pos + c)]? := by
      simp only [HVM.view, hrB, hBp, hB.word, if_true, HVM.len]
      congr 1 <;> omega
    by_cases heq : y[L - 1 - (pos + c)]? = y[c]?
    · have e2 : stepFlags { v with ctl := bctl fs (some pe) 26 (.symbols "Walk" "B") } =
          some { v with ctl := bctl fs (some pe) 27 (mv [("Walk", 1), ("B", 1)]) } :=
        fsym' (d := true) rfl (by decide) (by decide)
          (by simp only [HVM.inRange, HVM.len, hW, hB.word]; omega)
          (by simp only [HVM.inRange, HVM.len, hBp, hB.word]; omega)
          (by show decide (v.view "Walk" = v.view "B") = true; rw [hvW, hvB, heq]; simp) rfl
      have e3 : stepFlags { v with ctl := bctl fs (some pe) 27 (mv [("Walk", 1), ("B", 1)]) } =
          some { v with
            pos := Function.update (Function.update v.pos "Walk" (v.pos "Walk" + 1)) "B"
              (v.pos "B" + 1)
            ctl := bctl fs (some pe) 25 (.less "Walk" "Cut") } := by
        refine fmove' (ms := [⟨"Walk", 1⟩, ⟨"B", 1⟩]) rfl ?_ rfl
        show moveSeq flagBlind v.len _ v.pos = _
        rw [moveSeq_cons_ok (by intro _; simp only [hW, hlen]; omega),
          moveSeq_cons_ok (by intro _; simp [Function.update, hBp, hlen]; omega), moveSeq_nil']
        simp [Function.update]
      obtain ⟨n, c', hn, h1, h2, h3, h4⟩ := prefix_run fs top pos hps d (c + 1) { v with
          pos := Function.update (Function.update v.pos "Walk" (v.pos "Walk" + 1)) "B"
            (v.pos "B" + 1)
          ctl := bctl fs (some pe) 25 (.less "Walk" "Cut") } (by omega) rfl
        (hB.congr rfl (fun x hx => by
          simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Function.update])
          (fun _ _ => rfl))
        (by simp [Function.update, hC]) (by simp [Function.update, hW])
        (by simp [hrW]) (by simp [Function.update, hBp]; push_cast; ring) hrB
      refine ⟨3 + n, c', by omega, by omega, h2, ?_, ?_⟩
      · rw [h3]
        constructor
        · intro hj j hj1 hj2
          rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
          · exact heq
          · exact hj j hlt hj2
        · intro hj j hj1 hj2; exact hj j (by omega) hj2
      · have h3' : iterFlags 3 v = some { v with
            pos := Function.update (Function.update v.pos "Walk" (v.pos "Walk" + 1)) "B"
              (v.pos "B" + 1)
            ctl := bctl fs (some pe) 25 (.less "Walk" "Cut") } := by
          simp only [iterFlags, e1, Option.bind_some, e2, e3]
        rw [iterFlags_add, h3', Option.bind_some, h4]
        congr 2
        funext x
        by_cases hx1 : x = "B"
        · subst hx1; simp
        · by_cases hx2 : x = "Walk"
          · subst hx2; simp
          · simp [Function.update, hx1, hx2]
    · have e2 : stepFlags { v with ctl := bctl fs (some pe) 26 (.symbols "Walk" "B") } =
          some { v with ctl := bctl fs (some pe) 28 (.equal "Walk" "Cut") } :=
        fsym' (d := false) rfl (by decide) (by decide)
          (by simp only [HVM.inRange, HVM.len, hW, hB.word]; omega)
          (by simp only [HVM.inRange, HVM.len, hBp, hB.word]; omega)
          (by show decide (v.view "Walk" = v.view "B") = false; rw [hvW, hvB]
              simpa using fun h => heq h.symm) rfl
      refine ⟨2, c, by omega, le_rfl, by omega, ⟨fun h => by omega, fun h => absurd (h c le_rfl (by omega)) heq⟩, ?_⟩
      simp only [iterFlags, e1, Option.bind_some, e2]
      congr 2
      exact (update2_self _ _ _ _ _ hW hBp).symm

/-- Where a scan step leaves the controller before its shift: at the shift decision with the
stream at `t`, or done. -/
def DecEnd (fs pe : Bool) (top' : ℕ → HVM → Prop) (w : HVM) : Option ℕ → Prop
  | none => w.flagsDone
  | some t => w.ctl = decisionCtl fs pe ∧ top' t w

/-- The report call at site 29. -/
def repCallCtl (fs pe : Bool) : Ctl :=
  .pending [fc4, .borderController 8 true "TextOrigin" fs (some pe) 29, .report true 2]
    (.less "KP" "Lower")

/-- The finish call after a stopping report (site 30). -/
def finCallCtl (fs pe : Bool) : Ctl :=
  .pending [fc4, .borderController 8 true "TextOrigin" fs (some pe) 30, .finishFlags 1]
    (.less "Cursor" "Lower")

theorem fsRun_single (lo top ℓ : ℕ) : fsRun lo top [ℓ] =
    if (reportOut lo top ℓ).2.2 then
      ((reportOut lo top ℓ).1 ++ BorderJobHead.finishBits lo (reportOut lo top ℓ).2.1, none)
    else ((reportOut lo top ℓ).1, some (reportOut lo top ℓ).2.1) := by
  rw [fsRun_cons]; split_ifs <;> simp [fsRun]

/-- `w` is `v` after `Cursor := c` and `B := OriginalEnd` (the report and the restore of `B`). -/
def Restored (v w : HVM) (c : ℤ) : Prop :=
  w.word = v.word ∧ w.pos "Cursor" = c ∧ w.pos "B" = v.pos "OriginalEnd" ∧
    w.rev "B" = v.rev "OriginalEnd" ∧ (∀ x, x ≠ "B" → x ≠ "Cursor" → w.pos x = v.pos x) ∧
    (∀ x, x ≠ "B" → w.rev x = v.rev x)

/-- The stream position a stage part ends with (`0` when the stream has finished). -/
def endTop : Option ℕ → ℕ
  | none => 0
  | some t => t

theorem reportOut_le (lo top ℓ : ℕ) : (reportOut lo top ℓ).2.1 ≤ top := by
  unfold reportOut; split_ifs <;> simp <;> omega

/-- **A report inside the border controller** (site 29 onwards): `Report`, then either
`FinishFlags` (done) or `B := OriginalEnd` and the shift decision. -/
theorem report_call (fs : Bool) (top ℓ : ℕ) (v : HVM) (hv : v.ctl = repCallCtl fs pe)
    (hK : v.pos "KP" = (ℓ : ℤ)) (hC : v.pos "Cursor" = (top : ℤ) - 1) (hL : v.pos "Lower" = lo)
    (hO : v.pos "Origin" = 0) :
    ∃ n w, n + 4 * endTop (fsRun lo top [ℓ]).2 ≤ 4 * top + 8 ∧ iterFlags n v = some w ∧
      w.flags = v.flags ++ (fsRun lo top [ℓ]).1 ∧
      DecEnd fs pe (fun t w => Restored v w ((t : ℤ) - 1)) w (fsRun lo top [ℓ]).2 := by
  let vc : HVM := { v with ctl := repHead }
  obtain ⟨n, hn, hrun⟩ := report_run lo top ℓ vc rfl hK hC hL
  have hle := reportOut_le lo top ℓ
  let bc : Frame := .borderController 8 true "TextOrigin" fs (some pe) 29
  have hl := lift2_run fc4 bc (by simp [vc, repHead, NonEmptyCtl]) hrun
  have hl0 : liftVM fc4 (liftVM bc vc) = v := by
    simp only [liftVM, vc]; exact hvm_ctl_eta v _ (hv.trans rfl)
  rw [hl0] at hl
  rw [fsRun_single]
  generalize hro : reportOut lo top ℓ = ro at hl hn hle
  obtain ⟨bits, t', ret⟩ := ro
  simp only at hl hn hle ⊢
  cases ret with
  | true =>
    have hctl : liftCtl fc4 (liftCtl bc (.returned (some true))) = finCallCtl fs pe := rfl
    let w1 : HVM := { v with
      ctl := finCallCtl fs pe
      pos := Function.update v.pos "Cursor" ((t' : ℤ) - 1)
      flags := v.flags ++ bits }
    have hl' : iterFlags n v = some w1 := by
      rw [hl]; simp only [liftVM, vc, hctl]; rfl
    let vf : HVM := { w1 with ctl := ffHead }
    have hf := finish_run lo t' vf rfl (by simp [vf, w1]) (by simp [vf, w1, Function.update, hL])
      (by simp [vf, w1, Function.update, hO])
    let bc30 : Frame := .borderController 8 true "TextOrigin" fs (some pe) 30
    have hl2 := lift2_run fc4 bc30 (by simp [vf, ffHead, NonEmptyCtl]) hf
    have hl20 : liftVM fc4 (liftVM bc30 vf) = w1 := by
      simp only [liftVM, vf]; exact hvm_ctl_eta w1 _ rfl
    rw [hl20] at hl2
    refine ⟨n + (4 * (t' - lo) + 1), _, ?_, iterFlags_trans hl' hl2, ?_, ⟨none, rfl⟩⟩
    · simp only [if_true, endTop]; omega
    · simp [liftVM, vf, w1, List.append_assoc]
  | false =>
    have hctl : liftCtl fc4 (liftCtl bc (.returned (some false))) =
        bctl fs (some pe) 31 (.copy "B" "OriginalEnd") := rfl
    let w1 : HVM := { v with
      ctl := bctl fs (some pe) 31 (.copy "B" "OriginalEnd")
      pos := Function.update v.pos "Cursor" ((t' : ℤ) - 1)
      flags := v.flags ++ bits }
    have hl' : iterFlags n v = some w1 := by
      rw [hl]; simp only [liftVM, vc, hctl]; rfl
    have e1 := fcopy' (v := w1) rfl (decision_31 fs pe)
    refine ⟨n + 1, _, ?_, iterFlags_trans hl' (iterFlags_one e1), rfl, rfl, ?_⟩
    · simp only [Bool.false_eq_true, if_false, endTop]; omega
    refine ⟨rfl, by simp [w1, Function.update], by simp [w1, Function.update],
      by simp [w1, Function.update], fun x h1 h2 => by simp [w1, Function.update, h1, h2],
      fun x h1 => by simp [w1, Function.update, h1]⟩

/-- The stage relation survives changes of `Walk` and of the stream position. -/
theorem restore_rel {top t pos q : ℕ} {v w : HVM} (hB : Base y lo L top v)
    (hH : Heads y L s pe p₁ r pos q v) (hw : w.word = v.word) (hc : w.pos "Cursor" = (t : ℤ) - 1)
    (hp : ∀ x, x ≠ "Walk" → x ≠ "Cursor" → w.pos x = v.pos x)
    (hr : ∀ x, x ≠ "Walk" → w.rev x = v.rev x) :
    Base y lo L t w ∧ Heads y L s pe p₁ r pos q w := by
  refine ⟨⟨hw.trans hB.word, (hp _ (by decide) (by decide)).trans hB.origin,
    (hr _ (by decide)).trans hB.rOrigin, (hp _ (by decide) (by decide)).trans hB.end_,
    (hp _ (by decide) (by decide)).trans hB.tail, (hr _ (by decide)).trans hB.rTail,
    (hp _ (by decide) (by decide)).trans hB.oend, (hr _ (by decide)).trans hB.rOend,
    (hp _ (by decide) (by decide)).trans hB.lower, hc, hB.le⟩, ?_⟩
  refine hH.congr (fun x hx => hp x ?_ ?_) (fun x hx => hr x ?_) <;>
  · simp only [stageHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The frontier** (`B = OriginalEnd`, sites 22-31): the prefix check `MatchLen u T pos |u|`,
the report of `ℓ = L - pos` when it holds, and `B := OriginalEnd`. -/
theorem front_run (fs : Bool) (top pos q : ℕ) (v : HVM) (hv : v.ctl = scanCtl fs pe)
    (hB : Base y lo L top v) (hH : Heads y L s pe p₁ r pos q v) (hfr : pos + s + q = L)
    (hq1 : 1 ≤ q) :
    ∃ n w, n + 4 * endTop (fsRun lo top
        (if (∀ j, j < s → y[L - 1 - (pos + j)]? = y[j]?) then [L - pos] else [])).2 ≤
        4 * top + 3 * s + 16 ∧ iterFlags n v = some w ∧
      w.flags = v.flags ++ (fsRun lo top
        (if (∀ j, j < s → y[L - 1 - (pos + j)]? = y[j]?) then [L - pos] else [])).1 ∧
      DecEnd fs pe (fun t w => Base y lo L t w ∧ Heads y L s pe p₁ r pos q w) w
        (fsRun lo top (if (∀ j, j < s → y[L - 1 - (pos + j)]? = y[j]?) then [L - pos] else [])).2 := by
  have hm := hB.le
  have hlen := hB.len
  have e1 : stepFlags v = some { v with ctl := bctl fs (some pe) 22 (.equal "B" "OriginalEnd") } :=
    fless' (d := false) hv (by rw [hH.b, hB.oend]; simp; omega) rfl
  have e2 : stepFlags { v with ctl := bctl fs (some pe) 22 (.equal "B" "OriginalEnd") } =
      some { v with ctl := bctl fs (some pe) 23 (.copy "Walk" "Origin") } :=
    fequal' (d := true) rfl
      (by show decide (v.pos "B" = v.pos "OriginalEnd") = true; rw [hH.b, hB.oend]; simp; omega) rfl
  let w3 : HVM := { v with
    pos := Function.update v.pos "Walk" (v.pos "Origin")
    rev := Function.update v.rev "Walk" (v.rev "Origin")
    ctl := bctl fs (some pe) 24 (.copy "B" "P") }
  have e3 : stepFlags { v with ctl := bctl fs (some pe) 23 (.copy "Walk" "Origin") } = some w3 :=
    fcopy' rfl rfl
  let w4 : HVM := { w3 with
    pos := Function.update w3.pos "B" (w3.pos "P")
    rev := Function.update w3.rev "B" (w3.rev "P")
    ctl := bctl fs (some pe) 25 (.less "Walk" "Cut") }
  have e4 : stepFlags w3 = some w4 := fcopy' rfl rfl
  have h4 : iterFlags 4 v = some w4 := by simp only [iterFlags, e1, Option.bind_some, e2, e3, e4]
  have hB4 : Base y lo L top w4 := hB.congr rfl
    (fun x hx => by
      simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [w4, w3, Function.update])
    (fun x hx => by
      simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [w4, w3, Function.update])
  obtain ⟨n5, c', hn5, -, hc's, hiff, h5⟩ := prefix_run y lo L s pe fs top pos (by omega) s 0 w4
    (by omega) rfl hB4 (by simp [w4, w3, Function.update, hH.cut])
    (by simp [w4, w3, Function.update, hB.origin]) (by simp [w4, w3, Function.update, hB.rOrigin])
    (by simp [w4, w3, Function.update, hH.p]) (by simp [w4, w3, Function.update, hH.rP])
  have hM : (c' = s) ↔ (∀ j, j < s → y[L - 1 - (pos + j)]? = y[j]?) := by
    rw [hiff]; exact ⟨fun h j hj => h j (Nat.zero_le _) hj, fun h j _ hj => h j hj⟩
  let w5 : HVM := { w4 with
    ctl := bctl fs (some pe) 28 (.equal "Walk" "Cut")
    pos := Function.update (Function.update w4.pos "Walk" c') "B" ((y.length : ℤ) - L + pos + c') }
  have hw5p : ∀ x, x ≠ "Walk" → x ≠ "B" → w5.pos x = v.pos x := fun x h1 h2 => by
    simp [w5, w4, w3, Function.update, h1, h2]
  have hw5r : ∀ x, x ≠ "Walk" → x ≠ "B" → w5.rev x = v.rev x := fun x h1 h2 => by
    simp [w5, w4, w3, Function.update, h1, h2]
  have hvB : v.pos "B" = v.pos "OriginalEnd" := by rw [hH.b, hB.oend]; omega
  by_cases hMs : ∀ j, j < s → y[L - 1 - (pos + j)]? = y[j]?
  · rw [if_pos hMs]
    have hcs : c' = s := hM.mpr hMs
    have e5 : stepFlags w5 = some { w5 with ctl := repCallCtl fs pe } :=
      fequal' (d := true) rfl
        (by show decide (w5.pos "Walk" = w5.pos "Cut") = true
            simp [w5, w4, w3, Function.update, hH.cut, hcs]) rfl
    obtain ⟨n6, w, hn6, h6, hfl, hend⟩ := report_call lo pe fs top (L - pos) { w5 with ctl := repCallCtl fs pe }
      rfl (by simp [w5, w4, w3, Function.update, hH.kp]; omega)
      (by simp [w5, w4, w3, Function.update, hB.cursor]) (by simp [w5, w4, w3, Function.update, hB.lower])
      (by simp [w5, w4, w3, Function.update, hB.origin])
    refine ⟨4 + n5 + 1 + n6, w, by omega, ?_, ?_, ?_⟩
    · rw [iterFlags_add, iterFlags_add, iterFlags_add, h4, Option.bind_some, h5, Option.bind_some,
        iterFlags_one e5, Option.bind_some, h6]
    · rw [hfl]
    · cases ho : (fsRun lo top [L - pos]).2 with
      | none => rw [ho] at hend; exact hend
      | some t =>
        rw [ho] at hend
        obtain ⟨hwc, hwr, hwc', hwB, hwrB, hwp, hwrr⟩ := hend
        refine ⟨hwc, restore_rel y lo L s pe p₁ r hB hH hwr hwc' (fun x h1 h2 => ?_) (fun x h1 => ?_)⟩
        · by_cases hxB : x = "B"
          · subst hxB; rw [hwB, hvB]; simp [w5, w4, w3, Function.update]
          · rw [hwp x hxB h2]; exact hw5p x h1 hxB
        · by_cases hxB : x = "B"
          · subst hxB; rw [hwrB]; simp [w5, w4, w3, Function.update, hB.rOend, hH.rB]
          · rw [hwrr x hxB]; exact hw5r x h1 hxB
  · rw [if_neg hMs]
    have hcs : c' ≠ s := fun h => hMs (hM.mp h)
    have e5 : stepFlags w5 = some { w5 with ctl := bctl fs (some pe) 31 (.copy "B" "OriginalEnd") } :=
      fequal' (d := false) rfl
        (by show decide (w5.pos "Walk" = w5.pos "Cut") = false
            simp [w5, w4, w3, Function.update, hH.cut]; omega) rfl
    have e6 := fcopy' (v := { w5 with ctl := bctl fs (some pe) 31 (.copy "B" "OriginalEnd") }) rfl
      (decision_31 fs pe)
    let w7 : HVM := { w5 with
      ctl := decisionCtl fs pe
      pos := Function.update w5.pos "B" (w5.pos "OriginalEnd")
      rev := Function.update w5.rev "B" (w5.rev "OriginalEnd") }
    have e6' : stepFlags { w5 with ctl := bctl fs (some pe) 31 (.copy "B" "OriginalEnd") } = some w7 :=
      e6
    refine ⟨4 + n5 + 1 + 1, w7, by simp [fsRun, endTop]; omega, ?_, ?_, ?_⟩
    · rw [iterFlags_add, iterFlags_add, iterFlags_add, h4, Option.bind_some, h5, Option.bind_some,
        iterFlags_one e5, Option.bind_some, iterFlags_one e6']
    · simp [fsRun, w7, w5, w4, w3]
    show w7.ctl = decisionCtl fs pe ∧ (Base y lo L top w7 ∧ Heads y L s pe p₁ r pos q w7)
    refine ⟨rfl, ?_⟩
    · refine restore_rel y lo L s pe p₁ r hB hH rfl
        (by simp [w7, w5, w4, w3, Function.update, hB.cursor])
        (fun x h1 h2 => ?_) (fun x h1 => ?_)
      · by_cases hxB : x = "B"
        · subst hxB; simp [w7, w5, w4, w3, Function.update, hvB]
        · simp only [w7, Function.update_of_ne hxB]; exact hw5p x h1 hxB
      · by_cases hxB : x = "B"
        · subst hxB; simp [w7, w5, w4, w3, Function.update, hB.rOend, hH.rB]
        · simp only [w7, Function.update_of_ne hxB]; exact hw5r x h1 hxB

/-! ### The stage's list-level scan -/

/-- One stage's `ovRun` (`BorderJobHead.stageRunFrom` from any state). -/
def stRun (L s p₁ r F : ℕ) (st : ScanState) : List ℕ :=
  ovRun ((y.take L).take s) ((y.take L).drop s) (y.take L).reverse 8 p₁ r (max 1 (2 * s)) F st

/-- The stage's `ovStep`. -/
def stStep (L s p₁ r : ℕ) (st : ScanState) : ScanState :=
  ovStep ((y.take L).take s) ((y.take L).drop s) (y.take L).reverse 8 p₁ r st

theorem stageRunFrom_eq (L s p₁ r F start : ℕ) :
    BorderJobHead.stageRunFrom (y.take L) 8 s p₁ r F start = stRun y L s p₁ r F ⟨start, 0⟩ := rfl

/-- The prefix test of a frontier, at the list level (`MatchLen u T pos |u|`). -/
def PrefixOK (L s pos : ℕ) : Prop := ∀ j, j < s → y[L - 1 - (pos + j)]? = y[j]?

instance (L s pos : ℕ) : Decidable (PrefixOK y L s pos) := by unfold PrefixOK; infer_instance

theorem stRun_succ (hm : L ≤ y.length) (hsL : s ≤ L) (F pos q : ℕ)
    (hg : pos + max 1 (2 * s) ≤ L) (hfr : pos + s + q ≤ L) :
    stRun y L s p₁ r (F + 1) ⟨pos, q⟩ =
      (if pos + s + q = L ∧ PrefixOK y L s pos then [L - pos] else []) ++
        stRun y L s p₁ r F (stStep y L s p₁ r ⟨pos, q⟩) := by
  have hT : ((y.take L).reverse).length = L := by simp; omega
  have hU : ((y.take L).take s).length = s := by simp; omega
  unfold stRun
  rw [ovRun, if_neg (by rw [hT]; simp; omega)]
  simp only [hT, hU, ScanState.mk_pos, ScanState.mk_q]
  have hM : MatchLen ((y.take L).take s) (y.take L).reverse pos s ↔ PrefixOK y L s pos := by
    unfold MatchLen PrefixOK
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    rw [take_rev_get y hm (by omega), take_take_get y hj hsL]
  by_cases hc : pos + s + q = L ∧ PrefixOK y L s pos
  · rw [if_pos ⟨hc.1, hM.mpr hc.2⟩, if_pos hc]; rfl
  · rw [if_neg (fun h => hc ⟨h.1, hM.mp h.2⟩), if_neg hc]; rfl

theorem stStep_shift (hm : L ≤ y.length) (hsL : s ≤ L) (pos q : ℕ)
    (h : pos + s + q = L ∨ (pos + s + q < L ∧ y[L - 1 - (pos + s + q)]? ≠ y[s + q]?)) :
    stStep y L s p₁ r ⟨pos, q⟩ = ⟨pos + gsShift 8 p₁ r q, gsNextQ 8 p₁ r q⟩ := by
  have hT : ((y.take L).reverse).length = L := by simp; omega
  have hU : ((y.take L).take s).length = s := by simp; omega
  unfold stStep ovStep
  simp only [hT, hU, ScanState.mk_pos, ScanState.mk_q]
  rcases h with h | ⟨h1, h2⟩
  · rw [if_pos h]
  · rw [if_neg (by omega), if_neg]
    rw [take_rev_get y hm h1, take_drop_get y (by omega)]
    exact h2

theorem stStep_hit (hm : L ≤ y.length) (hsL : s ≤ L) (pos q : ℕ) (h1 : pos + s + q < L)
    (h2 : y[L - 1 - (pos + s + q)]? = y[s + q]?) :
    stStep y L s p₁ r ⟨pos, q⟩ = ⟨pos, q + 1⟩ := by
  have hT : ((y.take L).reverse).length = L := by simp; omega
  have hU : ((y.take L).take s).length = s := by simp; omega
  unfold stStep ovStep
  simp only [hT, hU, ScanState.mk_pos, ScanState.mk_q]
  rw [if_neg (by omega), if_pos]
  rw [take_rev_get y hm h1, take_drop_get y (by omega)]
  exact h2

/-- Where a stage ends: the stream finished (the program returned), or the shrink starts with the
stream continuing from `t`. -/
def StageEnd (L s : ℕ) (fs pe : Bool) (w : HVM) : Option ℕ → Prop
  | none => w.flagsDone
  | some t => w.ctl = shrinkCtl fs pe ∧ Base y lo L t w ∧ w.pos "Cut" = s

/-- A frontier's prefix check and report are paid by the shift that follows (`q ≥ s` there; a
period shift needs `cut_charge`, `s ≤ 8·p₁`). -/
theorem front_phi (pos q s p₁ r : ℕ) (hqs : s ≤ q) (hq1 : 1 ≤ q) (hp : 0 < p₁)
    (hchg : 8 * p₁ ≤ q ∧ q ≤ r → s ≤ 8 * p₁) :
    3 * s + 17 ≤ 68 * (Phi 8 ⟨pos + gsShift 8 p₁ r q, gsNextQ 8 p₁ r q⟩ - Phi 8 ⟨pos, q⟩) := by
  simp only [Phi, gsShift, gsNextQ, ceilDiv]
  split_ifs with h
  · have := hchg h; omega
  · rw [Nat.max_def]; split_ifs <;> omega

theorem shift_phi (pos q p₁ r : ℕ) (hp : 0 < p₁) :
    1 ≤ Phi 8 ⟨pos + gsShift 8 p₁ r q, gsNextQ 8 p₁ r q⟩ - Phi 8 ⟨pos, q⟩ := by
  simp only [Phi, gsShift, gsNextQ, ceilDiv]
  split_ifs with h
  · omega
  · rw [Nat.max_def]; split_ifs <;> omega

/-- From the match head with `F` fuel, the controller produces the stream of `stRun F`; with
`cut_charge` its step count is paid by the potential `100·(9L − Φ) + 4·top`. -/
def MatchClaim (fs : Bool) (F : ℕ) : Prop :=
  ∀ (top pos q : ℕ) (v : HVM), v.ctl = matchCtl fs pe → Base y lo L top v →
    Heads y L s pe p₁ r pos q v → 10 * L < Phi 8 ⟨pos, q⟩ + F →
    ∃ n w, ((pe = true → s ≤ 8 * p₁) →
        n + 4 * endTop (fsRun lo top (stRun y L s p₁ r F ⟨pos, q⟩)).2 ≤
          100 * (9 * L - Phi 8 ⟨pos, q⟩) + 4 * top + 3) ∧
      iterFlags n v = some w ∧
      w.flags = v.flags ++ (fsRun lo top (stRun y L s p₁ r F ⟨pos, q⟩)).1 ∧
      StageEnd y lo L s fs pe w (fsRun lo top (stRun y L s p₁ r F ⟨pos, q⟩)).2

/-- The same from the scan head, once the guard has passed. -/
def ScanClaim (fs : Bool) (F : ℕ) : Prop :=
  ∀ (top pos q : ℕ) (v : HVM), v.ctl = scanCtl fs pe → Base y lo L top v →
    Heads y L s pe p₁ r pos q v → pos + max 1 (2 * s) ≤ L → 10 * L < Phi 8 ⟨pos, q⟩ + F →
    ∃ n w, ((pe = true → s ≤ 8 * p₁) →
        n + 4 * endTop (fsRun lo top (stRun y L s p₁ r F ⟨pos, q⟩)).2 ≤
          100 * (9 * L - Phi 8 ⟨pos, q⟩) + 4 * top + 2) ∧
      iterFlags n v = some w ∧
      w.flags = v.flags ++ (fsRun lo top (stRun y L s p₁ r F ⟨pos, q⟩)).1 ∧
      StageEnd y lo L s fs pe w (fsRun lo top (stRun y L s p₁ r F ⟨pos, q⟩)).2

theorem match_of_scan (fs : Bool) (F : ℕ) (hsc : ScanClaim y lo L s pe p₁ r fs F) :
    MatchClaim y lo L s pe p₁ r fs F := by
  intro top pos q v hv hB hH hfuel
  have e1 := match_guard y lo L s pe p₁ r fs top pos q v hv hB hH
  by_cases hg : L < pos + max 1 (2 * s)
  · rw [if_pos hg] at e1
    have hnil : stRun y L s p₁ r F ⟨pos, q⟩ = [] := by
      cases F with
      | zero => rfl
      | succ F =>
        have hm := hB.le
        unfold stRun
        rw [ovRun, if_pos (by simp; omega)]
    rw [hnil]
    refine ⟨1, _, fun _ => by simp [fsRun, endTop]; omega, iterFlags_one e1, by simp [fsRun], rfl,
      hB.congr rfl (fun _ _ => rfl) (fun _ _ => rfl), hH.cut⟩
  · rw [if_neg hg] at e1
    obtain ⟨n, w, hn, h1, h2, h3⟩ := hsc top pos q { v with ctl := scanCtl fs pe } rfl
      (hB.congr rfl (fun _ _ => rfl) (fun _ _ => rfl))
      (hH.congr (fun _ _ => rfl) (fun _ _ => rfl)) (by omega) hfuel
    exact ⟨n + 1, w, fun hc => by have := hn hc; omega, iterFlags_succ e1 h1, h2, h3⟩

/-- **The stage scan**, by induction on the list-level fuel. -/
theorem scan_run (fs : Bool) (hsL : s ≤ L) (hp₁ : 0 < p₁)
    (hpe : pe = false → ∀ q, ¬(8 * p₁ ≤ q ∧ q ≤ r)) :
    ∀ F, ScanClaim y lo L s pe p₁ r fs F
  | 0 => by
    intro top pos q v hv hB hH hg hfuel
    have := hH.front
    simp only [Phi] at hfuel
    omega
  | F + 1 => by
    intro top pos q v hv hB hH hg hfuel
    have hm := hB.le
    have hfr := hH.front
    have hmatch : MatchClaim y lo L s pe p₁ r fs F :=
      match_of_scan y lo L s pe p₁ r fs F (scan_run fs hsL hp₁ hpe F)
    have hphi : Phi 8 ⟨pos, q⟩ < Phi 8 (stStep y L s p₁ r ⟨pos, q⟩) :=
      ovStep_phi_lt (by norm_num) hp₁ _
    have hphiL : Phi 8 ⟨pos, q⟩ ≤ 9 * L := by simp only [Phi]; omega
    rw [stRun_succ y L s p₁ r hm hsL F pos q hg hfr]
    -- after the shift, from the decision point with the stream at `t`
    have after_shift : ∀ (t : ℕ) (w : HVM), w.ctl = decisionCtl fs pe → Base y lo L t w →
        Heads y L s pe p₁ r pos q w → (q = 0 → pos + s < L) →
        (y[L - 1 - (pos + s + q)]? ≠ y[s + q]? ∨ pos + s + q = L) →
        ∃ n w', ((pe = true → s ≤ 8 * p₁) →
            n + 4 * endTop (fsRun lo t (stRun y L s p₁ r F (stStep y L s p₁ r ⟨pos, q⟩))).2 ≤
              32 * (Phi 8 (stStep y L s p₁ r ⟨pos, q⟩) - Phi 8 ⟨pos, q⟩) +
              100 * (9 * L - Phi 8 (stStep y L s p₁ r ⟨pos, q⟩)) + 4 * t + 3) ∧
          Phi 8 (stStep y L s p₁ r ⟨pos, q⟩) ≤ 9 * L ∧
          iterFlags n w = some w' ∧
          w'.flags = w.flags ++ (fsRun lo t (stRun y L s p₁ r F (stStep y L s p₁ r ⟨pos, q⟩))).1 ∧
          StageEnd y lo L s fs pe w' (fsRun lo t (stRun y L s p₁ r F (stStep y L s p₁ r ⟨pos, q⟩))).2 := by
      intro t w hw hBw hHw hq0 hcase
      have hst : stStep y L s p₁ r ⟨pos, q⟩ = ⟨pos + gsShift 8 p₁ r q, gsNextQ 8 p₁ r q⟩ := by
        apply stStep_shift y L s p₁ r hm hsL
        rcases hcase with h | h
        · by_cases hh : pos + s + q = L
          · exact Or.inl hh
          · exact Or.inr ⟨by omega, h⟩
        · exact Or.inl h
      obtain ⟨n1, w1, hn1, h1, h1c, h1B, h1H, h1f⟩ := shift_run y lo L s pe p₁ r fs t pos q w hw hBw
        hHw hq0 (fun hp => hpe hp q) hp₁
      rw [hst] at hphi ⊢
      have hphi' : Phi 8 ⟨pos + gsShift 8 p₁ r q, gsNextQ 8 p₁ r q⟩ ≤ 9 * L := by
        have := h1H.front; simp only [Phi]; omega
      obtain ⟨n2, w2, hn2, h2, h2f, h2e⟩ := hmatch t (pos + gsShift 8 p₁ r q) (gsNextQ 8 p₁ r q) w1 h1c
        h1B h1H (by omega)
      refine ⟨n1 + n2, w2, fun hc => by have := hn2 hc; omega, hphi', iterFlags_trans h1 h2, ?_, h2e⟩
      rw [h2f, h1f]
    by_cases hfront : pos + s + q = L
    · -- the frontier
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · subst h0; simp at hg; omega
        · have : max 1 (2 * s) = 2 * s := by omega
          omega
      have hqs : s ≤ q := by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · omega
        · have : max 1 (2 * s) = 2 * s := by omega
          omega
      obtain ⟨n1, w1, hn1, h1, h1f, h1e⟩ := front_run y lo L s pe p₁ r fs top pos q v hv hB hH hfront hq1
      have hRep : (if pos + s + q = L ∧ PrefixOK y L s pos then [L - pos] else []) =
          (if (∀ j, j < s → y[L - 1 - (pos + j)]? = y[j]?) then [L - pos] else []) := by
        by_cases hP : PrefixOK y L s pos
        · rw [if_pos ⟨hfront, hP⟩]; exact (if_pos hP).symm
        · rw [if_neg (fun h => hP h.2)]; exact (if_neg hP).symm
      have hst : stStep y L s p₁ r ⟨pos, q⟩ = ⟨pos + gsShift 8 p₁ r q, gsNextQ 8 p₁ r q⟩ :=
        stStep_shift y L s p₁ r hm hsL pos q (Or.inl hfront)
      rw [hRep, fsRun_append]
      generalize hR : (if (∀ j, j < s → y[L - 1 - (pos + j)]? = y[j]?) then [L - pos] else []) = Rep
        at h1f h1e hn1 ⊢
      cases ho : (fsRun lo top Rep).2 with
      | none =>
        rw [ho] at h1e hn1
        refine ⟨n1, w1, fun _ => ?_, h1, ?_, ?_⟩
        · show n1 + 4 * endTop (fsRun lo top Rep).2 ≤ _
          rw [ho]; simp only [endTop] at hn1 ⊢; simp only [Phi]; omega
        · dsimp only; exact h1f
        · dsimp only; rw [ho]; exact h1e
      | some t =>
        rw [ho] at h1e hn1
        obtain ⟨h1c, h1B, h1H⟩ := h1e
        obtain ⟨n2, w2, hn2, hphi', h2, h2f, h2e⟩ := after_shift t w1 h1c h1B h1H (by omega)
          (Or.inr hfront)
        refine ⟨n1 + n2, w2, fun hc => ?_, iterFlags_trans h1 h2, ?_, h2e⟩
        · have h3 := hn2 hc
          have h4 := front_phi pos q s p₁ r hqs hq1 hp₁ (fun hh => by
            cases pe with
            | false => exact absurd hh (hpe rfl q)
            | true => exact hc rfl)
          show n1 + n2 + 4 * endTop (fsRun lo t (stRun y L s p₁ r F (stStep y L s p₁ r ⟨pos, q⟩))).2 ≤ _
          rw [hst] at hphi' h3 ⊢
          simp only [endTop] at hn1
          simp only [Phi] at hphi' h3 h4 ⊢
          omega
        · rw [h2f, h1f, List.append_assoc]
    · have hlt : pos + s + q < L := by omega
      rw [if_neg (fun h => hfront h.1), List.nil_append]
      by_cases heq : y[L - 1 - (pos + s + q)]? = y[s + q]?
      · obtain ⟨w1, h1, h1c, h1B, h1H, h1f⟩ := scan_hit y lo L s pe p₁ r fs top pos q v hv hB hH hlt heq
        rw [stStep_hit y L s p₁ r hm hsL pos q hlt heq] at hphi ⊢
        obtain ⟨n2, w2, hn2, h2, h2f, h2e⟩ := scan_run fs hsL hp₁ hpe F top pos (q + 1) w1 h1c h1B h1H
          hg (by omega)
        refine ⟨3 + n2, w2, fun hc => ?_, iterFlags_trans h1 h2, ?_, h2e⟩
        · have := hn2 hc; simp only [Phi] at this ⊢; omega
        · rw [h2f, h1f]
      · have h1 := scan_miss y lo L s pe p₁ r fs top pos q v hv hB hH hlt heq
        obtain ⟨n2, w2, hn2, hphi', h2, h2f, h2e⟩ := after_shift top { v with ctl := decisionCtl fs pe }
          rfl (hB.congr rfl (fun _ _ => rfl) (fun _ _ => rfl))
          (hH.congr (fun _ _ => rfl) (fun _ _ => rfl)) (fun _ => by omega) (Or.inl heq)
        refine ⟨3 + n2, w2, fun hc => ?_, iterFlags_trans h1 h2, h2f, h2e⟩
        have := hn2 hc
        omega

/-! ### The shrink (sites 36-43): `End := nextLen s`, `Tail := len - End` -/

/-- `w'` differs from `w` at most in the positions of `a` and `b`. -/
def Moved (a b : String) (w w' : HVM) : Prop :=
  w'.word = w.word ∧ w'.flags = w.flags ∧ w'.rev = w.rev ∧ ∀ x, x ≠ a → x ≠ b → w'.pos x = w.pos x

/-- Sites 38-39: `Walk` runs up to `Cut`, `Second` twice as fast. -/
theorem shrink_walk (fs pe : Bool) (s : ℕ) :
    ∀ (d j : ℕ) (w : HVM), j + d = s → w.ctl = bctl fs (some pe) 38 (.less "Walk" "Cut") →
      w.pos "Walk" = j → w.pos "Second" = 2 * (j : ℤ) → w.pos "Cut" = s → (s : ℤ) ≤ w.len →
      ∃ w', iterFlags (2 * d + 1) w = some w' ∧ w'.ctl = bctl fs (some pe) 40 (.equal "Cut" "Origin") ∧
        w'.pos "Walk" = s ∧ w'.pos "Second" = 2 * (s : ℤ) ∧ Moved "Walk" "Second" w w'
  | 0, j, w, hjd, hw, hW, hS, hC, hl => by
    have e1 : stepFlags w = some { w with ctl := bctl fs (some pe) 40 (.equal "Cut" "Origin") } :=
      fless' (d := false) hw (by rw [hW, hC]; simp; omega) rfl
    exact ⟨_, iterFlags_one e1, rfl, by rw [hW]; simp; omega, by rw [hS]; simp; omega,
      rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | d + 1, j, w, hjd, hw, hW, hS, hC, hl => by
    have e1 : stepFlags w = some { w with ctl := bctl fs (some pe) 39 (mv [("Walk", 1), ("Second", 2)]) } :=
      fless' (d := true) hw (by rw [hW, hC]; simp; omega) rfl
    let w2 : HVM := { w with
      pos := Function.update (Function.update w.pos "Walk" (w.pos "Walk" + 1)) "Second"
        (w.pos "Second" + 2)
      ctl := bctl fs (some pe) 38 (.less "Walk" "Cut") }
    have e2 : stepFlags { w with ctl := bctl fs (some pe) 39 (mv [("Walk", 1), ("Second", 2)]) } =
        some w2 := by
      refine fmove' (ms := [⟨"Walk", 1⟩, ⟨"Second", 2⟩]) rfl ?_ rfl
      show moveSeq flagBlind w.len _ w.pos = _
      rw [moveSeq_cons_ok (by intro _; simp only [hW]; omega),
        moveSeq_cons_ok (by intro h; exact absurd (by simp [flagBlind]) h), moveSeq_nil']
      simp [Function.update]
    obtain ⟨w', h3, h3c, h3W, h3S, h3w, h3f, h3r, h3p⟩ := shrink_walk fs pe s d (j + 1) w2 (by omega) rfl
      (by simp [w2, hW]) (by simp [w2, Function.update, hS]; ring) (by simp [w2, Function.update, hC])
      (by simpa [w2, HVM.len] using hl)
    refine ⟨w', ?_, h3c, h3W, h3S, h3w, h3f, h3r, fun x h1 h2 => ?_⟩
    · rw [show 2 * (d + 1) + 1 = 1 + 1 + (2 * d + 1) by ring, iterFlags_add, iterFlags_add,
        iterFlags_one e1, Option.bind_some, iterFlags_one e2, Option.bind_some, h3]
    · rw [h3p x h1 h2]; simp [w2, Function.update, h1, h2]

/-- Sites 42-43: `End` comes down to `Second`, `Tail` goes up with it. -/
theorem shrink_end (fs pe : Bool) (nl m : ℕ) :
    ∀ (d : ℕ) (w : HVM), w.ctl = bctl fs (some pe) 42 (.less "Second" "End") →
      w.pos "Second" = nl → w.pos "End" = (nl + d : ℕ) → w.pos "Tail" = (m : ℤ) - (nl + d : ℕ) →
      w.len = m → nl + d ≤ m →
      ∃ w', iterFlags (2 * d + 1) w = some w' ∧ w'.ctl = bctl false (some pe) 3 (.less "Origin" "End") ∧
        w'.pos "End" = nl ∧ w'.pos "Tail" = (m : ℤ) - nl ∧ Moved "End" "Tail" w w'
  | 0, w, hw, hS, hE, hT, hl, hle => by
    have e1 : stepFlags w = some { w with ctl := bctl false (some pe) 3 (.less "Origin" "End") } :=
      fless' (d := false) hw (by rw [hS, hE]; simp) rfl
    exact ⟨_, iterFlags_one e1, rfl, by rw [hE]; simp, by rw [hT]; simp, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  | d + 1, w, hw, hS, hE, hT, hl, hle => by
    have e1 : stepFlags w = some { w with ctl := bctl fs (some pe) 43 (mv [("End", -1), ("Tail", 1)]) } :=
      fless' (d := true) hw (by rw [hS, hE]; simp) rfl
    let w2 : HVM := { w with
      pos := Function.update (Function.update w.pos "End" (w.pos "End" + -1)) "Tail"
        (w.pos "Tail" + 1)
      ctl := bctl fs (some pe) 42 (.less "Second" "End") }
    have e2 : stepFlags { w with ctl := bctl fs (some pe) 43 (mv [("End", -1), ("Tail", 1)]) } =
        some w2 := by
      refine fmove' (ms := [⟨"End", -1⟩, ⟨"Tail", 1⟩]) rfl ?_ rfl
      show moveSeq flagBlind w.len _ w.pos = _
      rw [moveSeq_cons_ok (by intro _; simp only [hE, hl]; omega),
        moveSeq_cons_ok (by intro _; simp [Function.update, hT, hl]; omega), moveSeq_nil']
      simp [Function.update]
    obtain ⟨w', h3, h3c, h3E, h3T, h3w, h3f, h3r, h3p⟩ := shrink_end fs pe nl m d w2 rfl
      (by simp [w2, Function.update, hS]) (by simp [w2, Function.update, hE]; omega)
      (by simp [w2, Function.update, hT]; omega) (by simpa [w2, HVM.len] using hl) (by omega)
    refine ⟨w', ?_, h3c, h3E, h3T, h3w, h3f, h3r, fun x h1 h2 => ?_⟩
    · rw [show 2 * (d + 1) + 1 = 1 + 1 + (2 * d + 1) by ring, iterFlags_add, iterFlags_add,
        iterFlags_one e1, Option.bind_some, iterFlags_one e2, Option.bind_some, h3]
    · rw [h3p x h1 h2]; simp [w2, Function.update, h1, h2]

/-- The stage head (site 3): `Origin < End`? -/
def stageCtl (fs : Bool) (pe : Option Bool) : Ctl := bctl fs pe 3 (.less "Origin" "End")

/-- **The shrink**: from the shrink start with `Cut = s` to the next stage head with
`End = nextLen s` (L1: `nextLen s < L`). -/
theorem shrink_run (fs pe : Bool) (L s t : ℕ) (w : HVM) (hw : w.ctl = shrinkCtl fs pe)
    (hB : Base y lo L t w) (hC : w.pos "Cut" = s) (hnl : nextLen s < L) :
    ∃ n w', n ≤ 2 * s + 2 * L + 6 ∧ iterFlags n w = some w' ∧ w'.ctl = stageCtl false (some pe) ∧
      Base y lo (nextLen s) t w' ∧ w'.flags = w.flags := by
  have hm := hB.le
  have hlen := hB.len
  have hsL : 2 * s ≤ L + 1 := by unfold nextLen at hnl; omega
  let w1 : HVM := { w with
    pos := Function.update w.pos "Second" (w.pos "Origin")
    rev := Function.update w.rev "Second" (w.rev "Origin")
    ctl := bctl fs (some pe) 37 (.copy "Walk" "Origin") }
  have e1 : stepFlags w = some w1 := fcopy' hw rfl
  let w2 : HVM := { w1 with
    pos := Function.update w1.pos "Walk" (w1.pos "Origin")
    rev := Function.update w1.rev "Walk" (w1.rev "Origin")
    ctl := bctl fs (some pe) 38 (.less "Walk" "Cut") }
  have e2 : stepFlags w1 = some w2 := fcopy' rfl rfl
  obtain ⟨w3, h3, h3c, h3W, h3S, h3w, h3f, h3r, h3p⟩ := shrink_walk fs pe s s 0 w2 (by omega) rfl
    (by simp [w2, w1, Function.update, hB.origin]) (by simp [w2, w1, Function.update, hB.origin])
    (by simp [w2, w1, Function.update, hC]) (by simp [w2, w1, HVM.len, hB.word]; omega)
  have hO3 : w3.pos "Origin" = 0 := by
    rw [h3p _ (by decide) (by decide)]; simp [w2, w1, Function.update, hB.origin]
  have hC3 : w3.pos "Cut" = s := by
    rw [h3p _ (by decide) (by decide)]; simp [w2, w1, Function.update, hC]
  -- site 40: `Cut = Origin`?, and `Second - 1` unless `s = 0`
  obtain ⟨w4, h4, h4c, h4S, h4m⟩ : ∃ w4, iterFlags (if s = 0 then 1 else 2) w3 = some w4 ∧
      w4.ctl = bctl fs (some pe) 42 (.less "Second" "End") ∧ w4.pos "Second" = (nextLen s : ℤ) ∧
      Moved "Second" "Second" w3 w4 := by
    by_cases hs0 : s = 0
    · have e4 : stepFlags w3 = some { w3 with ctl := bctl fs (some pe) 42 (.less "Second" "End") } :=
        fequal' (d := true) h3c (by rw [hO3, hC3, hs0]; simp) rfl
      refine ⟨{ w3 with ctl := bctl fs (some pe) 42 (.less "Second" "End") },
        by rw [if_pos hs0]; exact iterFlags_one e4, rfl, ?_, rfl, rfl, rfl, fun _ _ _ => rfl⟩
      simp only [h3S, hs0, nextLen]; simp
    · have e4 : stepFlags w3 = some { w3 with ctl := bctl fs (some pe) 41 (mv [("Second", -1)]) } :=
        fequal' (d := false) h3c (by rw [hO3, hC3]; simp; omega) rfl
      have e5 : stepFlags { w3 with ctl := bctl fs (some pe) 41 (mv [("Second", -1)]) } =
          some { w3 with
            pos := Function.update w3.pos "Second" (w3.pos "Second" + -1)
            ctl := bctl fs (some pe) 42 (.less "Second" "End") } := by
        refine fmove' (ms := [⟨"Second", -1⟩]) rfl ?_ rfl
        show moveSeq flagBlind w3.len _ w3.pos = _
        rw [moveSeq_cons_ok (by intro h; exact absurd (by simp [flagBlind]) h), moveSeq_nil']
      refine ⟨{ w3 with
            pos := Function.update w3.pos "Second" (w3.pos "Second" + -1)
            ctl := bctl fs (some pe) 42 (.less "Second" "End") }, ?_, rfl, ?_, rfl, rfl, rfl,
        fun x h1 _ => by simp [Function.update, h1]⟩
      · rw [if_neg hs0]; simp only [iterFlags, e4, Option.bind_some, e5]
      · simp only [Function.update_self, h3S, nextLen]; omega
  have hE4 : w4.pos "End" = L := by
    rw [h4m.2.2.2 _ (by decide) (by decide), h3p _ (by decide) (by decide)]
    simp [w2, w1, Function.update, hB.end_]
  have hT4 : w4.pos "Tail" = (y.length : ℤ) - L := by
    rw [h4m.2.2.2 _ (by decide) (by decide), h3p _ (by decide) (by decide)]
    simp [w2, w1, Function.update, hB.tail]
  have hl4 : w4.len = y.length := by
    simp only [HVM.len, h4m.1, h3w]; simp [w2, w1, hB.word]
  obtain ⟨w5, h5, h5c, h5E, h5T, h5w, h5f, h5r, h5p⟩ := shrink_end fs pe (nextLen s) y.length
    (L - nextLen s) w4 h4c h4S (by rw [hE4]; push_cast; omega) (by rw [hT4]; push_cast; omega)
    hl4 (by omega)
  refine ⟨_, _, by split_ifs <;> omega, iterFlags_trans (iterFlags_trans (iterFlags_trans
    (iterFlags_trans (iterFlags_one e1) (iterFlags_one e2)) h3) h4) h5, h5c, ?_, ?_⟩
  · -- the persistent heads
    have hpos : ∀ x, x ≠ "End" → x ≠ "Tail" → x ≠ "Walk" → x ≠ "Second" → w5.pos x = w.pos x :=
      fun x a b c d => by
        rw [h5p x a b, h4m.2.2.2 x d d, h3p x c d]; simp [w2, w1, Function.update, c, d]
    have hrev : ∀ x, x ≠ "Walk" → x ≠ "Second" → w5.rev x = w.rev x := fun x c d => by
      rw [h5r, h4m.2.2.1, h3r]; simp [w2, w1, Function.update, c, d]
    exact ⟨by rw [h5w, h4m.1, h3w]; simp [w2, w1, hB.word],
      (hpos _ (by decide) (by decide) (by decide) (by decide)).trans hB.origin,
      (hrev _ (by decide) (by decide)).trans hB.rOrigin, h5E, h5T,
      (hrev _ (by decide) (by decide)).trans hB.rTail,
      (hpos _ (by decide) (by decide) (by decide) (by decide)).trans hB.oend,
      (hrev _ (by decide) (by decide)).trans hB.rOend,
      (hpos _ (by decide) (by decide) (by decide) (by decide)).trans hB.lower,
      (hpos _ (by decide) (by decide) (by decide) (by decide)).trans hB.cursor, by omega⟩
  · rw [h5f, h4m.2.1, h3f]

/-! ### The stage start (sites 3-17) -/

/-- `w'` differs from `w` at most in the positions of `hs`. -/
def MovedIn (hs : List String) (w w' : HVM) : Prop :=
  w'.word = w.word ∧ w'.flags = w.flags ∧ w'.rev = w.rev ∧ ∀ x, x ∉ hs → w'.pos x = w.pos x

/-- Sites 14-15: `Walk` runs up to `Cut`, `B` with it, `Second` back twice as fast. -/
theorem offset_run (fs pe : Bool) (s : ℕ) (b0 m : ℤ) :
    ∀ (d j : ℕ) (w : HVM), j + d = s → w.ctl = bctl fs (some pe) 14 (.less "Walk" "Cut") →
      w.pos "Walk" = j → w.pos "B" = b0 + j → w.pos "Second" = m - 2 * (j : ℤ) →
      w.pos "Cut" = s → (s : ℤ) ≤ w.len → 0 ≤ b0 → b0 + s ≤ w.len →
      ∃ w', iterFlags (2 * d + 1) w = some w' ∧ w'.ctl = bctl fs (some pe) 16 (.equal "Cut" "Origin") ∧
        w'.pos "Walk" = s ∧ w'.pos "B" = b0 + s ∧ w'.pos "Second" = m - 2 * (s : ℤ) ∧
        MovedIn ["Walk", "B", "Second"] w w'
  | 0, j, w, hjd, hw, hW, hBp, hS, hC, hl, hb0, hbl => by
    have e1 : stepFlags w = some { w with ctl := bctl fs (some pe) 16 (.equal "Cut" "Origin") } :=
      fless' (d := false) hw (by rw [hW, hC]; simp; omega) rfl
    exact ⟨_, iterFlags_one e1, rfl, by rw [hW]; simp; omega, by rw [hBp]; simp; omega,
      by rw [hS]; simp; omega, rfl, rfl, rfl, fun _ _ => rfl⟩
  | d + 1, j, w, hjd, hw, hW, hBp, hS, hC, hl, hb0, hbl => by
    have e1 : stepFlags w = some { w with
        ctl := bctl fs (some pe) 15 (mv [("Walk", 1), ("B", 1), ("Second", -2)]) } :=
      fless' (d := true) hw (by rw [hW, hC]; simp; omega) rfl
    let w2 : HVM := { w with
      pos := Function.update (Function.update (Function.update w.pos "Walk" (w.pos "Walk" + 1)) "B"
        (w.pos "B" + 1)) "Second" (w.pos "Second" + -2)
      ctl := bctl fs (some pe) 14 (.less "Walk" "Cut") }
    have e2 : stepFlags { w with
        ctl := bctl fs (some pe) 15 (mv [("Walk", 1), ("B", 1), ("Second", -2)]) } = some w2 := by
      refine fmove' (ms := [⟨"Walk", 1⟩, ⟨"B", 1⟩, ⟨"Second", -2⟩]) rfl ?_ rfl
      show moveSeq flagBlind w.len _ w.pos = _
      rw [moveSeq_cons_ok (by intro _; simp only [hW]; omega),
        moveSeq_cons_ok (by intro _; simp [Function.update, hBp]; omega),
        moveSeq_cons_ok (by intro h; exact absurd (by simp [flagBlind]) h), moveSeq_nil']
      simp [Function.update]
    obtain ⟨w', h3, h3c, h3W, h3B, h3S, h3w, h3f, h3r, h3p⟩ := offset_run fs pe s b0 m d (j + 1) w2
      (by omega) rfl (by simp [w2, Function.update, hW]) (by simp [w2, Function.update, hBp]; ring)
      (by simp [w2, Function.update, hS]; ring) (by simp [w2, Function.update, hC])
      (by simpa [w2, HVM.len] using hl) hb0 (by simpa [w2, HVM.len] using hbl)
    refine ⟨w', ?_, h3c, h3W, h3B, h3S, h3w, h3f, h3r, fun x hx => ?_⟩
    · rw [show 2 * (d + 1) + 1 = 1 + 1 + (2 * d + 1) by ring, iterFlags_add, iterFlags_add,
        iterFlags_one e1, Option.bind_some, iterFlags_one e2, Option.bind_some, h3]
    · rw [h3p x hx]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [w2, Function.update, hx.1, hx.2.1, hx.2.2]

/-- The stage decomposition the program runs: `dec (y.take L)`, with the effective period of
`StageMatcher` when there is none (`p₁ = |v| + 1`, `r = 0`, so `gsShift` is the reset branch). -/
def bdec (dec : List (Fin 2) → ℕ × ℕ × ℕ) (L : ℕ) : ℕ × ℕ × ℕ :=
  if (dec (y.take L)).2.1 = 0 then ((dec (y.take L)).1, L - (dec (y.take L)).1 + 1, 0)
  else dec (y.take L)

/-- Sites 10-17: `A := Cut`, `B := P`, `Second := OriginalEnd`, the offset loop, and the last
`Second - 1` when `s = 0`. -/
theorem setup_tail (fs pe : Bool) (L top s p₁ r st : ℕ) (w : HVM)
    (hw : w.ctl = bctl fs (some pe) 10 (.copy "A" "Cut")) (hB : Base y lo L top w)
    (hC : w.pos "Cut" = s) (hrC : w.rev "Cut" = false)
    (hper : pe = true → w.pos "First" = (s : ℤ) + p₁ ∧ w.pos "KFirst" = (s : ℤ) + 8 * p₁ ∧
      w.pos "Reach" = (s : ℤ) + r)
    (hP : w.pos "P" = (y.length : ℤ) - L + st) (hrP : w.rev "P" = true)
    (hKP : w.pos "KP" = (L : ℤ) - st) (hst : st + s ≤ L) :
    ∃ n w', n ≤ 2 * s + 7 ∧ iterFlags n w = some w' ∧ w'.ctl = matchCtl fs pe ∧ Base y lo L top w' ∧
      Heads y L s pe p₁ r st 0 w' ∧ w'.flags = w.flags := by
  have hm := hB.le
  have hlen := hB.len
  let w1 : HVM := { w with
    pos := Function.update w.pos "A" (w.pos "Cut")
    rev := Function.update w.rev "A" (w.rev "Cut")
    ctl := bctl fs (some pe) 11 (.copy "B" "P") }
  have e1 : stepFlags w = some w1 := fcopy' hw rfl
  let w2 : HVM := { w1 with
    pos := Function.update w1.pos "B" (w1.pos "P")
    rev := Function.update w1.rev "B" (w1.rev "P")
    ctl := bctl fs (some pe) 12 (.copy "Second" "OriginalEnd") }
  have e2 : stepFlags w1 = some w2 := fcopy' rfl rfl
  let w3 : HVM := { w2 with
    pos := Function.update w2.pos "Second" (w2.pos "OriginalEnd")
    rev := Function.update w2.rev "Second" (w2.rev "OriginalEnd")
    ctl := bctl fs (some pe) 13 (.copy "Walk" "Origin") }
  have e3 : stepFlags w2 = some w3 := fcopy' rfl rfl
  let w4 : HVM := { w3 with
    pos := Function.update w3.pos "Walk" (w3.pos "Origin")
    rev := Function.update w3.rev "Walk" (w3.rev "Origin")
    ctl := bctl fs (some pe) 14 (.less "Walk" "Cut") }
  have e4 : stepFlags w3 = some w4 := fcopy' rfl rfl
  have h4 : iterFlags 4 w = some w4 := by simp only [iterFlags, e1, Option.bind_some, e2, e3, e4]
  obtain ⟨w5, h5, h5c, h5W, h5B, h5S, h5w, h5f, h5r, h5p⟩ := offset_run fs pe s
    ((y.length : ℤ) - L + st) y.length s 0 w4 (by omega) rfl
    (by simp [w4, w3, w2, w1, Function.update, hB.origin])
    (by simp [w4, w3, w2, w1, Function.update, hP])
    (by simp [w4, w3, w2, w1, Function.update, hB.oend])
    (by simp [w4, w3, w2, w1, Function.update, hC])
    (by simp [w4, w3, w2, w1, HVM.len, hB.word]; omega) (by omega)
    (by simp [w4, w3, w2, w1, HVM.len, hB.word]; omega)
  have hO5 : w5.pos "Origin" = 0 := by
    rw [h5p _ (by decide)]; simp [w4, w3, w2, w1, Function.update, hB.origin]
  have hC5 : w5.pos "Cut" = s := by
    rw [h5p _ (by decide)]; simp [w4, w3, w2, w1, Function.update, hC]
  -- the last step(s): `Cut = Origin`?, and `Second - 1` when `s = 0`
  obtain ⟨w6, h6, h6c, h6S, h6m⟩ : ∃ w6, iterFlags (if s = 0 then 2 else 1) w5 = some w6 ∧
      w6.ctl = matchCtl fs pe ∧ w6.pos "Second" = (y.length : ℤ) - max 1 (2 * s) ∧
      MovedIn ["Second"] w5 w6 := by
    by_cases hs0 : s = 0
    · have e6 : stepFlags w5 = some { w5 with ctl := bctl fs (some pe) 17 (mv [("Second", -1)]) } :=
        fequal' (d := true) h5c (by rw [hO5, hC5, hs0]; simp) rfl
      have e7 : stepFlags { w5 with ctl := bctl fs (some pe) 17 (mv [("Second", -1)]) } =
          some { w5 with
            pos := Function.update w5.pos "Second" (w5.pos "Second" + -1)
            ctl := matchCtl fs pe } := by
        refine fmove' (ms := [⟨"Second", -1⟩]) rfl ?_ rfl
        show moveSeq flagBlind w5.len _ w5.pos = _
        rw [moveSeq_cons_ok (by intro h; exact absurd (by simp [flagBlind]) h), moveSeq_nil']
      refine ⟨{ w5 with
            pos := Function.update w5.pos "Second" (w5.pos "Second" + -1)
            ctl := matchCtl fs pe }, ?_, rfl, ?_, rfl, rfl, rfl, fun x hx => ?_⟩
      · rw [if_pos hs0]; simp only [iterFlags, e6, Option.bind_some, e7]
      · simp only [Function.update_self, h5S, hs0]; simp; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; simp [Function.update, hx]
    · have e6 : stepFlags w5 = some { w5 with ctl := matchCtl fs pe } :=
        fequal' (d := false) h5c (by rw [hO5, hC5]; simp; omega) rfl
      refine ⟨{ w5 with ctl := matchCtl fs pe }, ?_, rfl, ?_, rfl, rfl, rfl, fun _ _ => rfl⟩
      · rw [if_neg hs0]; exact iterFlags_one e6
      · rw [h5S]; congr 1; omega
  have hpos : ∀ x, x ∉ ["Walk", "B", "Second", "A"] → w6.pos x = w.pos x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [h6m.2.2.2 x (by simp [hx.2.2.1]), h5p x (by simp [hx.1, hx.2.1, hx.2.2.1])]
    simp [w4, w3, w2, w1, Function.update, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  have hrev : ∀ x, x ∉ ["Walk", "B", "Second", "A"] → w6.rev x = w.rev x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [h6m.2.2.1, h5r]
    simp [w4, w3, w2, w1, Function.update, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  have hrA : w6.rev "A" = false := by
    rw [h6m.2.2.1, h5r]; simp [w4, w3, w2, w1, Function.update, hrC]
  have hrB : w6.rev "B" = true := by
    rw [h6m.2.2.1, h5r]; simp [w4, w3, w2, w1, Function.update, hrP]
  have hA6 : w6.pos "A" = s := by
    rw [h6m.2.2.2 _ (by decide), h5p _ (by decide)]; simp [w4, w3, w2, w1, Function.update, hC]
  have hB6 : w6.pos "B" = (y.length : ℤ) - L + st + s := by
    rw [h6m.2.2.2 _ (by decide), h5B]
  refine ⟨4 + (2 * s + 1) + (if s = 0 then 2 else 1), w6, by split_ifs <;> omega, ?_, h6c, ?_, ?_, ?_⟩
  · exact iterFlags_trans (iterFlags_trans h4 h5) h6
  · refine hB.congr (by rw [h6m.1, h5w]) (fun x hx => hpos x ?_) (fun x hx => hrev x ?_) <;>
    · simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact {
      cut := (hpos _ (by decide)).trans hC
      rCut := (hrev _ (by decide)).trans hrC
      per := fun h => by
        obtain ⟨h1, h2, h3⟩ := hper h
        exact ⟨(hpos _ (by decide)).trans h1, (hpos _ (by decide)).trans h2, (hpos _ (by decide)).trans h3⟩
      second := h6S
      p := (hpos _ (by decide)).trans hP
      rP := (hrev _ (by decide)).trans hrP
      kp := (hpos _ (by decide)).trans hKP
      a := by rw [hA6]; simp
      rA := hrA
      b := by rw [hB6]; ring
      rB := hrB
      front := by omega }
  · rw [h6m.2.1, h5f]

/-- The call of `Decompose` (site 6). -/
def decCallCtl (fs : Bool) (pe0 : Option Bool) : Ctl :=
  .pending [fc4, .borderController 8 true "TextOrigin" fs pe0 6, .decompose 8 1] (.copy "Cut" "Origin")

theorem bdec_fst (dec : List (Fin 2) → ℕ × ℕ × ℕ) (L : ℕ) :
    (bdec y dec L).1 = (dec (y.take L)).1 := by
  unfold bdec; split <;> rfl

theorem bdec_of_ne (dec : List (Fin 2) → ℕ × ℕ × ℕ) (L : ℕ) (h : (dec (y.take L)).2.1 ≠ 0) :
    bdec y dec L = dec (y.take L) := by
  unfold bdec; rw [if_neg h]

theorem bdec_of_eq (dec : List (Fin 2) → ℕ × ℕ × ℕ) (L : ℕ) (h : (dec (y.take L)).2.1 = 0) :
    bdec y dec L = ((dec (y.take L)).1, L - (dec (y.take L)).1 + 1, 0) := by
  unfold bdec; rw [if_pos h]

/-- **The stage start**: from the stage head with `1 ≤ L`, `lo ≤ L` to the match head at
`⟨start, 0⟩` (`start = 1` in the first stage). -/
theorem stage_start {dec : List (Fin 2) → ℕ × ℕ × ℕ} (hD : DecomposeContract 8 dec) (fs : Bool)
    (pe0 : Option Bool) (L top : ℕ) (v : HVM) (hv : v.ctl = stageCtl fs pe0)
    (hB : Base y lo L top v) (hL1 : 1 ≤ L) (hlo : lo ≤ L)
    (hstart : (if fs then 1 else 0) + (dec (y.take L)).1 ≤ L) :
    ∃ n w, (∀ cD, DecomposeCost 8 cD → n ≤ cD * L + cD + 2 * (dec (y.take L)).1 + 12) ∧
      iterFlags n v = some w ∧ w.ctl = matchCtl fs (decide ((dec (y.take L)).2.1 ≠ 0)) ∧
      Base y lo L top w ∧
      Heads y L (bdec y dec L).1 (decide ((dec (y.take L)).2.1 ≠ 0)) (bdec y dec L).2.1
        (bdec y dec L).2.2 (if fs then 1 else 0) 0 w ∧ w.flags = v.flags := by
  have hm := hB.le
  have hlen := hB.len
  have e1 : stepFlags v = some { v with ctl := bctl fs pe0 4 (.less "End" "Lower") } :=
    fless' (d := true) hv (by rw [hB.origin, hB.end_]; simp; omega) rfl
  let v2 : HVM := { v with ctl := decCallCtl fs pe0 }
  have e2 : stepFlags { v with ctl := bctl fs pe0 4 (.less "End" "Lower") } = some v2 :=
    fless' (d := false) rfl
      (by show decide (v.pos "End" < v.pos "Lower") = false; rw [hB.end_, hB.lower]; simp; omega) rfl
  -- the decomposition, inside the two callers
  let vc : HVM := { v with ctl := Ctl.ofOutcome (next [.decompose 8 0] none) }
  obtain ⟨n1, π, r', hn1, hrun, hdh, hπ, hrC, hr'⟩ := decompose_flags hD vc L rfl hB.origin hB.end_ hL1
    (by simp [vc, HVM.len, hB.word]; omega) hB.rOrigin
  have hvw : vc.word = y := hB.word
  let pe : Bool := decide ((dec (y.take L)).2.1 ≠ 0)
  let bc6 : Frame := .borderController 8 true "TextOrigin" fs pe0 6
  have hl := lift2_run fc4 bc6 (nonEmpty_ofOutcome [.decompose 8 0] none) hrun
  have hl0 : liftVM fc4 (liftVM bc6 vc) = v2 := rfl
  rw [hl0] at hl
  let w3 : HVM := { v with ctl := bctl fs (some pe) 7 (.copy "P" "Tail"), pos := π, rev := r' }
  have hl' : iterFlags n1 v2 = some w3 := by
    rw [hl]; simp only [liftVM, w3, pe, vc, hvw.symm]; rfl
  rw [hvw] at hdh
  -- sites 7-9
  have hπT : π "Tail" = (y.length : ℤ) - L := by rw [hπ _ (by decide)]; exact hB.tail
  have hπE : π "End" = L := by rw [hπ _ (by decide)]; exact hB.end_
  have hrT : r' "Tail" = true := by rw [hr' _ (by decide)]; exact hB.rTail
  let w4 : HVM := { w3 with
    pos := Function.update w3.pos "P" (w3.pos "Tail")
    rev := Function.update w3.rev "P" (w3.rev "Tail")
    ctl := bctl fs (some pe) 8 (.copy "KP" "End") }
  have e4 : stepFlags w3 = some w4 := fcopy' rfl rfl
  have hBase : ∀ w : HVM, w.word = v.word → (∀ x, x ∉ decT → x ≠ "P" → x ≠ "KP" → w.pos x = v.pos x) →
      (∀ x, x ∉ decT → x ≠ "P" → w.rev x = v.rev x) → Base y lo L top w := fun w hw hp hr =>
    hB.congr hw (fun x hx => hp x (by
        simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      (fun x hx => hr x (by
        simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [baseHeads, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  have hs : (bdec y dec L).1 = (dec (y.take L)).1 := bdec_fst y dec L
  have hper : pe = true → π "First" = ((bdec y dec L).1 : ℤ) + (bdec y dec L).2.1 ∧
      π "KFirst" = ((bdec y dec L).1 : ℤ) + 8 * (bdec y dec L).2.1 ∧
      π "Reach" = ((bdec y dec L).1 : ℤ) + (bdec y dec L).2.2 := by
    intro hpe
    have hne : (dec (y.take L)).2.1 ≠ 0 := by simpa [pe] using hpe
    obtain ⟨h1, h2, h3⟩ := hdh.2 hne
    rw [bdec_of_ne y dec L hne, h1, h2, h3]
    push_cast; exact ⟨rfl, rfl, rfl⟩
  have hcut : π "Cut" = ((bdec y dec L).1 : ℤ) := by rw [hdh.1, hs]
  cases fs with
  | false =>
    let w5 : HVM := { w4 with
      pos := Function.update w4.pos "KP" (w4.pos "End")
      rev := Function.update w4.rev "KP" (w4.rev "End")
      ctl := bctl false (some pe) 10 (.copy "A" "Cut") }
    have e5 : stepFlags w4 = some w5 := fcopy' rfl rfl
    obtain ⟨n6, w6, hn6, h6, h6c, h6B, h6H, h6f⟩ := setup_tail y lo false pe L top (bdec y dec L).1
      (bdec y dec L).2.1 (bdec y dec L).2.2 0 w5 rfl
      (hBase w5 rfl (fun x hx h1 h2 => by simp [w5, w4, w3, vc, Function.update, h1, h2, hπ x hx])
        (fun x hx h1 => by
          have hK : x ≠ "KP" := fun e => hx (by rw [e]; decide)
          simp [w5, w4, w3, vc, Function.update, h1, hK, hr' x hx]))
      (by simp [w5, w4, w3, Function.update, hcut]) (by simp [w5, w4, w3, Function.update, hrC])
      (fun h => by simpa [w5, w4, w3, Function.update] using hper h)
      (by simp [w5, w4, w3, Function.update, hπT]) (by simp [w5, w4, w3, Function.update, hrT])
      (by simp [w5, w4, w3, Function.update, hπE]) (by rw [hs]; simpa using hstart)
    refine ⟨2 + n1 + 1 + 1 + n6, w6, fun cD hc => by have := hn1 cD hc; rw [hs] at hn6; omega, ?_, h6c,
      h6B, h6H, ?_⟩
    · have h2 : iterFlags 2 v = some v2 := by simp only [iterFlags, e1, Option.bind_some, e2]
      exact iterFlags_trans (iterFlags_trans (iterFlags_trans (iterFlags_trans h2 hl')
        (iterFlags_one e4)) (iterFlags_one e5)) h6
    · rw [h6f]
  | true =>
    let w5 : HVM := { w4 with
      pos := Function.update w4.pos "KP" (w4.pos "End")
      rev := Function.update w4.rev "KP" (w4.rev "End")
      ctl := bctl true (some pe) 9 (mv [("P", 1), ("KP", -1)]) }
    have e5 : stepFlags w4 = some w5 := fcopy' rfl rfl
    let w6 : HVM := { w5 with
      pos := Function.update (Function.update w5.pos "P" (w5.pos "P" + 1)) "KP" (w5.pos "KP" + -1)
      ctl := bctl true (some pe) 10 (.copy "A" "Cut") }
    have e6 : stepFlags w5 = some w6 := by
      refine fmove' (ms := [⟨"P", 1⟩, ⟨"KP", -1⟩]) rfl ?_ rfl
      show moveSeq flagBlind w5.len _ w5.pos = _
      rw [moveSeq_cons_ok (by intro _; simp [w5, w4, w3, Function.update, hπT, HVM.len, hB.word]; omega),
        moveSeq_cons_ok (by intro h; exact absurd (by simp [flagBlind]) h), moveSeq_nil']
      simp [Function.update]
    obtain ⟨n7, w7, hn7, h7, h7c, h7B, h7H, h7f⟩ := setup_tail y lo true pe L top (bdec y dec L).1
      (bdec y dec L).2.1 (bdec y dec L).2.2 1 w6 rfl
      (hBase w6 rfl (fun x hx h1 h2 => by simp [w6, w5, w4, w3, vc, Function.update, h1, h2, hπ x hx])
        (fun x hx h1 => by
          have hK : x ≠ "KP" := fun e => hx (by rw [e]; decide)
          simp [w6, w5, w4, w3, vc, Function.update, h1, hK, hr' x hx]))
      (by simp [w6, w5, w4, w3, Function.update, hcut]) (by simp [w6, w5, w4, w3, Function.update, hrC])
      (fun h => by simpa [w6, w5, w4, w3, Function.update] using hper h)
      (by simp [w6, w5, w4, w3, Function.update, hπT]; try ring)
      (by simp [w6, w5, w4, w3, Function.update, hrT])
      (by simp [w6, w5, w4, w3, Function.update, hπE]; try ring) (by rw [hs]; simpa using hstart)
    refine ⟨2 + n1 + 1 + 1 + 1 + n7, w7, fun cD hc => by have := hn1 cD hc; rw [hs] at hn7; omega, ?_,
      h7c, h7B, h7H, ?_⟩
    · have h2 : iterFlags 2 v = some v2 := by simp only [iterFlags, e1, Option.bind_some, e2]
      exact iterFlags_trans (iterFlags_trans (iterFlags_trans (iterFlags_trans (iterFlags_trans h2 hl')
        (iterFlags_one e4)) (iterFlags_one e5)) (iterFlags_one e6)) h7
    · rw [h7f]

/-- A call of `FinishFlags` by the border controller at `site`. -/
def ffCallCtl (fs : Bool) (pe0 : Option Bool) (site : ℕ) : Ctl :=
  .pending [fc4, .borderController 8 true "TextOrigin" fs pe0 site, .finishFlags 1] (.less "Cursor" "Lower")

/-- A `FinishFlags` call inside the border controller (sites 5, 30, 44), when the controller
returns right after it. -/
theorem finish_call (fs : Bool) (pe0 : Option Bool) (site t : ℕ) (w : HVM)
    (hw : w.ctl = ffCallCtl fs pe0 site)
    (hret : liftCtl fc4 (liftCtl (.borderController 8 true "TextOrigin" fs pe0 site) (.returned none)) =
      .returned none)
    (hC : w.pos "Cursor" = (t : ℤ) - 1) (hL : w.pos "Lower" = lo) (hO : w.pos "Origin" = 0) :
    ∃ n w', n ≤ 4 * t + 1 ∧ iterFlags n w = some w' ∧ w'.flagsDone ∧
      w'.flags = w.flags ++ BorderJobHead.finishBits lo t := by
  let vf : HVM := { w with ctl := ffHead }
  have hf := finish_run lo t vf rfl hC hL hO
  let bc : Frame := .borderController 8 true "TextOrigin" fs pe0 site
  have hl := lift2_run fc4 bc (by simp [vf, ffHead, NonEmptyCtl]) hf
  have hl0 : liftVM fc4 (liftVM bc vf) = w := by
    simp only [liftVM, vf]; exact hvm_ctl_eta w _ (hw.trans rfl)
  rw [hl0] at hl
  refine ⟨_, _, by omega, hl, ⟨none, ?_⟩, rfl⟩
  show liftCtl fc4 (liftCtl bc (.returned none)) = _
  exact hret

/-- **A stage that does not run** (`End = 0` or `End < Lower`): `FinishFlags`, and done. -/
theorem stage_exit (fs : Bool) (pe0 : Option Bool) (L top : ℕ) (v : HVM)
    (hv : v.ctl = stageCtl fs pe0) (hB : Base y lo L top v) (hx : L = 0 ∨ L < lo) :
    ∃ n w, n ≤ 4 * top + 3 ∧ iterFlags n v = some w ∧ w.flagsDone ∧
      w.flags = v.flags ++ BorderJobHead.finishBits lo top := by
  by_cases hL0 : L = 0
  · have e1 : stepFlags v = some { v with ctl := ffCallCtl fs pe0 44 } :=
      fless' (d := false) hv (by rw [hB.origin, hB.end_, hL0]; simp) rfl
    obtain ⟨n, w, hn, h1, h2, h3⟩ := finish_call lo fs pe0 44 top { v with ctl := ffCallCtl fs pe0 44 }
      rfl rfl hB.cursor hB.lower hB.origin
    exact ⟨n + 1, w, by omega, iterFlags_succ e1 h1, h2, h3⟩
  · have hlo : L < lo := by omega
    have e1 : stepFlags v = some { v with ctl := bctl fs pe0 4 (.less "End" "Lower") } :=
      fless' (d := true) hv (by rw [hB.origin, hB.end_]; simp; omega) rfl
    have e2 : stepFlags { v with ctl := bctl fs pe0 4 (.less "End" "Lower") } =
        some { v with ctl := ffCallCtl fs pe0 5 } :=
      fless' (d := true) rfl
        (by show decide (v.pos "End" < v.pos "Lower") = true; rw [hB.end_, hB.lower]; simp; omega) rfl
    obtain ⟨n, w, hn, h1, h2, h3⟩ := finish_call lo fs pe0 5 top { v with ctl := ffCallCtl fs pe0 5 }
      rfl rfl hB.cursor hB.lower hB.origin
    exact ⟨n + 1 + 1, w, by omega, iterFlags_succ e1 (iterFlags_succ e2 h1), h2, h3⟩

/-- The hypotheses of the step bound: `cut_short` and `cut_charge` of `BorderJob.StageOK` for the
program's decomposition, and a linear cost of `Decompose` on the matcher VM. -/
structure CostHyp (dec : List (Fin 2) → ℕ × ℕ × ℕ) (cD : ℕ) : Prop where
  short : ∀ L, 1 ≤ L → L ≤ y.length → 7 * (dec (y.take L)).1 < L
  charge : ∀ L, 1 ≤ L → L ≤ y.length → (dec (y.take L)).2.1 ≠ 0 →
    (dec (y.take L)).1 ≤ 8 * (dec (y.take L)).2.1
  decCost : DecomposeCost 8 cD

/-- **The stage loop** (`BorderJobHead.headJob`), by induction on its fuel. L1 (`nextLen s < L`)
is what makes the stages shrink; under `CostHyp` the steps are linear in `L` and `top`. -/
theorem stages_run {dec : List (Fin 2) → ℕ × ℕ × ℕ} (hD : DecomposeContract 8 dec)
    (hL1 : ∀ L, 1 ≤ L → L ≤ y.length → nextLen (dec (y.take L)).1 < L) :
    ∀ (fuel : ℕ) (fs : Bool) (pe0 : Option Bool) (L top : ℕ) (v : HVM), v.ctl = stageCtl fs pe0 →
      Base y lo L top v → L < fuel →
      ∃ n w, (∀ cD, CostHyp y dec cD → n ≤ (3 * cD + 3000) * L + 4 * top + 5) ∧
        iterFlags n v = some w ∧ w.flagsDone ∧
        w.flags = v.flags ++ BorderJobHead.flagStream lo top
          (BorderJobHead.headJob y (bdec y dec) 8 lo fuel (if fs then 1 else 0) L)
  | 0, _, _, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, fs, pe0, L, top, v, hv, hB, hfuel => by
    have hm := hB.le
    by_cases hx : L = 0 ∨ L < lo
    · obtain ⟨n, w, hn, h1, h2, h3⟩ := stage_exit y lo fs pe0 L top v hv hB hx
      refine ⟨n, w, fun cD _ => by
        have : 0 ≤ (3 * cD + 3000) * L := Nat.zero_le _
        omega, h1, h2, ?_⟩
      rw [h3, BorderJobHead.headJob]
      rcases hx with hx | hx
      · rw [if_pos hx]; rfl
      · by_cases h0 : L = 0
        · rw [if_pos h0]; rfl
        · rw [if_neg h0, if_pos hx]; rfl
    · have hL1' : 1 ≤ L := by omega
      have hlo : lo ≤ L := by omega
      have hnl := hL1 L hL1' hm
      have hs := bdec_fst y dec L
      have hsL : (bdec y dec L).1 ≤ L := by rw [hs]; unfold nextLen at hnl; omega
      have hstart : (if fs then 1 else 0) + (dec (y.take L)).1 ≤ L := by
        unfold nextLen at hnl; split <;> omega
      obtain ⟨n1, w1, hn1, h1, h1c, h1B, h1H, h1f⟩ :=
        stage_start y lo hD fs pe0 L top v hv hB hL1' hlo hstart
      set pe := decide ((dec (y.take L)).2.1 ≠ 0) with hpe
      have hp₁ : 0 < (bdec y dec L).2.1 := by
        unfold bdec; split
        · simp
        · rename_i h; exact Nat.pos_of_ne_zero h
      have hpe' : pe = false → ∀ q, ¬(8 * (bdec y dec L).2.1 ≤ q ∧ q ≤ (bdec y dec L).2.2) := by
        intro h q hq
        have h0 : (dec (y.take L)).2.1 = 0 := by simpa [hpe] using h
        rw [bdec_of_eq y dec L h0] at hq
        simp at hq; omega
      have hscan := scan_run y lo L (bdec y dec L).1 pe (bdec y dec L).2.1 (bdec y dec L).2.2 fs hsL hp₁
        hpe' (10 * L + 1)
      obtain ⟨n2, w2, hn2, h2, h2f, h2e⟩ := match_of_scan y lo L _ pe _ _ fs _ hscan top
        (if fs then 1 else 0) 0 w1 h1c h1B h1H (by simp [Phi]; omega)
      have hchg : ∀ cD, CostHyp y dec cD → pe = true → (bdec y dec L).1 ≤ 8 * (bdec y dec L).2.1 := by
        intro cD hc h
        have h0 : (dec (y.take L)).2.1 ≠ 0 := by simpa [hpe] using h
        rw [bdec_of_ne y dec L h0]
        exact hc.charge L hL1' hm h0
      have hjob : BorderJobHead.headJob y (bdec y dec) 8 lo (fuel + 1) (if fs then 1 else 0) L =
          stRun y L (bdec y dec L).1 (bdec y dec L).2.1 (bdec y dec L).2.2 (10 * L + 1)
            ⟨if fs then 1 else 0, 0⟩ ++
          BorderJobHead.headJob y (bdec y dec) 8 lo fuel 0 (nextLen (bdec y dec L).1) := by
        rw [BorderJobHead.headJob, if_neg (by omega), if_neg (by omega), stageRunFrom_eq]
      rw [hjob, flagStream_append]
      generalize hR : stRun y L (bdec y dec L).1 (bdec y dec L).2.1 (bdec y dec L).2.2 (10 * L + 1)
        ⟨if fs then 1 else 0, 0⟩ = R at h2f h2e hn2
      have hA : ∀ cD : ℕ, cD ≤ cD * L := fun cD => Nat.le_mul_of_pos_right cD (by omega)
      have hΦ : Phi 8 ⟨if fs then 1 else 0, 0⟩ ≤ 9 * L := by simp only [Phi]; split <;> omega
      cases ho : (fsRun lo top R).2 with
      | none =>
        rw [ho] at h2e hn2
        refine ⟨n1 + n2, w2, fun cD hc => ?_, iterFlags_trans h1 h2, h2e, ?_⟩
        · have b1 := hn1 cD hc.decCost
          have b2 := hn2 (hchg cD hc)
          have e : (3 * cD + 3000) * L = 3 * (cD * L) + 3000 * L := by ring
          have := hA cD
          simp only [endTop] at b2
          rw [hs] at hsL
          rw [e]
          omega
        · rw [h2f, h1f]; simp [fsCont]
      | some t =>
        rw [ho] at h2e hn2
        obtain ⟨h2c, h2B, h2C⟩ := h2e
        obtain ⟨n3, w3, hn3, h3, h3c, h3B, h3f⟩ := shrink_run y lo fs pe L (bdec y dec L).1 t w2 h2c h2B
          h2C (by rw [hs]; exact hnl)
        obtain ⟨n4, w4, hn4, h4, h4d, h4f⟩ := stages_run hD hL1 fuel false (some pe) _ t w3 h3c h3B
          (by rw [hs]; omega)
        refine ⟨n1 + n2 + n3 + n4, w4, fun cD hc => ?_,
          iterFlags_trans (iterFlags_trans (iterFlags_trans h1 h2) h3) h4, h4d, ?_⟩
        · have b1 := hn1 cD hc.decCost
          have b2 := hn2 (hchg cD hc)
          have b4 := hn4 cD hc
          simp only [endTop] at b2
          have hsh := hc.short L hL1' hm
          have hnl3 : 3 * nextLen (bdec y dec L).1 + 1 ≤ L := by
            rw [hs]; exact nextLen_shrink hsh
          have hAB : cD * (3 * nextLen (bdec y dec L).1 + 1) ≤ cD * L := Nat.mul_le_mul_left cD hnl3
          have e1 : (3 * cD + 3000) * L = 3 * (cD * L) + 3000 * L := by ring
          have e2 : (3 * cD + 3000) * nextLen (bdec y dec L).1 =
              3 * (cD * nextLen (bdec y dec L).1) + 3000 * nextLen (bdec y dec L).1 := by ring
          have e3 : cD * (3 * nextLen (bdec y dec L).1 + 1) =
              3 * (cD * nextLen (bdec y dec L).1) + cD := by ring
          rw [hs] at hsL hn3 e2 e3 b4 hAB hnl3
          rw [e2] at b4
          rw [e3] at hAB
          rw [e1]
          omega
        · rw [h4f, h3f, h2f, h1f]
          simp [fsCont, List.append_assoc]

end Scan

/-! ## 6. The whole program -/

/-- **The flags head program pushes `BorderJobHead.dualFlags`.** Started as `DualFlagVM(y, lo, up)`
(`flagsInitialVM`), the dual flag controller runs on `stepFlags` until it returns, and the flags
it has pushed are `dualFlags y (bdec y dec) 8 lo up`, for the decomposition `dec` its `Decompose`
computes (`DecomposeContract`) and assuming L1 for it (`nextLen s < L` at every stage length).
With `BorderJobHead.dualFlags_eq` (given `StageOK` for `bdec y dec`) these are the palindrome
flags of the lengths `up-1, …, lo`. -/
theorem flags_head_dualFlags {dec : List (Fin 2) → ℕ × ℕ × ℕ} (hD : DecomposeContract 8 dec)
    (y : List (Fin 2)) (hL1 : ∀ L, 1 ≤ L → L ≤ y.length → nextLen (dec (y.take L)).1 < L)
    (lo up : ℕ) :
    ∃ n w, (∀ cD, CostHyp y dec cD → n ≤ (3 * cD + 3000) * y.length + 4 * up + 10) ∧
      iterFlags n (flagsInitialVM y lo up (Ctl.ofOutcome (next (flagsInitial 8) none))) = some w ∧
      w.flagsDone ∧ w.flags = BorderJobHead.dualFlags y (bdec y dec) 8 lo up := by
  let v0 := flagsInitialVM y lo up (Ctl.ofOutcome (next (flagsInitial 8) none))
  have hv0 : v0.ctl =
      .pending [.flagController "dual_flag_controller" 8 "TextOrigin" 1] (.copy "Cursor" "Upper") := rfl
  let v1 : HVM := { v0 with
    pos := Function.update v0.pos "Cursor" (v0.pos "Upper")
    rev := Function.update v0.rev "Cursor" (v0.rev "Upper")
    ctl := .pending [.flagController "dual_flag_controller" 8 "TextOrigin" 2] (mv [("Cursor", -1)]) }
  have e1 : stepFlags v0 = some v1 := fcopy' hv0 rfl
  let v2 : HVM := { v1 with
    pos := Function.update v1.pos "Cursor" (v1.pos "Cursor" + -1)
    ctl := .pending [.flagController "dual_flag_controller" 8 "TextOrigin" 3] (.less "Cursor" "Lower") }
  have e2 : stepFlags v1 = some v2 := by
    refine fmove' (ms := [⟨"Cursor", -1⟩]) rfl ?_ rfl
    show moveSeq flagBlind v1.len _ v1.pos = _
    rw [moveSeq_cons_ok (by intro h; exact absurd (by simp [flagBlind]) h), moveSeq_nil']
  have hC2 : v2.pos "Cursor" = (up : ℤ) - 1 := by
    simp [v2, v1, v0, flagsInitialVM, Function.update]; ring
  have hL2 : v2.pos "Lower" = lo := by simp [v2, v1, v0, flagsInitialVM, Function.update]
  by_cases hul : up ≤ lo
  · have e3 : stepFlags v2 = some { v2 with ctl := .returned none } :=
      fless' (d := true) rfl (by rw [hC2, hL2]; simp; omega) rfl
    refine ⟨3, { v2 with ctl := .returned none }, fun _ _ => by omega, ?_, ⟨none, rfl⟩, ?_⟩
    · exact iterFlags_succ e1 (iterFlags_succ e2 (iterFlags_one e3))
    · simp [v2, v1, v0, flagsInitialVM, BorderJobHead.dualFlags, hul]
  · have e3 : stepFlags v2 = some { v2 with ctl := bctl true none 1 (.copy "End" "OriginalEnd") } :=
      fless' (d := false) rfl (by rw [hC2, hL2]; simp; omega) rfl
    let v4 : HVM := { v2 with
      pos := Function.update v2.pos "End" (v2.pos "OriginalEnd")
      rev := Function.update v2.rev "End" (v2.rev "OriginalEnd")
      ctl := bctl true none 2 (.copy "Tail" "TextOrigin") }
    have e4 : stepFlags { v2 with ctl := bctl true none 1 (.copy "End" "OriginalEnd") } = some v4 :=
      fcopy' (v := { v2 with ctl := bctl true none 1 (.copy "End" "OriginalEnd") }) rfl rfl
    let v5 : HVM := { v4 with
      pos := Function.update v4.pos "Tail" (v4.pos "TextOrigin")
      rev := Function.update v4.rev "Tail" (v4.rev "TextOrigin")
      ctl := stageCtl true none }
    have e5 : stepFlags v4 = some v5 := fcopy' rfl rfl
    have hB5 : Base y lo y.length up v5 := {
      word := rfl
      origin := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]
      rOrigin := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]
      end_ := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]
      tail := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]
      rTail := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]
      oend := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]
      rOend := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]
      lower := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]
      cursor := by simp [v5, v4, v2, v1, v0, flagsInitialVM, Function.update]; ring
      le := le_rfl }
    obtain ⟨n, w, hn, h, hd, hf⟩ := stages_run y lo hD hL1 (y.length + 1) true none y.length up v5 rfl
      hB5 (by omega)
    refine ⟨5 + n, w, fun cD hc => by have := hn cD hc; omega, ?_, hd, ?_⟩
    · have h5 : iterFlags 5 v0 = some v5 := by
        simp only [iterFlags, e1, Option.bind_some, e2, e3, e4, e5]
      exact iterFlags_trans h5 h
    · rw [hf]
      simp [v5, v4, v2, v1, v0, flagsInitialVM, BorderJobHead.dualFlags, hul]

/-- **Linear form.** With `CostHyp` (`cut_short`, `cut_charge`, and `Decompose` in `cD·L + cD`
steps) and `up ≤ |y|`, the flags program finishes within `(3·cD + 3004)·|y| + 10` steps. -/
theorem flags_head_linear {dec : List (Fin 2) → ℕ × ℕ × ℕ} (hD : DecomposeContract 8 dec)
    (y : List (Fin 2)) {cD : ℕ} (hc : CostHyp y dec cD) (lo up : ℕ) (hup : up ≤ y.length) :
    ∃ n w, n ≤ (3 * cD + 3004) * y.length + 10 ∧
      iterFlags n (flagsInitialVM y lo up (Ctl.ofOutcome (next (flagsInitial 8) none))) = some w ∧
      w.flagsDone ∧ w.flags = BorderJobHead.dualFlags y (bdec y dec) 8 lo up := by
  obtain ⟨n, w, hn, h1, h2, h3⟩ := flags_head_dualFlags hD y
    (fun L h1 h2 => nextLen_lt (k := 8) (by norm_num) (hc.short L h1 h2)) lo up
  refine ⟨n, w, ?_, h1, h2, h3⟩
  have := hn cD hc
  have e : (3 * cD + 3004) * y.length = (3 * cD + 3000) * y.length + 4 * y.length := by ring
  omega

/-- **The palindrome bits.** If `bdec y dec` satisfies `StageOK` at every stage length (the
hypothesis of `BorderJobHead.dualFlags_eq`) and `up ≤ |y|`, the flags program pushes the palindrome
flags of the prefixes of lengths `up-1, …, lo` of `y`, within `(3·cD + 3004)·|y| + 10` steps. -/
theorem flags_head_palindromes {dec : List (Fin 2) → ℕ × ℕ × ℕ} (hD : DecomposeContract 8 dec)
    {cD : ℕ} (hcost : DecomposeCost 8 cD) (y : List (Fin 2))
    (hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (bdec y dec L).1 (bdec y dec L).2.1 (bdec y dec L).2.2)
    (lo up : ℕ) (hup : up ≤ y.length) :
    ∃ n w, n ≤ (3 * cD + 3004) * y.length + 10 ∧
      iterFlags n (flagsInitialVM y lo up (Ctl.ofOutcome (next (flagsInitial 8) none))) = some w ∧
      w.flagsDone ∧
      w.flags = (BorderJobHead.lensDown lo up).map (fun m => decide (IsPal (y.take m))) := by
  have hc : CostHyp y dec cD := {
    short := fun L h1 h2 => by
      have := (hOK L h1 h2).cut_short
      rw [bdec_fst y dec L] at this; simpa using this
    charge := fun L h1 h2 hne => by
      have := (hOK L h1 h2).cut_charge
      rw [bdec_of_ne y dec L hne] at this; exact this
    decCost := hcost }
  obtain ⟨n, w, hn, h1, h2, h3⟩ := flags_head_linear hD y hc lo up hup
  exact ⟨n, w, hn, h1, h2, h3.trans (BorderJobHead.dualFlags_eq (by norm_num) hOK lo up hup)⟩

/-! ## 7. With the proved `Decompose` contract (`ScaHeadDecompose.decompose_run`) -/

/-- The decomposition the program runs: `GSPreprocess.decompose · 8`. -/
def gsDec8 : List (Fin 2) → ℕ × ℕ × ℕ := fun x => decompose x 8

theorem stepMatch_returned {v : HVM} {val : Value} (h : v.ctl = .returned val) : stepMatch v = none := by
  unfold stepMatch; rw [h]

/-- A matcher run that has returned has a unique length. -/
theorem iterStep_returned_le {v w w' : HVM} {n m : ℕ} (h1 : iterStep n v = some w)
    (hw : ∃ val, w.ctl = .returned val) (h2 : iterStep m v = some w') : m ≤ n := by
  by_contra hlt
  obtain ⟨val, hval⟩ := hw
  obtain ⟨d, rfl⟩ : ∃ d, m = n + (d + 1) := ⟨m - n - 1, by omega⟩
  rw [iterStep_add, h1, Option.bind_some] at h2
  simp [iterStep, stepMatch_returned hval] at h2

theorem decomposeContract_gs : DecomposeContract 8 gsDec8 := by
  intro v L hv hO hE hL1 hLl
  have hlen : L ≤ v.word.length := by simp only [HVM.len] at hLl; omega
  obtain ⟨n, b, π', -, hrun, hkeep, -, -, hC, hiff, hper⟩ := ScaHeadDecompose.decompose_run 8
    (by norm_num) (v.word.take L) (v.word.drop L) v hv (List.take_append_drop L v.word).symm hO
    (by rw [hE, List.length_take, Nat.min_eq_left hlen])
    (by rw [List.take_append_drop]; intro h; rw [h] at hlen; simp at hlen; omega)
  have hb : b = decide ((gsDec8 (v.word.take L)).2.1 ≠ 0) := by
    cases b <;> simp [gsDec8] at hiff ⊢ <;> tauto
  subst hb
  refine ⟨n, π', hrun, hC, fun hne => ?_, fun h hh => hkeep h hh⟩
  obtain ⟨h1, h2, h3⟩ := hper (by simpa [gsDec8] using hne)
  exact ⟨by rw [h1]; simp [gsDec8], by rw [h2]; simp [gsDec8], by rw [h3]; simp [gsDec8]⟩

theorem decomposeCost_gs : DecomposeCost 8 1698 := by
  intro v w L n hv hO hE hL1 hLl hrun hret
  have hlen : L ≤ v.word.length := by simp only [HVM.len] at hLl; omega
  obtain ⟨n0, b, π', hn0, hrun0, -⟩ := ScaHeadDecompose.decompose_run 8
    (by norm_num) (v.word.take L) (v.word.drop L) v hv (List.take_append_drop L v.word).symm hO
    (by rw [hE, List.length_take, Nat.min_eq_left hlen])
    (by rw [List.take_append_drop]; intro h; rw [h] at hlen; simp at hlen; omega)
  have hle := iterStep_returned_le hrun0 ⟨_, rfl⟩ hrun
  rw [List.length_take, Nat.min_eq_left hlen] at hn0
  omega

/-- **The flags head program with its own `Decompose`.** Only L1 for `decompose · 8` (the open gap
of `SCA_GS_MAPPING.md` §6) is assumed. -/
theorem flags_head_gs (y : List (Fin 2))
    (hL1 : ∀ L, 1 ≤ L → L ≤ y.length → nextLen (decompose (y.take L) 8).1 < L) (lo up : ℕ) :
    ∃ n w, iterFlags n (flagsInitialVM y lo up (Ctl.ofOutcome (next (flagsInitial 8) none))) = some w ∧
      w.flagsDone ∧ w.flags = BorderJobHead.dualFlags y (bdec y gsDec8) 8 lo up := by
  obtain ⟨n, w, -, h1, h2, h3⟩ := flags_head_dualFlags decomposeContract_gs y hL1 lo up
  exact ⟨n, w, h1, h2, h3⟩

/-- **The palindrome bits in linear time, with the program's own `Decompose`.** Assumes `StageOK`
for the effective decomposition `bdec y gsDec8` (L1 and the `k`-simplicity of each stage: the
open gap of `SCA_GS_MAPPING.md` §6) and `up ≤ |y|`. -/
theorem flags_head_gs_palindromes (y : List (Fin 2))
    (hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (bdec y gsDec8 L).1 (bdec y gsDec8 L).2.1 (bdec y gsDec8 L).2.2)
    (lo up : ℕ) (hup : up ≤ y.length) :
    ∃ n w, n ≤ 8098 * y.length + 10 ∧
      iterFlags n (flagsInitialVM y lo up (Ctl.ofOutcome (next (flagsInitial 8) none))) = some w ∧
      w.flagsDone ∧
      w.flags = (BorderJobHead.lensDown lo up).map (fun m => decide (IsPal (y.take m))) :=
  flags_head_palindromes decomposeContract_gs decomposeCost_gs y hOK lo up hup

end PalPeg.ScaFlagsHead
