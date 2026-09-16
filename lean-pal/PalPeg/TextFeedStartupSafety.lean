import PalPeg.TextFeedStartupSchedule

/-! Queue safety while the shared task is suspended in preparation or
scanning. A prep call may change the scanner tapes arbitrarily but cannot
change the FIFO or the current input cell. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartupSafety
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule

variable {k : ℕ} {Terminal : Type}

theorem extend_restrict {n t : ℕ} (ι : Fin n ↪ Fin t) (T : Fin t → STape (Fin k)) :
    extend ι (fun j => T (ι j)) T = T := by
  funext j
  cases hp : proj ι j with
  | none => exact extend_of_proj_none hp _ T
  | some i =>
    have hi := eq_ι_of_proj_eq_some hp
    subst j
    exact extend_ι ι _ T i

def ReadyAt (e : Env k) (T : Fin 27 → STape (Fin k)) (q : Queue (Fin k)) (old : Fin k) : Prop :=
  ∃ qt m S, feedView T = rtapes e qt m S old ∧ Ready e.blank e.mark qt m q

theorem feedView_extend (F : Fin 20 → STape (Fin k)) (T : Fin 27 → STape (Fin k)) :
    feedView (extend feedSlot F T) = F := by
  funext j
  exact extend_ι feedSlot F T j

theorem ready_feed {e : Env k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (h : Ready e.blank e.mark qt m q) (S : Stage k) (old : Fin k)
    (T : Fin 27 → STape (Fin k)) :
    ReadyAt e (extend feedSlot (rtapes e qt m S old) T) q old :=
  ⟨qt, m, S, feedView_extend _ _, h⟩

theorem prepSlot_outside {j : Fin 27} (h : j.val < 11 ∨ j.val = 26) :
    proj prepSlot j = none := by
  apply proj_eq_none
  intro i he
  have hv := congrArg Fin.val he
  change 11 + i.val = j.val at hv
  omega

theorem feedView_prep {e : Env k} {T : Fin 27 → STape (Fin k)}
    {qt : QT k} {m : Mode} {S : Stage k} {old : Fin k}
    (h : feedView T = rtapes e qt m S old) (P : Fin 15 → STape (Fin k)) :
    feedView (extend prepSlot P T) =
      rtapes e qt m (fun j => P (Fin.castAddEmb 7 j)) old := by
  funext j
  have hq := congrFun h j
  by_cases hj : j.val < 11
  · have hp : proj prepSlot (feedSlot j) = none := by
      apply prepSlot_outside
      left
      change (if h : j.val < 19 then (⟨j.val, by omega⟩ : Fin 27) else ⟨26, by decide⟩).val < 11
      rw [dif_pos (show j.val < 19 by omega)]
      exact hj
    change extend prepSlot P T (feedSlot j) = _
    rw [extend_of_proj_none hp]
    apply hq.trans
    fin_cases j <;> first | rfl | norm_num at hj
  · by_cases hs : j.val < 19
    · let i : Fin 8 := ⟨j.val - 11, by omega⟩
      have hij : feedSlot j = prepSlot (Fin.castAddEmb 7 i) := by
        apply Fin.ext
        change (if h : j.val < 19 then (⟨j.val, by omega⟩ : Fin 27) else ⟨26, by decide⟩).val =
          11 + (j.val - 11)
        rw [dif_pos hs]
        dsimp only
        omega
      change extend prepSlot P T (feedSlot j) = _
      rw [hij, extend_ι]
      fin_cases j <;> first | rfl | exact False.elim (hj (by decide)) | norm_num at hs
    · have hj19 : j = ⟨19, by decide⟩ := by apply Fin.ext; exact show j.val = 19 by omega
      subst j
      change extend prepSlot P T ⟨26, by omega⟩ = _
      rw [extend_of_proj_none (prepSlot_outside (Or.inr rfl))]
      exact hq

theorem ready_prep {e : Env k} {T : Fin 27 → STape (Fin k)}
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e T q old)
    (P : Fin 15 → STape (Fin k)) : ReadyAt e (extend prepSlot P T) q old := by
  obtain ⟨qt, m, S, hv, hr⟩ := h
  exact ⟨qt, m, _, feedView_prep hv P, hr⟩

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _

def queueEffect (e : Env k) (a : TextFeedStartupBank.Label k) (q : Queue (Fin k)) : Queue (Fin k) :=
  match a with
  | .first a => snoc empty a
  | .feed (.enqueue a) => snoc q a
  | .feed .supply => if (toList q).head?.getD e.mark = e.mark then q else RTQueue.tail q
  | _ => q

theorem queueEffect_feed (e : Env k) (a : TextFeedAtomic.Label k) (q : Queue (Fin k))
    (S : Stage k) : (TextFeedAtomic.effect e a q S).1 = queueEffect e (.feed a) q := by
  cases a with
  | supply =>
    dsimp only [TextFeedAtomic.effect, TextFeedAtomic.supplyEffect, queueEffect]
    split_ifs <;> rfl
  | _ => rfl

/-- All non-bootstrap calls preserve a valid queue. Preparation requires
no scanner invariant; its 15-tape work may be halfway through any loop. -/
theorem normal_bounded {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {T : Fin 27 → STape (Fin k)}
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e T q old)
    (a : TextFeedStartupBank.Label k)
    (ha : match a with
      | .first _ => False
      | .feed a => TextFeedAtomic.allowed e.mark a
      | .prep _ => True) :
    ∃ tr, Exec (shared (Terminal := Terminal) e) e.blank (low e a) T tr ∧
      tr.length ≤ 47 ∧ ReadyAt e (applyTrace e.blank T tr) (queueEffect e a q) old := by
  cases a with
  | first a => exact False.elim ha
  | feed a =>
    obtain ⟨qt, m, S, hv, hr⟩ := h
    obtain ⟨tr, qt', m', he, hn, ht, hr'⟩ :=
      feed_exec (Terminal := Terminal) hc hmb hr S old a ha T
    have hs : extend feedSlot (rtapes e qt m S old) T = T := by
      rw [← hv]
      exact extend_restrict feedSlot T
    rw [hs] at he ht
    rw [queueEffect_feed] at hr'
    exact ⟨tr, he, hn, ht ▸ ready_feed hr' _ old T⟩
  | prep a =>
    obtain ⟨tr, he, hn, ht⟩ := prep_exec (Terminal := Terminal) e a
      (fun j => T (prepSlot j)) T
    rw [extend_restrict] at he ht
    refine ⟨tr, he, by omega, ?_⟩
    rw [ht]
    exact ready_prep h _

/-- info: 'PalPeg.TextFeedStartupSafety.normal_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normal_bounded

end PalPeg.TextFeedStartupSafety
