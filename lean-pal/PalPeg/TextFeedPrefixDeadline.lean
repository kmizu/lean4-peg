import PalPeg.TextFeedPrefixRank

/-! Rank descent across real input frames: one arrival is followed by
exactly R atomic source calls. Input waiting does not invalidate the phase
invariant; once the prefix is available its rank falls by R per frame. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixDeadline
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.TextFeedControl PalPeg.TextFeedPrefixAtomic PalPeg.TextFeedPrefixCycle
open PalPeg.TextFeedPrefixRank PalPeg.TextFeedPrefixMachine

variable {k : ℕ}

def erase {R : ℕ} (z : Outer R × Data k) : Stack Act Cond × Model k := (z.1.2.2.val, z.2.worker)

theorem frame_erase_partial (e : Env k) (R : ℕ) (a : Fin k) (z : Outer R × Data k) (hz : z.1.1 = 0) :
    ∀ N : ℕ, N ≤ R →
    erase ((modelStep e R)^[N + 1] (z.1, capture z.2 a)) =
      (tick e)^[N] (TextFeedPrefixRank.arrive a (erase z)) := by
  intro N
  induction N with
  | zero =>
    intro _
    change erase (modelStep e R (z.1, capture z.2 a)) = _
    rw [modelStep, if_pos hz]
    rfl
  | succ N ih =>
    intro hn
    have hc : ((modelStep e R)^[N + 1] (z.1, capture z.2 a)).1.1 ≠ 0 := by
      rw [model_counter_iterate, hz]
      have hh := nextPhase_iterate (Nat.zero_lt_succ R) (N + 1) (by omega : N + 1 < R + 1)
      change (nextPhase^[N + 1] (⟨0, Nat.zero_lt_succ R⟩ : Fin (R + 1))) ≠ 0
      rw [hh]
      intro he
      have hh' : N + 1 = 0 := congrArg Fin.val he
      omega
    have hstep : erase (modelStep e R ((modelStep e R)^[N + 1] (z.1, capture z.2 a))) =
        tick e (erase ((modelStep e R)^[N + 1] (z.1, capture z.2 a))) := machine_work_tick e R _ hc
    rw [Function.iterate_succ_apply', hstep, ih (by omega), Function.iterate_succ_apply']

theorem frame_erase (e : Env k) (R : ℕ) (a : Fin k) (z : Outer R × Data k) (hz : z.1.1 = 0) :
    erase (modelFrame e R a z) = (tick e)^[R] (TextFeedPrefixRank.arrive a (erase z)) :=
  frame_erase_partial e R a z hz R (Nat.le_refl R)

theorem workers_progress {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n fuel z)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length) (hroom : u.length ≤ n) (N : ℕ) :
    Good e u v Text d p r n (fuel - N) ((tick e)^[N] z) := by
  induction N generalizing z fuel with
  | zero => exact h
  | succ N ih =>
    rw [Function.iterate_succ_apply]
    have hh := ih (h.progress hmb hblank hmark hend hsu hse hn hroom)
    convert hh using 1; omega

theorem workers_preserve {e : Env k} {u v Text : List (Fin k)} {d p r n fuel : ℕ}
    {z : Stack Act Cond × Model k} (h : Good e u v Text d p r n fuel z)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length) (N : ℕ) :
    ∃ fuel', Good e u v Text d p r n fuel' ((tick e)^[N] z) := by
  induction N generalizing z fuel with
  | zero => exact ⟨fuel, h⟩
  | succ N ih =>
    obtain ⟨fuel', hh⟩ := h.preserve hmb hblank hmark hend hsu hse hn
    rw [Function.iterate_succ_apply]
    exact ih hh

theorem frame_progress {e : Env k} {u v Text : List (Fin k)} {d p r n fuel R : ℕ}
    {z : Outer R × Data k} {a : Fin k} (h : Good e u v Text d p r n fuel (erase z)) (hz : z.1.1 = 0)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n < Text.length) (ha : Text[n]? = some a) (hroom : u.length ≤ n + 1) :
    Good e u v Text d p r (n + 1) (fuel - R) (erase (modelFrame e R a z)) := by
  rw [frame_erase e R a z hz]
  exact workers_progress (h.arrive hmb hn ha) hmb hblank hmark hend hsu hse (by omega) hroom R

theorem frame_preserve {e : Env k} {u v Text : List (Fin k)} {d p r n fuel R : ℕ}
    {z : Outer R × Data k} {a : Fin k} (h : Good e u v Text d p r n fuel (erase z)) (hz : z.1.1 = 0)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n < Text.length) (ha : Text[n]? = some a) :
    ∃ fuel', Good e u v Text d p r (n + 1) fuel' (erase (modelFrame e R a z)) := by
  rw [frame_erase e R a z hz]
  exact workers_preserve (h.arrive hmb hn ha) hmb hblank hmark hend hsu hse (by omega) R

inductive Valid (Text : List (Fin k)) : ℕ → List (Fin k) → Prop
  | nil {n} (hn : n ≤ Text.length) : Valid Text n []
  | cons {n a w} (ha : Text[n]? = some a) (ht : Valid Text (n + 1) w) : Valid Text n (a :: w)

theorem Valid.bound {Text : List (Fin k)} {n : ℕ} {w : List (Fin k)} (h : Valid Text n w) :
    n + w.length ≤ Text.length := by
  induction h with
  | nil hn => exact hn
  | cons _ _ ih => simp only [List.length_cons]; omega

noncomputable def frames (e : Env k) (R : ℕ) (w : List (Fin k)) (z : Outer R × Data k) :=
  w.foldl (fun z a => modelFrame e R a z) z

theorem frames_counter (e : Env k) (R : ℕ) (w : List (Fin k))
    (z : Outer R × Data k) (hz : z.1.1 = 0) : (frames e R w z).1.1 = 0 := by
  induction w generalizing z with
  | nil => exact hz
  | cons a w ih => exact ih _ (frame_counter e R a z hz)

/-- Waiting for input may change the rank, but never loses the invariant. -/
theorem frames_preserve {e : Env k} {u v Text : List (Fin k)} {d p r n fuel R : ℕ}
    {z : Outer R × Data k} (h : Good e u v Text d p r n fuel (erase z)) (hz : z.1.1 = 0)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    {w : List (Fin k)} (hw : Valid Text n w) :
    ∃ fuel', Good e u v Text d p r (n + w.length) fuel' (erase (frames e R w z)) := by
  induction hw generalizing z fuel with
  | nil _ => exact ⟨fuel, h⟩
  | @cons n a w ha ht ih =>
    have hn : n < Text.length := by have := ht.bound; omega
    obtain ⟨f, hh⟩ := frame_preserve h hz hmb hblank hmark hend hsu hse hn ha
    obtain ⟨f', hh'⟩ := ih hh (frame_counter e R a z hz)
    refine ⟨f', ?_⟩
    change Good e u v Text d p r (n + (a :: w).length) f'
      (erase (frames e R w (modelFrame e R a z)))
    convert hh' using 1; simp only [List.length_cons]; omega

theorem frames_progress {e : Env k} {u v Text : List (Fin k)} {d p r n fuel R : ℕ}
    {z : Outer R × Data k} (h : Good e u v Text d p r n fuel (erase z)) (hz : z.1.1 = 0)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hroom : u.length ≤ n) {w : List (Fin k)} (hw : Valid Text n w) :
    Good e u v Text d p r (n + w.length) (fuel - w.length * R) (erase (frames e R w z)) := by
  induction hw generalizing z fuel with
  | nil _ => simpa only [List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.sub_zero, frames, List.foldl_nil] using h
  | @cons n a w ha ht ih =>
    have hn : n < Text.length := by have := ht.bound; omega
    have hh := frame_progress h hz hmb hblank hmark hend hsu hse hn ha (by omega)
    have hh' := ih hh (frame_counter e R a z hz) (by omega)
    change Good e u v Text d p r (n + (a :: w).length) (fuel - (a :: w).length * R)
      (erase (frames e R w (modelFrame e R a z)))
    convert hh' using 1 <;> simp only [List.length_cons, Nat.succ_mul] <;> omega

/-- This bound includes continuing arrivals: every frame still performs
exactly its R worker calls, and no new input increases the remaining rank. -/
theorem frames_complete {e : Env k} {u v Text : List (Fin k)} {d p r n fuel R : ℕ}
    {z : Outer R × Data k} (h : Good e u v Text d p r n fuel (erase z)) (hz : z.1.1 = 0)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hroom : u.length ≤ n) {w : List (Fin k)} (hw : Valid Text n w) (hbudget : fuel ≤ w.length * R) :
    (erase (frames e R w z)).1 = [] ∧
      ∃ M U, (erase (frames e R w z)).2 = TextFeedPrefixFinish.data M U ∧
        Rep e u v Text d p r (n + w.length) M U u.length 1 ∧ M.m = u.length := by
  have hh := frames_progress h hz hmb hblank hmark hend hsu hse hroom hw
  rw [Nat.sub_eq_zero_of_le hbudget] at hh
  exact hh.finished

/-- No lower bound on available input is needed during the waiting word.
Once it has arrived, a uniform prefix-sized work budget suffices. -/
theorem wait_complete {e : Env k} {u v Text : List (Fin k)} {d p r n fuel R : ℕ}
    {z : Outer R × Data k} (h : Good e u v Text d p r n fuel (erase z)) (hz : z.1.1 = 0)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    {waiting running : List (Fin k)} (hw : Valid Text n waiting)
    (hr : Valid Text (n + waiting.length) running) (hroom : u.length ≤ n + waiting.length)
    (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    (erase (frames e R (waiting ++ running) z)).1 = [] ∧
      ∃ M U, (erase (frames e R (waiting ++ running) z)).2 = TextFeedPrefixFinish.data M U ∧
        Rep e u v Text d p r (n + (waiting ++ running).length) M U u.length 1 ∧ M.m = u.length := by
  obtain ⟨f, hh⟩ := frames_preserve h hz hmb hblank hmark hend hsu hse hw
  have hh' := frames_complete hh (frames_counter e R waiting z hz)
    hmb hblank hmark hend hsu hse hroom hr (Nat.le_trans hh.bound hbudget)
  simpa only [frames, List.foldl_append, List.length_append, Nat.add_assoc] using hh'

/-- The actual initial source continuation enters the rank invariant on
its first positive-rate frame, even if the prefix has not arrived yet. -/
theorem source_frame {e : Env k} {u v Text : List (Fin k)} {d p r n R : ℕ}
    {z : Outer R × Data k} {M : TextFeed.Machine' k} {U : TapeConfiguration k} {a : Fin k}
    (hz : z.1.1 = 0) (hctrl : (erase z).1 = [source])
    (hdata : (erase z).2 = TextFeedPrefixFinish.data M U)
    (h : Rep e u v Text d p r n M U 0 1) (hm : M.m = 0) (hR : 0 < R)
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n < Text.length) (ha : Text[n]? = some a) :
    ∃ fuel, Good e u v Text d p r (n + 1) fuel (erase (modelFrame e R a z)) := by
  rw [frame_erase e R a z hz]
  have he : erase z = ([source], TextFeedPrefixFinish.data M U) := Prod.ext hctrl hdata
  rw [he, arrive_data e, tick_start_iterate e _ R hR]
  exact workers_preserve (Good.loop (h.arrive hmb hn ha) hm (Nat.zero_le _))
    hmb hblank hmark hend hsu hse (by omega) R

noncomputable local instance : DecidableEq (TextFeedPrefixBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPrefixBank.Cond k) := Classical.decEq _
noncomputable local instance (R : ℕ) : DecidableEq (Outer R) := Classical.decEq _
attribute [local irreducible] StructuredMachine.sRound

/-- Completion of the actual finite machine, with arrivals still running.
The conclusion includes its genuinely empty source continuation. -/
theorem physical_complete {Terminal : Type} {e : Env k}
    (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) {u v Text : List (Fin k)} {d p r n fuel R : ℕ}
    {x : Config e R} {z : Outer R × Data k}
    (hsim : Sim e R x z) (h : Good e u v Text d p r n fuel (erase z))
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hroom : u.length ≤ n) (w : List Terminal) (hw : Valid Text n (w.map enc))
    (hall : ∀ a ∈ w, enc a ≠ e.mark) (hbudget : fuel ≤ w.length * R) :
    let y := w.foldl (machine e enc R).sRound x
    let z' := frames e R (w.map enc) z
    Sim e R y z' ∧ y.state.1.1.1.2.2.val = [] ∧
      ∃ M U, z'.2.worker = TextFeedPrefixFinish.data M U ∧
        Rep e u v Text d p r (n + w.length) M U u.length 1 ∧ M.m = u.length := by
  have hz : z.1.1 = 0 := by
    obtain ⟨_, _, _, _, _, _, _, hz, _⟩ := hsim
    exact hz
  have hlen : (w.map enc).length = w.length := List.length_map enc
  obtain ⟨hctrl, hfinal⟩ := frames_complete h hz hmb hblank hmark hend hsu hse hroom hw (by rwa [hlen])
  have hs := word_sim hc hmb enc R w hall hsim
  have he : frames e R (w.map enc) z = w.foldl (fun z a => modelFrame e R (enc a) z) z := by
    rw [frames, List.foldl_map]
  rw [← he] at hs
  refine ⟨hs, ?_, ?_⟩
  · have hstate : (w.foldl (machine e enc R).sRound x).state.1.1.1 = (frames e R (w.map enc) z).1 := by
      obtain ⟨c, _, _, _, _, hx, hc', _⟩ := hs
      rw [hx]
      exact hc'
    rw [hstate]
    exact hctrl
  · simpa only [erase, hlen] using hfinal

/-- Physical completion after an arbitrarily long input-waiting phase. -/
theorem physical_wait_complete {Terminal : Type} {e : Env k}
    (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) {u v Text : List (Fin k)} {d p r n fuel R : ℕ}
    {x : Config e R} {z : Outer R × Data k}
    (hsim : Sim e R x z) (h : Good e u v Text d p r n fuel (erase z))
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (waiting running : List Terminal) (hw : Valid Text n (waiting.map enc))
    (hr : Valid Text (n + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + waiting.length)
    (hall : ∀ a ∈ waiting ++ running, enc a ≠ e.mark)
    (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    let y := (waiting ++ running).foldl (machine e enc R).sRound x
    let z' := frames e R ((waiting ++ running).map enc) z
    Sim e R y z' ∧ y.state.1.1.1.2.2.val = [] ∧
      ∃ M U, z'.2.worker = TextFeedPrefixFinish.data M U ∧
        Rep e u v Text d p r (n + (waiting ++ running).length) M U u.length 1 ∧ M.m = u.length := by
  have hz : z.1.1 = 0 := by
    obtain ⟨_, _, _, _, _, _, _, hz, _⟩ := hsim
    exact hz
  obtain ⟨f, hh⟩ := frames_preserve h hz hmb hblank hmark hend hsu hse hw
  simp only [List.length_map] at hh
  have hs := word_sim hc hmb enc R waiting (fun a ha => hall a (List.mem_append_left _ ha)) hsim
  have he : frames e R (waiting.map enc) z = waiting.foldl (fun z a => modelFrame e R (enc a) z) z := by
    rw [frames, List.foldl_map]
  rw [← he] at hs
  have result := physical_complete hc hmb enc hs hh hblank hmark hend hsu hse hroom running hr
    (fun a ha => hall a (List.mem_append_right _ ha)) (Nat.le_trans hh.bound hbudget)
  simpa only [List.foldl_append, List.map_append, List.length_append, Nat.add_assoc, frames] using result

/-- Start with the source program itself, not an assumed intermediate
continuation. The initial frame may arrive before the prefix is available. -/
theorem physical_source_complete {Terminal : Type} {e : Env k}
    (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) {u v Text : List (Fin k)} {d p r n R : ℕ}
    {x : Config e R} {z : Outer R × Data k}
    {M : TextFeed.Machine' k} {U : TapeConfiguration k}
    (hsim : Sim e R x z) (hctrl : (erase z).1 = [source])
    (hdata : (erase z).2 = TextFeedPrefixFinish.data M U)
    (h : Rep e u v Text d p r n M U 0 1) (hm : M.m = 0) (hR : 0 < R)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (a : Terminal) (waiting running : List Terminal)
    (hn : n < Text.length) (ha : Text[n]? = some (enc a))
    (hw : Valid Text (n + 1) (waiting.map enc))
    (hr : Valid Text (n + 1 + waiting.length) (running.map enc))
    (hroom : u.length ≤ n + 1 + waiting.length)
    (hall : ∀ b ∈ a :: (waiting ++ running), enc b ≠ e.mark)
    (hbudget : 5 * u.length + 2 ≤ running.length * R) :
    let y := (a :: (waiting ++ running)).foldl (machine e enc R).sRound x
    let z' := frames e R ((a :: (waiting ++ running)).map enc) z
    Sim e R y z' ∧ y.state.1.1.1.2.2.val = [] ∧
      ∃ M U, z'.2.worker = TextFeedPrefixFinish.data M U ∧
        Rep e u v Text d p r (n + (a :: (waiting ++ running)).length) M U u.length 1 ∧ M.m = u.length := by
  have hz : z.1.1 = 0 := by
    obtain ⟨_, _, _, _, _, _, _, hz, _⟩ := hsim
    exact hz
  obtain ⟨f, hh⟩ := source_frame hz hctrl hdata h hm hR hmb hblank hmark hend hsu hse hn ha
  have hs := word_sim hc hmb enc R [a] (by
    intro b hb
    have he : b = a := List.mem_singleton.mp hb
    subst b
    exact hall a (List.mem_cons_self)) hsim
  simp only [List.foldl_cons, List.foldl_nil] at hs
  have result := physical_wait_complete hc hmb enc hs hh hblank hmark hend hsu hse
    waiting running hw hr hroom (fun b hb => hall b (List.mem_cons_of_mem a hb)) hbudget
  simpa only [List.foldl_cons, List.map_cons, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    frames] using result

/-- info: 'PalPeg.TextFeedPrefixDeadline.physical_source_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms physical_source_complete

/-- info: 'PalPeg.TextFeedPrefixDeadline.physical_wait_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms physical_wait_complete

/-- info: 'PalPeg.TextFeedPrefixDeadline.source_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_frame

/-- info: 'PalPeg.TextFeedPrefixDeadline.physical_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms physical_complete

/-- info: 'PalPeg.TextFeedPrefixDeadline.frames_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_complete

/-- info: 'PalPeg.TextFeedPrefixDeadline.frame_preserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_preserve

end PalPeg.TextFeedPrefixDeadline
