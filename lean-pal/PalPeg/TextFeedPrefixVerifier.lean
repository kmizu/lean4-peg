import PalPeg.TextFeedPrefixDeadline

/-! The arrival-aware prefix phase establishes the verifier's feed
invariant. Both FIFO representations are taken from the actual machine's
simulation, not independently postulated at its endpoint. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixVerifier
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedPrefixMachine PalPeg.TextFeedPrefixDeadline
open PalPeg.TextFeedPrefixRank

variable {k : ℕ}

theorem valid_take_append {Text : List (Fin k)} {n : ℕ} {w : List (Fin k)}
    (h : Valid Text n w) : Text.take n ++ w = Text.take (n + w.length) := by
  induction h with
  | nil _ => simp
  | @cons n a w ha ht ih =>
    have hs : Text.take (n + 1) = Text.take n ++ [a] := by
      rw [List.take_add_one, ha]; rfl
    rw [hs] at ih
    simpa only [List.append_assoc, List.singleton_append, List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih

theorem step_X (e : Env k) (R : ℕ) (z : Outer R × Data k) :
    (modelStep e R z).2.X = z.2.X := by
  unfold modelStep
  split <;> rfl

theorem frame_X (e : Env k) (R : ℕ) (a : Fin k) (z : Outer R × Data k) :
    (modelFrame e R a z).2.X = z.2.X := by
  have hi : ∀ N : ℕ, ∀ z : Outer R × Data k, ((modelStep e R)^[N] z).2.X = z.2.X := by
    intro N
    induction N with
    | zero => intro z; rfl
    | succ N ih => intro z; rw [Function.iterate_succ_apply', step_X, ih]
  exact hi (R + 1) (z.1, capture z.2 a)

theorem frames_X (e : Env k) (R : ℕ) (w : List (Fin k)) (z : Outer R × Data k) :
    (frames e R w z).2.X = z.2.X := by
  induction w generalizing z with
  | nil => rfl
  | cons a w ih => change (frames e R w (modelFrame e R a z)).2.X = _; rw [ih, frame_X]

theorem frames_q₂ {e : Env k} {R n : ℕ} {Text w : List (Fin k)} {z : Outer R × Data k}
    (hz : z.1.1 = 0) (hi : Inv z.2.q₂) (hl : toList z.2.q₂ = Text.take n)
    (hw : Valid Text n w) : toList (frames e R w z).2.q₂ = Text.take (n + w.length) := by
  have hh := word_q₂_contents e id R w z hz hi
  simp only [List.map_id, id_eq] at hh
  rw [frames, hh, hl]
  exact valid_take_append hw

/-- A completed physical prefix run supplies both physical FIFO witnesses
and the verifier's genuine initial position, including its untouched X. -/
theorem endpoint_ready {e : Env k} {u v Text : List (Fin k)} {d p r n R : ℕ}
    {x y : Config e R} {z : Outer R × Data k} {w : List (Fin k)}
    (hin : Sim e R x z) (hout : Sim e R y (frames e R w z))
    (hw : Valid Text n w) (hl : toList z.2.q₂ = Text.take n)
    (hx : Tape.SeqView e.blank z.2.X (TextFeed.padW e.blank Text 0) 0)
    {M : TextFeed.Machine' k} {U : TapeConfiguration k}
    (hdata : (frames e R w z).2.worker = TextFeedPrefixFinish.data M U)
    (hrep : Rep e u v Text d p r (n + w.length) M U u.length 1) :
    ∃ qt₁ m₁ qt₂ m₂,
      y.tape = tapes e qt₁ m₁ qt₂ m₂ (frames e R w z).2 ∧
      Ready e.blank e.mark qt₁ m₁ M.Q ∧
      Ready e.blank e.mark qt₂ m₂ (frames e R w z).2.q₂ ∧
      VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r (n + w.length)
        (TextFeedPrefixReady.model M U (frames e R w z).2.X (frames e R w z).2.q₂
          ⟨qt₂ ∘ m₂.roles, 0⟩) := by
  obtain ⟨_, _, _, _, _, _, _, hz, _, _, _, hq₂⟩ := hin
  have hl' := frames_q₂ (e := e) hz hq₂.inv hl hw
  have hx' : Tape.SeqView e.blank (frames e R w z).2.X (TextFeed.padW e.blank Text 0) 0 := by
    rwa [frames_X]
  obtain ⟨c, qt₁, m₁, qt₂, m₂, he, _, _, _, _, h₁, h₂⟩ := hout
  refine ⟨qt₁, m₁, qt₂, m₂, ?_, ?_, h₂, ?_⟩
  · rw [he]
  · simpa only [hdata, TextFeedPrefixFinish.data] using h₁
  · exact TextFeedPrefixReady.model_feedInv hrep.feed hrep.pos hrep.pat hx' h₂.enc h₂.inv hl'

def VerifierReady (e : Env k) (u v Text : List (Fin k)) (d p r n R : ℕ)
    (y : Config e R) (D : Data k) : Prop :=
  ∃ M U qt₁ m₁ qt₂ m₂,
    D.worker = TextFeedPrefixFinish.data M U ∧
    y.tape = tapes e qt₁ m₁ qt₂ m₂ D ∧
    Ready e.blank e.mark qt₁ m₁ M.Q ∧ Ready e.blank e.mark qt₂ m₂ D.q₂ ∧
    VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n
      (TextFeedPrefixReady.model M U D.X D.q₂ ⟨qt₂ ∘ m₂.roles, 0⟩) ∧
    M.st.pos = u.length ∧ M.st.q = 0 ∧ M.m = u.length

noncomputable local instance : DecidableEq (TextFeedPrefixBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPrefixBank.Cond k) := Classical.decEq _
noncomputable local instance (R : ℕ) : DecidableEq (Outer R) := Classical.decEq _
attribute [local irreducible] StructuredMachine.sRound

/-- From the initial source continuation, through input waiting and the
fixed-rate physical execution, to the verifier's feed-ready endpoint. -/
theorem source_ready {Terminal : Type} {e : Env k}
    (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) {u v Text : List (Fin k)} {d p r n R : ℕ}
    {x : Config e R} {z : Outer R × Data k}
    {M : TextFeed.Machine' k} {U : TapeConfiguration k}
    (hsim : Sim e R x z) (hctrl : (erase z).1 = [TextFeedPrefixAtomic.source])
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
    (hbudget : 5 * u.length + 2 ≤ running.length * R)
    (hl : toList z.2.q₂ = Text.take n)
    (hx : Tape.SeqView e.blank z.2.X (TextFeed.padW e.blank Text 0) 0) :
    let w := a :: (waiting ++ running)
    let y := w.foldl (machine e enc R).sRound x
    y.state.1.1.1.2.2.val = [] ∧
      VerifierReady e u v Text d p r (n + w.length) R y (frames e R (w.map enc) z).2 := by
  obtain ⟨hs, hdone, M', U', hd, hp, hm'⟩ := physical_source_complete hc hmb enc hsim hctrl hdata h hm hR
    hblank hmark hend hsu hse a waiting running hn ha hw hr hroom hall hbudget
  have append_valid {n : ℕ} {w w' : List (Fin k)} (h : Valid Text n w)
      (h' : Valid Text (n + w.length) w') : Valid Text n (w ++ w') := by
    induction h with
    | nil _ => exact h'
    | @cons n a w ha ht ih =>
      apply Valid.cons ha
      exact ih (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h')
  have hv : Valid Text n ((a :: (waiting ++ running)).map enc) := by
    rw [List.map_cons, List.map_append]
    apply Valid.cons ha
    exact append_valid hw (by simpa only [List.length_map] using hr)
  have hp' : Rep e u v Text d p r (n + ((a :: (waiting ++ running)).map enc).length) M' U' u.length 1 := by
    simpa only [List.length_map] using hp
  obtain ⟨qt₁, m₁, qt₂, m₂, ht, h₁, h₂, hf⟩ := endpoint_ready hsim hs hv hl hx hd hp'
  refine ⟨hdone, M', U', qt₁, m₁, qt₂, m₂, hd, ht, h₁, h₂, ?_, hp.pos, hp.q, hm'⟩
  simpa only [List.length_map] using hf

/-- info: 'PalPeg.TextFeedPrefixVerifier.source_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_ready

/-- info: 'PalPeg.TextFeedPrefixVerifier.endpoint_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpoint_ready

end PalPeg.TextFeedPrefixVerifier
