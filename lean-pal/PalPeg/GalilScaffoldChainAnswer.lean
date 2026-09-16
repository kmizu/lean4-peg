import PalPeg.GalilScaffoldSearchRun
import PalPeg.GalilScaffoldInputHead

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainAnswer
open GalilScaffoldControl GalilScaffoldSearchFinish

/-- A found Search result puts the physical-list OUTPUT head on its final one,
so Chain.copy can begin with a legal left move. Walker/period guards are separate. -/
theorem found_output {s t : State} {x y : Machine 12} {as : List Bool}
    {w : List (Fin 3)} {lower : ℕ}
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    ∃ h, GalilDpCorrect.Candidate w lower h ∧
      (∀ k, k < h → ¬ GalilDpCorrect.Candidate w lower k) ∧
      GalilScaffoldTape.denote (y.config.tapes 11) = GalilDpCounters.output h ∧
      GalilScaffoldTape.head (y.config.tapes 11) = h ∧
      (y.config.tapes 11).focus = 8 ∧ (y.config.tapes 11).left ≠ [] := by
  have hl := (GalilScaffoldSearchRun.safe_quanta_terminal_link hr (Or.inl hs)).resolve_left (by simp [ht])
  have hpc := hl.1.mp ht
  rcases hv with ⟨h,_,hc,hmin,hp,hout,hpos⟩ | ⟨hp,hnone⟩
  · have hh : 0 < h := by have := hc.1; omega
    change GalilScaffoldTape.denote (y.config.tapes 11) = GalilDpCounters.output h at hout
    change GalilScaffoldTape.head (y.config.tapes 11) = h at hpos
    refine ⟨h,hc,fun k hk => hmin k (Nat.zero_le _) hk,hout,hpos,?_,?_⟩
    · rw [← GalilScaffoldTape.focus_eq,hpos,hout]
      simp [GalilDpCounters.output,show h ≠ 0 by omega]
    · intro he
      simp [GalilScaffoldTape.head,he] at hpos
      omega
  · change y.config.pc = 347 at hp
    omega

/-- OUTPUT/h projection of enabled Chain.copy ticks. Walker and period
guards must still be supplied when lifting this relation to the whole Chain. -/
inductive AnswerCopy : GalilScaffoldTape.Tape → GalilScaffoldCounter.Counter →
    ℕ → GalilScaffoldTape.Tape → GalilScaffoldCounter.Counter → Prop
  | stop (t) (c) : AnswerCopy t c 0 t c
  | next {t c n u d} (one : t.focus = 8) (legal : t.left ≠ [])
      (rest : AnswerCopy (GalilScaffoldTape.moveLeft t)
        (GalilScaffoldCounter.inc c) n u d) : AnswerCopy t c (n+1) u d

theorem answer_copy_exact (h n k : ℕ) (t : GalilScaffoldTape.Tape)
    (hout : GalilScaffoldTape.denote t = GalilDpCounters.output h)
    (hpos : GalilScaffoldTape.head t = n) (hn : n ≤ h) :
    ∃ u, AnswerCopy t (GalilScaffoldCounter.ofNat k) n u
      (GalilScaffoldCounter.ofNat (k+n)) ∧
      GalilScaffoldTape.denote u = GalilDpCounters.output h ∧
      GalilScaffoldTape.head u = 0 ∧ u.focus = 4 := by
  induction n generalizing t k with
  | zero =>
    refine ⟨t, ?_, hout, hpos, ?_⟩
    · simpa using AnswerCopy.stop t (GalilScaffoldCounter.ofNat k)
    · rw [← GalilScaffoldTape.focus_eq, hpos, hout]
      simp [GalilDpCounters.output]
  | succ n ih =>
    have hp : 0 < GalilScaffoldTape.head t := by omega
    have hm : GalilScaffoldTape.head (GalilScaffoldTape.moveLeft t) = n := by
      rw [GalilScaffoldTape.left_head t hp, hpos]; omega
    obtain ⟨u, hr, hu, hz, hf⟩ := ih (k+1) (GalilScaffoldTape.moveLeft t)
      (by rw [GalilScaffoldTape.left_denote, hout]) hm (by omega)
    refine ⟨u, ?_, hu, hz, hf⟩
    apply AnswerCopy.next
    · rw [← GalilScaffoldTape.focus_eq, hpos, hout]
      simp [GalilDpCounters.output, hn]
    · exact (GalilScaffoldTape.left_legal t).mpr hp
    · simpa [GalilScaffoldCounter.inc_ofNat, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hr

theorem answer_copy_done (h : ℕ) (hh : 0 < h) (t : GalilScaffoldTape.Tape)
    (hout : GalilScaffoldTape.denote t = GalilDpCounters.output h)
    (hpos : GalilScaffoldTape.head t = h) :
    ∃ u, AnswerCopy t GalilScaffoldCounter.reset h u (GalilScaffoldCounter.ofNat h) ∧
      u.focus = 4 ∧ GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat h) = true := by
  obtain ⟨u, hr, _, _, hf⟩ := answer_copy_exact h h 0 t hout hpos (Nat.le_refl h)
  refine ⟨u, ?_, hf, ?_⟩
  · simpa [GalilScaffoldCounter.ofNat, GalilScaffoldCounter.reset] using hr
  · apply (GalilScaffoldCounter.positive_iff _ (GalilScaffoldCounter.ofNat_canonical h)).mpr
    rw [GalilScaffoldCounter.ofNat_value]
    exact_mod_cast hh

/-- The same OUTPUT/h execution with the actual left-then-read walker order.
The symbol list is the sequence to be written to period, not a period tape. -/
inductive CopyWalk : GalilScaffoldTape.Tape → GalilScaffoldCounter.Counter →
    GalilScaffoldPlace.Place → ℕ → GalilScaffoldTape.Tape →
    GalilScaffoldCounter.Counter → GalilScaffoldPlace.Place → List (Fin 3) → Prop
  | stop (t c p) : CopyWalk t c p 0 t c p []
  | next {t c p n u d q xs} (a : Fin 3)
      (one : t.focus = 8) (legal : t.left ≠ [])
      (present : GalilScaffoldPlace.read (GalilScaffoldPlace.left p) = some a)
      (rest : CopyWalk (GalilScaffoldTape.moveLeft t) (GalilScaffoldCounter.inc c)
        (GalilScaffoldPlace.left p) n u d q xs) :
      CopyWalk t c p (n+1) u d q (a :: xs)

theorem copy_walk {t c n u d} (hr : AnswerCopy t c n u d)
    (p : GalilScaffoldPlace.Place) (hp : n < (GalilScaffoldPlace.stream p).length) :
    ∃ q xs, CopyWalk t c p n u d q xs ∧
      xs = ((GalilScaffoldPlace.stream p).drop 1).take n ∧
      GalilScaffoldPlace.stream q = (GalilScaffoldPlace.stream p).drop n := by
  induction hr generalizing p with
  | stop t c => exact ⟨p, [], CopyWalk.stop t c p, by simp, by simp⟩
  | @next t c n u d one legal rest ih =>
    have hlen : n < (GalilScaffoldPlace.stream (GalilScaffoldPlace.left p)).length := by
      rw [GalilScaffoldPlace.left_stream, List.length_tail]; omega
    obtain ⟨q, xs, hrun, hxs, hq⟩ := ih (GalilScaffoldPlace.left p) hlen
    have hne : GalilScaffoldPlace.stream (GalilScaffoldPlace.left p) ≠ [] := by
      intro he; simp [he] at hlen
    cases he : GalilScaffoldPlace.stream (GalilScaffoldPlace.left p) with
    | nil => exact False.elim (hne he)
    | cons a as =>
      have ha : GalilScaffoldPlace.read (GalilScaffoldPlace.left p) = some a := by
        rw [GalilScaffoldPlace.read_stream, he]; rfl
      refine ⟨q, a :: xs, CopyWalk.next a one legal ha hrun, ?_, ?_⟩
      · rw [hxs, he]
        have ht : (GalilScaffoldPlace.stream p).drop 1 = a :: as := by
          simpa [GalilScaffoldPlace.left_stream] using he
        simp [ht]
      · rw [hq]
        simp [GalilScaffoldPlace.left_stream]

/-- Connect the very same found DP run to the synchronized OUTPUT/h/walker
copy. The window-layout equality remains an explicit online invariant. -/
theorem found_copy_walk {s t : State} {x y : Machine 12} {as : List Bool}
    {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    ∃ h u q xs, GalilDpCorrect.Candidate w lower h ∧
      CopyWalk (y.config.tapes 11) GalilScaffoldCounter.reset p h u
        (GalilScaffoldCounter.ofNat h) q xs ∧
      u.focus = 4 ∧ GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat h) = true ∧
      xs = ((GalilScaffoldPlace.stream p).drop 1).take h ∧
      GalilScaffoldPlace.stream q = (GalilScaffoldPlace.stream p).drop h := by
  obtain ⟨h, hc, _, hout, hpos, _, _⟩ := found_output hr hs ht hv
  have hh : 0 < h := by have := hc.1; omega
  obtain ⟨u, ha, hf, hpositive⟩ := answer_copy_done h hh (y.config.tapes 11) hout hpos
  have hlen : h < (GalilScaffoldPlace.stream p).length := by
    have hb := hc.2.1
    rw [hw, List.length_take] at hb
    omega
  obtain ⟨q, xs, hcopy, hxs, hq⟩ := copy_walk ha p hlen
  exact ⟨h, u, q, xs, hc, hcopy, hf, hpositive, hxs, hq⟩

#print axioms found_copy_walk
#print axioms copy_walk
#print axioms answer_copy_done
#print axioms answer_copy_exact
#print axioms found_output
end PalPeg.GalilScaffoldChainAnswer
