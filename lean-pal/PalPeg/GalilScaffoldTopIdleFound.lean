import PalPeg.GalilScaffoldTopSegmentFacts

/-!
# The found tick after a chain-idle segment

From `Search.start(lower)` at a fresh match clock, a chain-idle segment
followed by a tick whose search step lands in `found`: either that tick is
the end of the first search stage — the DP result holds on the found
program, the search was in `run` just before, and the candidate semiperiod
exists (the entry of `found_life`) — or the first stage already halted
within the segment in a non-`found` exit mode (a later stage's `found`;
its analysis is the lower layer's `later_stage_chain`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem map_fst_map_pair (av : List Bool) :
    ((av.map (fun b => (b, true))).map Prod.fst) = av := by
  induction av with
  | nil => rfl
  | cons b av ih => simp [ih]

theorem advances_replicate_false (delay : ℕ) (m : ℕ) : ∀ clock : ℕ,
    GalilScaffoldAdvanceClock.advances delay clock (List.replicate m (false, true)) =
      List.replicate m false := by
  induction m with
  | zero => intro clock; rfl
  | succ m ih => intro clock; simp [List.replicate_succ, GalilScaffoldAdvanceClock.advances, ih]

theorem idle_segment_found_first (P : Shared) (qq : ℕ) (first : Fin 9)
    (hplace : ∀ u v : GalilVM, u.center = v.center → P.place u = P.place v)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {c0 : Control} {r : GalilVM} (hcl : c0.clock = 2048) (hplr : P.place r = ⟨a :: ls,gap⟩)
    (hcen : r.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (lower radius : Counter) (hlc : Canonical lower) (k : ℕ) (hk : value lower = k)
    (hrc : Canonical radius) (rad : ℕ) (hrad : value radius = rad) (hr : 3*rad ≤ 5*k)
    (hsearch : r.search = GalilScaffoldSearchFinish.begin lower radius) (hlower : r.lower = lower)
    {es1 : List Bool} {c1 : Control} {s1 : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r c1 s1) (hs1 : s1.chain = .idle)
    (aF : Bool) (hclock1 : aF = true → c1.clock = 1) (vq : SearchVM)
    (hstep : searchStep (P.place s1) aF (searchLens.get s1) vq)
    (hfound : vq.search.mode = .found) :
    ((∃ dpv, vq.dp = ⟨dpv, true⟩ ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k 0
          (GalilScaffoldProgram.denote dpv)) ∧
      s1.search.mode = .run ∧
      (∀ (rad' : Counter), Canonical rad' → ∀ (r0 : ℕ), value rad' = r0 → 0 < r0 → ∀ (sm dm : Bool),
        ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
          GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k h ∧
          ys.length+1 = h)) ∨
    (∃ (L : ℕ) (vL : SearchVM), L ≤ es1.length ∧
      SearchRun ⟨a :: ls,gap⟩ (es1.take L) (searchLens.get r) vL ∧
      vL.search.mode ≠ .run ∧ vL.search.mode ≠ .found) := by
  -- the search's run over the segment and the found tick
  have hrunSeg := watchSegE_searchRun P qq first 2048 hplace hseg hs1
  rw [hplr] at hrunSeg
  have hcen1 : s1.center = r.center := watchSegE_center P qq first 2048 hseg
  rw [hplace s1 r hcen1, hplr] at hstep
  -- the events
  obtain ⟨av1, hav1, hes1, hcl1, _⟩ := watchSegE_clock P qq first 2048 hseg
  rw [hcl] at hes1 hcl1
  -- the padded run
  obtain ⟨m, hm⟩ : ∃ m, max k 1 + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) = m := ⟨_, rfl⟩
  have hpad : SearchRun ⟨a :: ls,gap⟩ (List.replicate m false) vq vq :=
    searchRun_pad _ m vq (Or.inl hfound)
  have hrunF : SearchRun ⟨a :: ls,gap⟩ (es1 ++ [aF]) (searchLens.get r) vq := by
    rw [← List.singleton_append] at hpad
    exact searchRun_append hrunSeg (.cons hstep (.nil _))
  have hrunAll : SearchRun ⟨a :: ls,gap⟩ ((es1 ++ [aF]) ++ List.replicate m false) (searchLens.get r) vq :=
    searchRun_append hrunF hpad
  -- the events of the padded run are advances from the fresh clock
  have hadv : (es1 ++ [aF]) ++ List.replicate m false =
      GalilScaffoldAdvanceClock.advances 2048 2048
        ((av1 ++ aF :: List.replicate m false).map (fun b => (b, true))) := by
    rw [List.map_append, GalilScaffoldAdvanceClock.advances_append, map_fst_map_pair, ← hcl1, ← hes1,
      List.append_assoc]
    congr 1
    simp only [List.map_cons, GalilScaffoldAdvanceClock.advances, List.singleton_append, List.map_replicate]
    congr 1
    · cases aF
      · rfl
      · rw [hclock1 rfl]; rfl
    · exact (advances_replicate_false 2048 m _).symm
  have hlen : max k 1 + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) ≤ ((es1 ++ [aF]) ++ List.replicate m false).length := by
    rw [hm]; simp only [List.length_append, List.length_replicate, List.length_singleton]; omega
  obtain ⟨as, bs, usedQ, rest, v1, v2, v3, hsplit, has, hbs, h1, h2, h3, _, hm0, hw0, hp, hm1, hw1, hl1,
      hm2, hq, hm3, _, ⟨dpv, hdp, hres⟩, hcand⟩ :=
    search_first_stage a ls rs q gap r.center hcen c hc lower radius hlc k hk hrc rad hrad hr hrunAll
      hsearch hlower (by simp [hav1]) hadv hlen
  have hU : SearchRun ⟨a :: ls,gap⟩ (as ++ bs ++ usedQ) (searchLens.get r) v3 :=
    searchRun_append (searchRun_append h1 h2) h3
  obtain ⟨L, hL⟩ : ∃ L, (as ++ bs ++ usedQ).length = L := ⟨_, rfl⟩
  have hUlen : 1 ≤ L := by
    rw [← hL]; simp only [List.length_append]; omega
  have hprefixU : as ++ bs ++ usedQ = ((es1 ++ [aF]) ++ List.replicate m false).take L := by
    rw [hsplit, ← hL, List.take_left]
  have hlenF : (es1 ++ [aF]).length = es1.length + 1 := by simp
  rcases Nat.lt_trichotomy L (es1.length + 1) with hlt | heq | hgt
  · -- the first stage halted inside the segment
    right
    have hL' : L ≤ es1.length := by omega
    have hUes : as ++ bs ++ usedQ = es1.take L := by
      rw [hprefixU, List.append_assoc, List.take_append_of_le_length hL']
    refine ⟨L, v3, hL', by rw [← hUes]; exact hU, hm3, ?_⟩
    have hsplit1 : es1 = (as ++ bs ++ usedQ) ++ es1.drop L := by
      have := List.take_append_drop L es1
      rw [← hUes] at this
      exact this.symm
    exact watchSegE_search_not_found P qq first 2048 hplace hseg hs1 _ _ v3 hsplit1
      (by intro h0; rw [h0] at hL; simp at hL; omega) (by rw [hplr]; exact hU)
  · -- the found tick ends the first stage
    left
    have hUes : as ++ bs ++ usedQ = es1 ++ [aF] := by
      rw [hprefixU, heq, ← hlenF, List.take_left]
    have hv3 : v3 = vq := by
      rw [hUes] at hU
      exact searchRun_unique hU hrunF
    subst hv3
    refine ⟨⟨dpv, hdp, hres⟩, ?_, hcand hfound⟩
    have := stage_prefix_mode ⟨a :: ls,gap⟩ k h1 h2 h3 hm0 hw0 hp hm1 hw1 hl1 hm2 hq hm3 es1 [aF]
      (searchLens.get s1) hUes (by simp) hrunSeg
    exact this.2 rfl
  · -- impossible: the search would not yet be found
    exfalso
    have hF : es1 ++ [aF] = (as ++ bs ++ usedQ).take (es1.length + 1) := by
      rw [hprefixU, List.take_take, Nat.min_eq_left (by omega), ← hlenF, List.take_left]
    have hsplitU : as ++ bs ++ usedQ = (es1 ++ [aF]) ++ (as ++ bs ++ usedQ).drop (es1.length + 1) := by
      have := List.take_append_drop (es1.length + 1) (as ++ bs ++ usedQ)
      rw [← hF] at this
      exact this.symm
    have hne : (as ++ bs ++ usedQ).drop (es1.length + 1) ≠ [] := by
      intro h0
      have := congrArg List.length h0
      rw [List.length_drop, hL] at this
      simp only [List.length_nil] at this
      omega
    have := stage_prefix_mode ⟨a :: ls,gap⟩ k h1 h2 h3 hm0 hw0 hp hm1 hw1 hl1 hm2 hq hm3 _ _ vq hsplitU hne hrunF
    exact this.1 hfound

#print axioms idle_segment_found_first

end PalPeg.GalilScaffoldChainInputSupply
