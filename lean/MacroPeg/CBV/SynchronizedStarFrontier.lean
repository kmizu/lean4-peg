import MacroPeg.CBV.DelimitedRepeatEvaluation

/-! Exact stopping positions for conjunctions of synchronized consuming
steps. `maximum` is a calculation on actual evaluator results, not a PEG
expression or an assumed grammar closure operation. -/
namespace Shallot.MacroPeg.CBV.SynchronizedStarFrontier

def maximum : List Res → Res
  | [] => some (some 0)
  | r::rs => match r,maximum rs with
    | some (some p),some (some q) => some (some (max p q))
    | _,_ => none

def loops (fs : List (Nat → Res)) (p : Nat) : Res :=
  maximum (fs.map (fun f => evStar f p))

theorem maximum_bound (rs : List Res) (p : Nat)
    (hb : ∀ r∈rs, ∃ q, q≤p ∧ r=some (some q)) :
    ∃ q, q≤p ∧ maximum rs=some (some q) := by
  induction rs with
  | nil => exact ⟨0,Nat.zero_le _,rfl⟩
  | cons r rs ih =>
    obtain ⟨q,hq,rfl⟩ := hb r (by simp)
    obtain ⟨t,ht,he⟩ := ih (fun s hs => hb s (by simp [hs]))
    exact ⟨max q t,Nat.max_le.mpr ⟨hq,ht⟩,by simp [maximum,he]⟩

theorem maximum_attained (rs : List Res) (p : Nat)
    (hb : ∀ r∈rs, ∃ q, q≤p ∧ r=some (some q))
    (hm : some (some p)∈rs) : maximum rs=some (some p) := by
  induction rs with
  | nil => simp at hm
  | cons r rs ih =>
    obtain ⟨q,hq,rfl⟩ := hb r (by simp)
    rcases List.mem_cons.mp hm with he|hm
    · have he : p=q := by simpa using he
      subst q
      obtain ⟨t,ht,he⟩ := maximum_bound rs p (fun s hs => hb s (by simp [hs]))
      simp [maximum,he,Nat.max_eq_left ht]
    · have he := ih (fun s hs => hb s (by simp [hs])) hm
      simp [maximum,he,Nat.max_eq_right hq]

theorem loops_bound (fs : List (Nat → Res)) (limit p : Nat) (hp : p≤limit)
    (ht : ∀ f∈fs, ∀ q, q≤limit → ∃ r, f q=some r)
    (hprogress : ∀ f∈fs, ∀ q, q≤limit → ∀ r, f q=some (some r) → r<q) :
    ∃ q, q≤p ∧ loops fs p=some (some q) := by
  apply maximum_bound
  intro r hr
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hr
  obtain ⟨q,hq,he⟩ := DelimitedRepeatEvaluation.star_total f limit (ht f hf) (hprogress f hf) p hp
  exact ⟨q,hq,he⟩

/-- The simultaneous step succeeds at exactly the common endpoint, and
fails exactly when at least one component step fails. All premises refer
to one step; the conclusion computes the entire unbounded greedy loop. -/
theorem star_maximum (f : Nat → Res) (fs : List (Nat → Res)) (hne : fs≠[])
    (limit : Nat) (ht : ∀ p, p≤limit → ∃ r, f p=some r)
    (hcomponents : ∀ g∈fs, ∀ p, p≤limit → ∃ r, g p=some r)
    (hprogress : ∀ g∈fs, ∀ p, p≤limit → ∀ q, g p=some (some q) → q<p)
    (hok : ∀ p, p≤limit → ∀ q, f p=some (some q) ↔ ∀ g∈fs, g p=some (some q))
    (hfail : ∀ p, p≤limit → (f p=some none ↔ ∃ g∈fs, g p=some none)) :
    ∀ p, p≤limit → evStar f p=loops fs p := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp
    obtain ⟨r,hr⟩ := ht p hp
    cases r with
    | none =>
      obtain ⟨g,hg,hgf⟩ := (hfail p hp).mp hr
      have hm : evStar g p=some (some p) := evStar_fail hgf
      rw [evStar_fail hr]
      symm
      apply maximum_attained
      · intro r hmem
        obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hmem
        obtain ⟨q,hq,he⟩ := DelimitedRepeatEvaluation.star_total g limit
          (hcomponents g hg) (hprogress g hg) p hp
        exact ⟨q,hq,he⟩
      · exact List.mem_map.mpr ⟨g,hg,hm⟩
    | some q =>
      have hall := (hok p hp q).mp hr
      obtain ⟨g,hg⟩ := List.exists_mem_of_ne_nil fs hne
      have hq := hprogress g hg p hp q (hall g hg)
      rw [evStar_ok hr hq,ih q hq (by omega)]
      unfold loops
      congr 1
      apply List.map_congr_left
      intro g hg
      exact (evStar_ok (hall g hg) hq).symm

end Shallot.MacroPeg.CBV.SynchronizedStarFrontier
