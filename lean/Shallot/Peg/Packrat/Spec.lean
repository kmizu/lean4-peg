import Shallot.Peg.Packrat.Defs
import Shallot.Peg.Soundness
import Shallot.Peg.Completeness
import Shallot.Peg.Props

/-!
# Agreement with the fuel interpreter

A round of the table corresponds to a level of fuel in the tree-producing
interpreter. Positions and consumed lengths replace suffixes and trees.
No termination assumption on the grammar is needed.
-/

namespace Shallot.Packrat

/-- Erase the tree, retaining failure or the number of consumed characters. -/
def erase (input : List Char) : Outcome → Res
  | .fail => none
  | .ok _ rest => some (input.length - rest.length)

/-- A successful run returns exactly the suffix indexed by its consumption. -/
theorem run_rest {g : Grammar} {n : Nat} {e : PExp} {x rest : List Char}
    {i : Nat} {t : PTree} (h : pegRun g n e (x.drop i) = some (.ok t rest)) :
    x.drop (i + ((x.drop i).length - rest.length)) = rest ∧
      rest.length ≤ (x.drop i).length := by
  obtain ⟨p, hp⟩ := derives_suffix (pegRun_sound h) t rest rfl
  constructor
  · rw [← List.drop_drop, hp]
    simp
  · rw [hp, List.length_append]
    omega

private theorem literal_length : ∀ (s x r : List Char),
    stripPrefix? s x = some r → x.length = s.length + r.length
  | [], x, r, h => by simp [stripPrefix?] at h; subst r; simp
  | _ :: _, [], _, h => by simp [stripPrefix?] at h
  | c :: cs, d :: ds, r, h => by
    simp only [stripPrefix?] at h
    split at h
    · have := literal_length cs ds r h
      simp only [List.length_cons]
      omega
    · cases h

/-- Every round agrees exactly with the interpreter at the same fuel. -/
theorem iter_eq_run (g : Grammar) (x : List Char) (n : Nat) (e : PExp) (i : Nat) :
    iter g x n e i = (pegRun g n e (x.drop i)).map (erase (x.drop i)) := by
  induction n generalizing e i with
  | zero => simp [iter, pegRun]
  | succ n ih =>
    rw [iter, pegRun.eq_def]
    cases e with
    | eps => simp [F, erase]
    | any =>
      simp only [F]
      cases hx : x.drop i with
      | nil =>
        have hi : x.length ≤ i := List.drop_eq_nil_iff.mp hx
        simp [Nat.not_lt.mpr hi, erase]
      | cons c rest =>
        have hi : i < x.length := by
          have hd : (x.drop i).length = x.length - i := List.length_drop
          rw [hx] at hd
          simp only [List.length_cons] at hd
          omega
        simp [hi, erase]
    | chr c =>
      simp only [F]
      have hx : x[i]? = (x.drop i).head? := (List.head?_drop).symm
      rw [hx]
      cases x.drop i with
      | nil => simp [erase]
      | cons d rest => cases h : beqChar c d <;> simp [h, erase]
    | range lo hi =>
      simp only [F]
      have hx : x[i]? = (x.drop i).head? := (List.head?_drop).symm
      rw [hx]
      cases x.drop i with
      | nil => simp [erase]
      | cons d rest => cases h : (leChar lo d && leChar d hi) <;> simp [h, erase]
    | lit s =>
      simp only [F]
      cases hs : stripPrefix? s (x.drop i) with
      | none => simp [erase]
      | some rest =>
        have hlen := literal_length s (x.drop i) rest hs
        simp [erase, hlen]
    | nt j =>
      simp only [F]
      cases hr : ruleAt g.rules j with
      | none => simp [erase]
      | some b =>
        dsimp only
        rw [ih]
        cases pegRun g n b (x.drop i) with
        | none => rfl
        | some o => cases o <;> rfl
    | seq a b =>
      simp only [F, ih]
      cases ha : pegRun g n a (x.drop i) with
      | none => rfl
      | some oa =>
        cases oa with
        | fail => rfl
        | ok ta rest =>
          obtain ⟨hr, hle⟩ := run_rest ha
          simp only [Option.map_some, erase, hr]
          cases hb : pegRun g n b rest with
          | none => rfl
          | some ob =>
            cases ob with
            | fail => rfl
            | ok tb rest' =>
              obtain ⟨p, hp⟩ := derives_suffix (pegRun_sound hb) tb rest' rfl
              have hle' : rest'.length ≤ rest.length := by
                rw [hp, List.length_append]; omega
              simp only [Option.map_some, erase, Option.some.injEq]
              omega
    | alt a b =>
      simp only [F, ih]
      cases ha : pegRun g n a (x.drop i) with
      | none => rfl
      | some oa =>
        cases oa with
        | ok t rest => rfl
        | fail =>
          cases pegRun g n b (x.drop i) with
          | none => rfl
          | some ob => cases ob <;> rfl
    | star a =>
      simp only [F, ih]
      cases ha : pegRun g n a (x.drop i) with
      | none => rfl
      | some oa =>
        cases oa with
        | fail => simp [erase]
        | ok ta rest =>
          obtain ⟨hr, hle⟩ := run_rest ha
          simp only [Option.map_some, erase, hr]
          cases hb : pegRun g n (.star a) rest with
          | none => rfl
          | some ob =>
            cases ob with
            | fail => exact False.elim (starNeverFails (pegRun_sound hb) rfl)
            | ok tb rest' =>
              obtain ⟨p, hp⟩ := derives_suffix (pegRun_sound hb) tb rest' rfl
              have hle' : rest'.length ≤ rest.length := by
                rw [hp, List.length_append]; omega
              simp only [Option.map_some, erase, Option.some.injEq]
              omega
    | notP a =>
      simp only [F, ih]
      cases pegRun g n a (x.drop i) with
      | none => rfl
      | some o => cases o <;> simp [erase]

/-- A filled entry has a derivation with exactly the recorded result. -/
theorem iter_sound {g : Grammar} {x : List Char} {n : Nat} {e : PExp}
    {i : Nat} {r : Res} (h : iter g x n e i = some r) :
    ∃ o, Derives g e (x.drop i) o ∧ erase (x.drop i) o = r := by
  rw [iter_eq_run] at h
  cases hr : pegRun g n e (x.drop i) with
  | none => simp [hr] at h
  | some o =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    exact ⟨o, pegRun_sound hr, h⟩

/-- Every derivation eventually fills its table entry. -/
theorem iter_complete {g : Grammar} {x : List Char} {e : PExp} {i : Nat}
    {o : Outcome} (h : Derives g e (x.drop i) o) :
    ∃ n, iter g x n e i = some (erase (x.drop i) o) := by
  obtain ⟨n, hn⟩ := pegRun_complete h
  exact ⟨n, by rw [iter_eq_run, hn]; rfl⟩

/-- Once filled, an entry never changes. -/
theorem iter_mono {g : Grammar} {x : List Char} {n m : Nat} {e : PExp}
    {i : Nat} {r : Res} (h : iter g x n e i = some r) (hnm : n ≤ m) :
    iter g x m e i = some r := by
  rw [iter_eq_run] at h ⊢
  cases hr : pegRun g n e (x.drop i) with
  | none => simp [hr] at h
  | some o =>
    rw [pegRun_mono_le hnm hr]
    simpa only [hr] using h

/-- Recorded consumption stays within the input, including at its end. -/
theorem iter_consumption {g : Grammar} {x : List Char} {n : Nat} {e : PExp}
    {i k : Nat} (h : iter g x n e i = some (some k)) : k ≤ (x.drop i).length := by
  obtain ⟨o, hd, he⟩ := iter_sound h
  cases o with
  | fail => cases he
  | ok t rest =>
    simp only [erase, Option.some.injEq] at he
    omega

end Shallot.Packrat
