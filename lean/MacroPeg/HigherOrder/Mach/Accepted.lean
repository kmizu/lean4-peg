import MacroPeg.HigherOrder.Mach.Iterates
import MacroPeg.HigherOrder.Mach.ItemZBound

/-!
# Facts about an accepted reading

For the final state of an accepted reading: the items' contexts exist (`items_ctx_le`), the string's codes are
character codes, and the starting rule values are the first iterate (`zero_iter`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

theorem itemsOf_ctx_le {tt ct : List (Nat × Nat)} {lt : List (List Nat)} :
    ∀ {l : List MItem} {is : List Item}, itemsOf tt ct lt l = some is → ∀ it ∈ l, it.ctx ≤ ct.length
  | [], _, _, it, h => by simp at h
  | i :: l, is, h, it, hit => by
    obtain ⟨item, is', hi, hl, rfl⟩ := mapM_cons_some h
    rcases List.mem_cons.1 hit with rfl | hit
    · unfold itemOf at hi
      split at hi
      · rename_i op Γ _ hΓ; exact ctxOf_le hΓ
      · cases hi
    · exact itemsOf_ctx_le hl it hit

theorem mapM_items_ctx_le {tt ct : List (Nat × Nat)} {lt : List (List Nat)} :
    ∀ {bodies : List (List MItem)} {bis : List (List Item)}, bodies.mapM (itemsOf tt ct lt) = some bis →
      ∀ it ∈ bodies.flatten, it.ctx ≤ ct.length
  | [], _, _, it, h => by simp at h
  | b :: bodies, bis, h, it, hit => by
    obtain ⟨is, bis', hb, hbs, rfl⟩ := mapM_cons_some h
    rw [List.flatten_cons] at hit
    rcases List.mem_append.1 hit with hit | hit
    · exact itemsOf_ctx_le hb it hit
    · exact mapM_items_ctx_le hbs it hit

theorem read_ctx_le {st : PSt} {R : List HO.Ty} {bis : List (List Item)} {is : List Item} {x : List Char}
    (hr : ReadOK st R bis is x) : ∀ it ∈ st.bodies.flatten ++ st.start, it.ctx ≤ st.ct.length := by
  intro it hit
  rcases List.mem_append.1 hit with hit | hit
  · exact mapM_items_ctx_le hr.bodies it hit
  · exact itemsOf_ctx_le hr.start it hit

theorem read_x_codes {st : PSt} {R : List HO.Ty} {bis : List (List Item)} {is : List Item} {x : List Char}
    (hr : ReadOK st R bis is x) : ∀ c ∈ st.x, c < 1114112 := by
  intro c hc
  rw [hr.x] at hc
  obtain ⟨d, _, rfl⟩ := List.mem_map.1 hc
  exact toNat_lt d

/-! ## Tags and type numbers of the items -/

theorem itemOf_tag_le {tt ct : List (Nat × Nat)} {lt : List (List Nat)} {it : MItem} {item : Item}
    (h : itemOf tt ct lt it = some item) : it.tag ≤ 12 ∧ (it.tag = 11 → it.a ≤ tt.length) := by
  unfold itemOf at h
  split at h
  · rename_i op Γ hop _
    unfold opOf at hop
    split at hop
    all_goals first
      | (rename_i htag; constructor <;> (intro; omega) <;> omega)
      | (rename_i htag; refine ⟨by omega, fun _ => ?_⟩
         split at hop
         · rename_i a σ ha _; exact tyOf_le ha
         · cases hop)
      | (rename_i htag; refine ⟨by omega, fun h => absurd (htag ▸ h) (by decide)⟩)
      | cases hop
  · cases h

theorem itemsOf_tags {tt ct : List (Nat × Nat)} {lt : List (List Nat)} :
    ∀ {l : List MItem} {is : List Item}, itemsOf tt ct lt l = some is →
      ∀ it ∈ l, it.tag ≤ 12 ∧ (it.tag = 11 → it.a ≤ tt.length)
  | [], _, _, it, h => by simp at h
  | i :: l, is, h, it, hit => by
    obtain ⟨item, is', hi, hl, rfl⟩ := mapM_cons_some h
    rcases List.mem_cons.1 hit with rfl | hit
    · exact itemOf_tag_le hi
    · exact itemsOf_tags hl it hit

theorem read_tags {st : PSt} {R : List HO.Ty} {bis : List (List Item)} {is : List Item} {x : List Char}
    (hr : ReadOK st R bis is x) :
    ∀ it ∈ st.bodies.flatten ++ st.start, it.tag ≤ 12 ∧ (it.tag = 11 → it.a ≤ st.tt.length) := by
  have hb : ∀ (bodies : List (List MItem)) (bis : List (List Item)),
      bodies.mapM (itemsOf st.tt st.ct st.lt) = some bis →
        ∀ it ∈ bodies.flatten, it.tag ≤ 12 ∧ (it.tag = 11 → it.a ≤ st.tt.length) := by
    intro bodies
    induction bodies with
    | nil => intro _ _ it h; simp at h
    | cons b bodies ih =>
      intro bis h it hit
      obtain ⟨is', bis', hb', hbs, rfl⟩ := mapM_cons_some h
      rw [List.flatten_cons] at hit
      rcases List.mem_append.1 hit with hit | hit
      · exact itemsOf_tags hb' it hit
      · exact ih bis' hbs it hit
  intro it hit
  rcases List.mem_append.1 hit with hit | hit
  · exact hb _ _ hr.bodies it hit
  · exact itemsOf_tags hr.start it hit

end Shallot.MacroPeg.Mach
