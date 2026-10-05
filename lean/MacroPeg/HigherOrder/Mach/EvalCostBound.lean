import MacroPeg.HigherOrder.Mach.Accepted

/-!
# The steps of the evaluation

On an accepted reading, the rule values of every round have the same lengths, so the sizes `pushBound` and `evalW`
are the same in every round (`pushBound_congr`, `evalW_congr`); the rounds end in an iterate (`fixT_iter`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

theorem flatten_length_congr {Tf Tf' : List (List Nat)} (h : Tf.map List.length = Tf'.map List.length) :
    Tf.flatten.length = Tf'.flatten.length := by
  simp only [List.length_flatten, h]

theorem pushBound_congr {j cap : Nat} {x : List Char} {tt ct : List (Nat × Nat)} {Tf Tf' : List (List Nat)}
    (h : Tf.map List.length = Tf'.map List.length) : pushBound j cap x tt ct Tf = pushBound j cap x tt ct Tf' := by
  simp only [pushBound, flatten_length_congr h]

theorem evalW_congr {j cap : Nat} {st : PSt} {Tf Tf' : List (List Nat)}
    (h : Tf.map List.length = Tf'.map List.length) : evalW j cap st Tf = evalW j cap st Tf' := by
  have hl : Tf.length = Tf'.length := by
    have := congrArg List.length h; simpa using this
  simp only [evalW, flatten_length_congr h, hl, pushBound_congr h]

section Accepted

variable {j cap : Nat} {g : HGrammar} {bis : List (List Item)} {is : List Item} {st : PSt} (G : TGrammar g.types)

/-- **The rounds end in an iterate.** -/
theorem fixT_iter (hr : ReadOK st g.types bis is (st.x.map Char.ofNat)) (hbis : bodyItems G.bodies = bis)
    (hit : ∀ it ∈ st.bodies.flatten, ItemOK j cap st.tt st.ct it) :
    ∀ fuel m, ∃ m', fixT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies fuel
      (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G m)) =
        envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G m')
  | 0, m => ⟨m, rfl⟩
  | fuel + 1, m => by
    rw [fixT, roundT_iter G hr hbis hit m]
    split
    · exact ⟨m, rfl⟩
    · exact fixT_iter hr hbis hit fuel (m + 1)

/-- The lengths of an iterate: those of the rule types. -/
theorem iter_lengths (x : List Char) (m : Nat) :
    (envFlat x.length (iter x G m)).map List.length = g.types.map (valSize x.length) :=
  envFlat_lengths x.length (iter_mem x G m)

end Accepted

/-! ## Sums over the bodies -/

theorem sum_map_le_lin {α : Type} (f : α → Nat) (len : α → Nat) (c d : Nat) :
    ∀ (L : List α), (∀ l ∈ L, f l ≤ c * len l + d) → (L.map f).sum ≤ c * (L.map len).sum + d * L.length
  | [], _ => by simp
  | l :: L, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h₁ := h l List.mem_cons_self
    have h₂ := sum_map_le_lin f len c d L (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    rw [Nat.mul_add, Nat.mul_succ]
    omega

theorem bodies_items_le (bodies : List (List MItem)) :
    (bodies.map List.length).sum + bodies.length ≤ (encBodies bodies).length := by
  induction bodies with
  | nil => simp [encBodies]
  | cons b bodies ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, encBodies, List.flatMap_cons,
      List.length_append] at ih ⊢
    have : b.length ≤ (encItems b).length := by
      simp only [encItems, List.length_flatMap, encItem, List.length_cons, List.length_nil]
      induction b with
      | nil => simp
      | cons i b ihb => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
    omega



/-! ## One round -/

theorem pow5_mono {a b : Nat} (h : a ≤ b) : a * a * a * a * a ≤ b * b * b * b * b :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h h) h) h) h

section Round

variable {j cap : Nat} {g : HGrammar} {bis : List (List Item)} {is : List Item} {st : PSt} (G : TGrammar g.types)

/-- The cost of an item, on the stacks of a round. -/
def itemK (j cap : Nat) (st : PSt) (T0 : List (List Nat)) : Nat :=
  let Y := (st.x.length + 1114116) * (2 * ((encBodies st.bodies).length + (encItems st.start).length) *
      pushBound j cap (st.x.map Char.ofNat) st.tt st.ct T0 + evalW j cap st T0)
  1000 * (Y * Y * Y * Y * Y)

/-- **One round costs at most this**, whatever iterate it starts from. -/
theorem roundCost_iter_le (hr : ReadOK st g.types bis is (st.x.map Char.ofNat)) (hbis : bodyItems G.bodies = bis)
    (hit : ∀ it ∈ st.bodies.flatten, ItemOK j cap st.tt st.ct it) (hx : ∀ c ∈ st.x, c < 1114112) (hlt : LtOK st)
    (m : Nat) :
    roundCost j cap st (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G m)) ≤
      (itemK j cap st (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0)) + 600 +
        100 * pushBound j cap (st.x.map Char.ofNat) st.tt st.ct
          (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0))) *
        (encBodies st.bodies).length + 100 * (encBodies st.bodies).length +
      100 * ((encBodies st.bodies).length +
        (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0)).flatten.length +
        (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0)).length +
        (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0)).flatten.length *
          (st.x.length + 2) + 1) := by
  have hxl : (st.x.map Char.ofNat).length = st.x.length := by simp
  -- the iterates and their sizes
  obtain ⟨Tm, hTm⟩ : ∃ T, T = envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G m) := ⟨_, rfl⟩
  obtain ⟨T0, hT0⟩ : ∃ T, T = envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0) := ⟨_, rfl⟩
  rw [← hTm, ← hT0]
  have hlen : Tm.map List.length = T0.map List.length := by rw [hTm, hT0, iter_lengths, iter_lengths]
  have hpB := pushBound_congr (j := j) (cap := cap) (x := st.x.map Char.ofNat) (tt := st.tt) (ct := st.ct) hlen
  have hW := evalW_congr (j := j) (cap := cap) (st := st) hlen
  have hfl := flatten_length_congr hlen
  have hl : Tm.length = T0.length := by have := congrArg List.length hlen; simpa using this
  have hsm : ∀ f ∈ Tm, Small (st.x.length + 2) f := by
    rw [hTm, ← hxl]; exact envFlat_small _ (iter_mem _ G m)
  have hsum := sum_le_of_small (flatten_small hsm)
  have hctx := read_ctx_le hr
  -- the items of a body cost at most `itemK`
  obtain ⟨E, hE⟩ : ∃ E, E = (encBodies st.bodies).length := ⟨_, rfl⟩
  obtain ⟨pB, hpB0⟩ : ∃ p, p = pushBound j cap (st.x.map Char.ofNat) st.tt st.ct T0 := ⟨_, rfl⟩
  have hbody : ∀ l ∈ st.bodies,
      runCost j cap st Tm l [] + 100 * (l.length + (evFlat (runT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tm l
        [])).length + 1) ≤ (itemK j cap st T0 + 600 + 100 * pB) * l.length + 100 := by
    intro l hlb
    have hlE : l.length ≤ E := by
      have := bodies_items_le st.bodies
      have := le_sum_of_mem (List.mem_map.2 ⟨l, hlb, rfl⟩ : l.length ∈ st.bodies.map List.length)
      omega
    have hlctx : ∀ it ∈ l, it.ctx ≤ st.ct.length :=
      fun it hi => hctx it (List.mem_append_left _ (List.mem_flatten.2 ⟨l, hlb, hi⟩))
    have hrun := runT_bounded (j := j) (cap := cap) (x := st.x.map Char.ofNat) (lt := st.lt) hr.tt hr.ct
      (by rw [hxl]; exact hsm) l hlctx [] (by simp)
    have hcost := runCost_le (j := j) (cap := cap) st hr.tt hr.ct hsm (itemK j cap st T0) l []
      ((E + (encItems st.start).length) * pB) hlctx (by simp)
      (by
        simp only [evFlat, List.reverse_nil, List.flatten_nil, List.length_nil, Nat.zero_add]
        rw [hpB, ← hpB0]; exact Nat.mul_le_mul_right _ (by omega))
      (fun it hi vs' hvs' hsm' => by
        have hz := itemZ_le (j := j) (cap := cap) (Tf := Tm) hr.tt hr.ct (hlctx it hi)
          (List.mem_append_left _ (List.mem_flatten.2 ⟨l, hlb, hi⟩)) hsm' hvs' hsm hx hlt
        rw [hW] at hz
        unfold itemCost itemK
        simp only []
        refine Nat.mul_le_mul_left _ (pow5_mono (Nat.le_trans hz ?_))
        rw [← hpB0, ← hE]
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_of_eq (Nat.mul_assoc _ _ _).symm) _))
    rw [hpB, ← hpB0] at hrun
    have := hrun.1
    rw [show (evFlat ([] : List (List Nat))).length = 0 from rfl, Nat.zero_add] at this
    have h₁ : l.length * pB ≤ pB * l.length := Nat.le_of_eq (Nat.mul_comm _ _)
    rw [Nat.add_mul, Nat.add_mul]
    have h₂ : 100 * pB * l.length = 100 * (pB * l.length) := Nat.mul_assoc _ _ _
    have h₃ : l.length * (itemK j cap st T0 + 500) = itemK j cap st T0 * l.length + 500 * l.length := by
      rw [Nat.mul_comm, Nat.add_mul]
    omega
  have h₁ := sum_map_le_lin _ List.length _ 100 st.bodies hbody
  have h₂ := bodies_items_le st.bodies
  have h₃ : (itemK j cap st T0 + 600 + 100 * pB) * (st.bodies.map List.length).sum ≤
      (itemK j cap st T0 + 600 + 100 * pB) * E := Nat.mul_le_mul_left _ (by omega)
  unfold roundCost
  rw [hfl, hl, ← hE]
  have h₄ : Tm.flatten.sum ≤ T0.flatten.length * (st.x.length + 2) := by rw [← hfl]; exact hsum
  rw [← hpB0]
  omega

end Round

/-! ## The whole evaluation -/

section Whole

variable {j cap : Nat} {g : HGrammar} {bis : List (List Item)} {is : List Item} {st : PSt} (G : TGrammar g.types)

theorem valT_rt (hrt : ∀ t ∈ st.rt, need j cap st.tt t) :
    st.rt.map (valT j cap st.x.length st.tt) = st.rt.map (valNum st.x.length st.tt) :=
  List.map_congr_left (fun t ht => valT_eq t (hrt t ht))

/-- The starting rule values are the first iterate. -/
theorem zero_iter (hr : ReadOK st g.types bis is (st.x.map Char.ofNat)) (hrt : ∀ t ∈ st.rt, need j cap st.tt t) :
    st.rt.map (fun t => List.replicate (valT j cap (st.x.map Char.ofNat).length st.tt t) 0) =
      envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0) := by
  have hxl : (st.x.map Char.ofNat).length = st.x.length := by simp
  rw [show iter (st.x.map Char.ofNat) G 0 = Env.bot _ g.types from rfl, envFlat_bot]
  obtain ⟨_, h₂⟩ := valNum_sum (x := st.x.map Char.ofNat) hr.tt hr.rt
  rw [← h₂, hxl]
  exact List.map_congr_left (fun t ht => by rw [valT_eq t (hrt t ht)])

theorem encItems_length (l : List MItem) : (encItems l).length = 4 * l.length := by
  induction l with
  | nil => simp [encItems]
  | cons i l ih => simp only [encItems, List.flatMap_cons, List.length_append, encItem] at ih ⊢; simp [ih]; omega

theorem items_le_enc (l : List MItem) : l.length ≤ (encItems l).length := by rw [encItems_length]; omega

/-- The sizes in the bound on the evaluation, for starting rule values `T0`. -/
def evFuel (j cap : Nat) (st : PSt) : Nat := (st.rt.map (valT j cap st.x.length st.tt)).sum + 1
def evPB (j cap : Nat) (st : PSt) (T0 : List (List Nat)) : Nat :=
  pushBound j cap (st.x.map Char.ofNat) st.tt st.ct T0
def evR (j cap : Nat) (st : PSt) (T0 : List (List Nat)) : Nat :=
  (itemK j cap st T0 + 600 + 100 * evPB j cap st T0) * (encBodies st.bodies).length +
    100 * (encBodies st.bodies).length +
    100 * ((encBodies st.bodies).length + T0.flatten.length + T0.length + T0.flatten.length * (st.x.length + 2) + 1)
def evZ (j cap : Nat) (st : PSt) (T0 : List (List Nat)) : Nat :=
  evFuel j cap st + st.rt.length + T0.flatten.length + (valTable j cap st.x.length st.tt).sum +
    (encItems st.start).length + (encItems st.start).length * evPB j cap st T0 + st.x.length + st.tt.length + 2
def evBound (j cap : Nat) (st : PSt) (T0 : List (List Nat)) : Nat :=
  1000 * evZ j cap st T0 * evZ j cap st T0 + (evFuel j cap st + 1) * (evR j cap st T0 + 1) +
    (encItems st.start).length * (itemK j cap st T0 + 500)

/-- **The whole evaluation costs at most `evBound`.** -/
theorem evalCost_le (hr : ReadOK st g.types bis is (st.x.map Char.ofNat)) (hbis : bodyItems G.bodies = bis)
    (hit : ∀ it ∈ st.bodies.flatten ++ st.start, ItemOK j cap st.tt st.ct it)
    (hrt : ∀ t ∈ st.rt, need j cap st.tt t) (hx : ∀ c ∈ st.x, c < 1114112) (hlt : LtOK st) :
    evalCost j cap st ≤
      evBound j cap st (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0)) := by
  have hxl : (st.x.map Char.ofNat).length = st.x.length := by simp
  obtain ⟨T0, hT0⟩ : ∃ T, T = envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G 0) := ⟨_, rfl⟩
  rw [← hT0]
  have hb : ∀ it ∈ st.bodies.flatten, ItemOK j cap st.tt st.ct it := fun it h => hit it (List.mem_append_left _ h)
  have hz := zero_iter G hr hrt
  rw [← hT0] at hz
  -- the rounds
  have hround := fun m => roundCost_iter_le G hr hbis hb hx hlt m
  rw [← hT0] at hround
  have hfix := fixCost_le G hr hbis hb (evR j cap st T0) (fun m => hround m)
    ((st.rt.map (valT j cap (st.x.map Char.ofNat).length st.tt)).sum + 1) 0
  rw [← hT0] at hfix
  -- where the rounds end
  obtain ⟨m', hm'⟩ := fixT_iter G hr hbis hb ((st.rt.map (valT j cap (st.x.map Char.ofNat).length st.tt)).sum + 1) 0
  rw [← hT0] at hm'
  obtain ⟨Tm, hTm⟩ : ∃ T, T = envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G m') := ⟨_, rfl⟩
  rw [← hTm] at hm'
  have hlen : Tm.map List.length = T0.map List.length := by rw [hTm, hT0, iter_lengths, iter_lengths]
  have hpB := pushBound_congr (j := j) (cap := cap) (x := st.x.map Char.ofNat) (tt := st.tt) (ct := st.ct) hlen
  have hW := evalW_congr (j := j) (cap := cap) (st := st) hlen
  have hsm : ∀ f ∈ Tm, Small (st.x.length + 2) f := by
    rw [hTm, ← hxl]; exact envFlat_small _ (iter_mem _ G m')
  have hctx := read_ctx_le hr
  have hsctx : ∀ it ∈ st.start, it.ctx ≤ st.ct.length := fun it h => hctx it (List.mem_append_right _ h)
  have hSs : st.start.length ≤ (encItems st.start).length := items_le_enc st.start
  -- the start
  have hrun := runT_bounded (j := j) (cap := cap) (x := st.x.map Char.ofNat) (lt := st.lt) hr.tt hr.ct
    (by rw [hxl]; exact hsm) st.start hsctx [] (by simp)
  rw [show (evFlat ([] : List (List Nat))).length = 0 from rfl, Nat.zero_add, hpB] at hrun
  have hstart := runCost_le (j := j) (cap := cap) st hr.tt hr.ct hsm (itemK j cap st T0) st.start []
    (((encBodies st.bodies).length + (encItems st.start).length) * evPB j cap st T0) hsctx (by simp)
    (by
      rw [show (evFlat ([] : List (List Nat))).length = 0 from rfl, Nat.zero_add, hpB]
      exact Nat.mul_le_mul_right _ (by omega))
    (fun it hi vs' hvs' hsm' => by
      have hz' := itemZ_le (j := j) (cap := cap) (Tf := Tm) hr.tt hr.ct (hsctx it hi)
        (List.mem_append_right _ hi) hsm' hvs' hsm hx hlt
      rw [hW] at hz'
      unfold itemCost itemK
      simp only []
      refine Nat.mul_le_mul_left _ (pow5_mono (Nat.le_trans hz' ?_))
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_of_eq (Nat.mul_assoc _ _ _).symm) _))
  have hev : (evFlat (runT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tm st.start [])).length ≤
      (encItems st.start).length * evPB j cap st T0 :=
    Nat.le_trans hrun.1 (Nat.mul_le_mul_right _ hSs)
  -- putting it together
  unfold evalCost
  simp only []
  rw [hz, hm']
  have hZ : (st.rt.map (valT j cap (st.x.map Char.ofNat).length st.tt)).sum + 1 + st.rt.length +
      T0.flatten.length + (valTable j cap (st.x.map Char.ofNat).length st.tt).sum + (encItems st.start).length +
      (evFlat (runT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tm st.start [])).length +
      (st.x.map Char.ofNat).length + st.tt.length + 2 ≤ evZ j cap st T0 := by
    unfold evZ evFuel; rw [hxl]; omega
  have hZZ : 1000 * _ * _ ≤ 1000 * evZ j cap st T0 * evZ j cap st T0 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hZ) hZ
  have hS' : st.start.length * (itemK j cap st T0 + 500) ≤
      (encItems st.start).length * (itemK j cap st T0 + 500) := Nat.mul_le_mul_right _ hSs
  unfold evBound
  rw [show evFuel j cap st = (st.rt.map (valT j cap (st.x.map Char.ofNat).length st.tt)).sum + 1 by
    unfold evFuel; rw [hxl]]
  exact Nat.add_le_add (Nat.add_le_add hZZ hfix) (Nat.le_trans hstart hS')

end Whole

end Shallot.MacroPeg.Mach
