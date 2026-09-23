import PalPeg.ScaTyped

/-!
# Multi-stack machines compile to scaffold automata

A *multi-stack machine* has a finite control and `K` stacks over a finite alphabet. On each input
letter it sees the top `D` cells of every stack and replaces every stack `k` by
`pre ++ (stack src).drop drop` for a bounded `pre` (length `≤ E`), a source stack `src` (or the
empty stack) and a bounded `drop` (`≤ D`). Stacks may be shared, copied or discarded in one step.

We compile such a machine into a scaffold automaton over finite types (`ScaTyped.Typed`), which
recognizes its language in Kim–Park's sense.

## Encoding

One scaffold node per input letter. The label of the node created at a step records, for each
stack `k`, the cells pushed at that step (`≤ E` of them) and a *tail descriptor*
`Option (Fin K × Fin (E + 1))`: `some (k', j)` means "continue with the cells of stack `k'` of the
node reached by edge `k`, starting at cell `j`". The descriptor always points *into* the cells of
the target node (`j < length`), so each edge hop yields at least one element. Edge `k` of a node
(`Fin.castSucc k`) is the tail pointer of stack `k`; edge `K` is unused (it keeps the degree
positive when `K = 0`). The radius is `D + 1`: `D` hops read the top `D` cells, and `D + 1` hops
locate the cell where the stack continues after dropping `≤ D` cells.

The meaning of a stack is the relation `Den` (by induction on the hop chain), and `StackRep`
relates the top node of the scaffold with the machine's stacks. The automaton reads labels
through `lookupAt`, which agrees with `Scaffold.follow` on short paths (`agrees_top`).
-/
set_option autoImplicit false
namespace PalPeg.ScaStackMachine
open PegSeparation PegSeparation.Scaffolding

/-! ## The machine -/

/-- How one stack is replaced in a step: push `pre` (top first) on top of stack `src` with its top
`drop` cells removed (`src = none` means the empty stack). -/
structure Rewrite (Γ : Type) (K : ℕ) where
  pre : List Γ
  src : Option (Fin K)
  drop : ℕ

/-- A real-time multi-stack machine reading `Fin 2`. It sees the top `D` cells of every stack. -/
structure StackMachine (Γ C : Type) (K E D : ℕ) where
  init : C
  accept : C → Bool
  step : C → Fin 2 → (Fin K → List Γ) → C × (Fin K → Rewrite Γ K)
  pre_le : ∀ c a v k, ((step c a v).2 k).pre.length ≤ E
  drop_le : ∀ c a v k, ((step c a v).2 k).drop ≤ D

/-- The stack produced by a rewrite from the current stacks. -/
def apply {Γ : Type} {K : ℕ} (st : Fin K → List Γ) (r : Rewrite Γ K) : List Γ :=
  r.pre ++ (match r.src with
    | none => []
    | some i => (st i).drop r.drop)

namespace StackMachine

variable {Γ C : Type} {K E D : ℕ}

/-- One input letter: the machine sees only the top `D` cells of each stack. -/
def stepCfg (M : StackMachine Γ C K E D) (cfg : C × (Fin K → List Γ)) (a : Fin 2) :
    C × (Fin K → List Γ) :=
  let out := M.step cfg.1 a (fun k => (cfg.2 k).take D)
  (out.1, fun k => apply cfg.2 (out.2 k))

def run (M : StackMachine Γ C K E D) (w : List (Fin 2)) : C × (Fin K → List Γ) :=
  w.foldl M.stepCfg (M.init, fun _ => [])

def Accepts (M : StackMachine Γ C K E D) (w : List (Fin 2)) : Prop :=
  M.accept (M.run w).1 = true

end StackMachine

/-! ## Reading a neighborhood by paths -/

section Paths

variable {L : Type} {deg : ℕ}

/-- The label (if a node is there) at a path inside a neighborhood. -/
def lookupAt : (r : ℕ) → Neighborhood L deg r → List (Fin deg) → Option (Option L)
  | 0, m, [] => some (m : Option L)
  | 0, _, _ :: _ => none
  | _ + 1, m, [] => some m.1
  | r + 1, m, d :: ds => (m.2 d).bind (fun m' => lookupAt r m' ds)

/-- The label of the node at position `p` (outer `none`: no node there). -/
def labelAt (nodes : List (Node L deg)) (p : ℕ) : Option (Option L) :=
  nodes[p]?.map Node.label

/-- The offset of edge `d` of the node at position `p`. -/
def edgeAt (nodes : List (Node L deg)) (p : ℕ) (d : Fin deg) : Option ℕ :=
  nodes[p]?.bind (fun node => node.edgeOffset d)

theorem lookupAt_neighborhoodAt (nodes : List (Node L deg)) :
    ∀ (r p : ℕ) (ds : List (Fin deg)), ds.length ≤ r →
      (Scaffold.neighborhoodAt nodes r p).bind (fun m => lookupAt r m ds)
        = (Scaffold.follow nodes p ds).bind (labelAt nodes)
  | 0, p, [], _ => by
    simp only [Scaffold.neighborhoodAt, Scaffold.follow, labelAt]
    cases hn : nodes[p]? <;> simp [hn, lookupAt]
  | 0, _, _ :: _, h => by simp at h
  | r + 1, p, [], _ => by
    simp only [Scaffold.neighborhoodAt, Scaffold.follow, labelAt]
    cases hn : nodes[p]? <;> simp [hn, lookupAt]
  | r + 1, p, d :: ds, h => by
    simp only [Scaffold.neighborhoodAt, Scaffold.follow]
    cases hn : nodes[p]? with
    | none => rfl
    | some node =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, lookupAt]
      cases he : node.edgeOffset d with
      | none => rfl
      | some off =>
        simp only [Option.bind_some]
        exact lookupAt_neighborhoodAt nodes r (p + off) ds (by simpa using h)

theorem neighborhoodAt_zero (s : Scaffold L deg) :
    ∀ r, Scaffold.neighborhoodAt s.nodes r 0 = some (s.topNeighborhood r)
  | 0 => by simp [Scaffold.neighborhoodAt, Scaffold.topNeighborhood, Scaffold.nodes]
  | r + 1 => by simp [Scaffold.neighborhoodAt, Scaffold.topNeighborhood, Scaffold.nodes]

/-- Reading the top neighborhood by paths agrees with following edges in the scaffold. -/
theorem agrees_top (s : Scaffold L deg) (r : ℕ) (ds : List (Fin deg)) (h : ds.length ≤ r) :
    lookupAt r (s.topNeighborhood r) ds = (Scaffold.follow s.nodes 0 ds).bind (labelAt s.nodes) := by
  have := lookupAt_neighborhoodAt s.nodes r 0 ds h
  rwa [neighborhoodAt_zero, Option.bind_some] at this

/-- A path reader `g` agrees with the scaffold `nodes` on paths of length `≤ R`. -/
def Agrees (g : List (Fin deg) → Option (Option L)) (nodes : List (Node L deg)) (R : ℕ) : Prop :=
  ∀ ds : List (Fin deg), ds.length ≤ R → g ds = (Scaffold.follow nodes 0 ds).bind (labelAt nodes)

theorem follow_append (nodes : List (Node L deg)) :
    ∀ (p : ℕ) (ds es : List (Fin deg)),
      Scaffold.follow nodes p (ds ++ es) = (Scaffold.follow nodes p ds).bind
        (fun q => Scaffold.follow nodes q es)
  | p, [], es => by
    simp only [List.nil_append, Scaffold.follow]
    cases hp : nodes[p]? with
    | none =>
      cases es with
      | nil => simp [Scaffold.follow, hp]
      | cons e es => simp [Scaffold.follow, hp]
    | some node => rfl
  | p, d :: ds, es => by
    simp only [List.cons_append, Scaffold.follow, Option.bind_eq_bind]
    cases nodes[p]? with
    | none => rfl
    | some node =>
      simp only [Option.bind_some]
      cases node.edgeOffset d with
      | none => rfl
      | some off => simp only [Option.bind_some]; exact follow_append nodes (p + off) ds es

theorem follow_nil_of_labelAt (nodes : List (Node L deg)) (p : ℕ) (x : Option L)
    (h : labelAt nodes p = some x) : Scaffold.follow nodes p [] = some p := by
  simp only [labelAt, Option.map_eq_some_iff] at h
  obtain ⟨node, hn, -⟩ := h
  simp [Scaffold.follow, hn]

theorem follow_snoc (nodes : List (Node L deg)) (ds : List (Fin deg)) (p off : ℕ) (d : Fin deg)
    (x : Option L) (hf : Scaffold.follow nodes 0 ds = some p) (he : edgeAt nodes p d = some off)
    (hl : labelAt nodes (p + off) = some x) :
    Scaffold.follow nodes 0 (ds ++ [d]) = some (p + off) := by
  rw [follow_append, hf, Option.bind_some]
  simp only [edgeAt, Option.bind_eq_some_iff] at he
  obtain ⟨node, hn, he⟩ := he
  simp only [Scaffold.follow, Option.bind_eq_bind, hn, Option.bind_some, he]
  exact follow_nil_of_labelAt nodes (p + off) x hl

theorem follow_zero_nil (s : Scaffold L deg) : Scaffold.follow s.nodes 0 [] = some 0 := by
  simp [Scaffold.follow, Scaffold.nodes]

theorem labelAt_zero (s : Scaffold L deg) : labelAt s.nodes 0 = some s.top.label := by
  simp [labelAt, Scaffold.nodes]

theorem Agrees.nil {g : List (Fin deg) → Option (Option L)} {s : Scaffold L deg} {R : ℕ}
    (hg : Agrees g s.nodes R) : g [] = some s.top.label := by
  rw [hg [] (Nat.zero_le _), follow_zero_nil, Option.bind_some, labelAt_zero]

theorem labelAt_cons_succ (fresh : Node L deg) (nodes : List (Node L deg)) (p : ℕ) :
    labelAt (fresh :: nodes) (p + 1) = labelAt nodes p := by
  simp [labelAt]

theorem edgeAt_cons_succ (fresh : Node L deg) (nodes : List (Node L deg)) (p : ℕ) (d : Fin deg) :
    edgeAt (fresh :: nodes) (p + 1) d = edgeAt nodes p d := by
  simp [edgeAt]

end Paths

/-! ## Labels -/

/-- A bounded list of cells. -/
structure Cells (Γ : Type) (E : ℕ) where
  val : List Γ
  le : val.length ≤ E

instance instFiniteCells {Γ : Type} [Finite Γ] {E : ℕ} : Finite (Cells Γ E) :=
  haveI := (List.finite_length_le Γ E).to_subtype
  Finite.of_injective
    (fun c : Cells Γ E => (⟨c.val, c.le⟩ : ↥{l : List Γ | l.length ≤ E}))
    (by
      intro x y h
      cases x; cases y
      simp only [Subtype.mk.injEq] at h
      subst h
      rfl)

/-- What a node records about one stack: its newly pushed cells and the tail descriptor. -/
abbrev Seg (Γ : Type) (K E : ℕ) := Cells Γ E × Option (Fin K × Fin (E + 1))

/-- A node label: one segment per stack. -/
abbrev Lab (Γ : Type) (K E : ℕ) := Fin K → Seg Γ K E

/-- Edge `k` carries the tail pointer of stack `k`. -/
def edge {K : ℕ} (k : Fin K) : Fin (K + 1) := k.castSucc

variable {Γ : Type} {K E : ℕ}

/-! ## Denotation of stacks -/

/-- `Den nodes p k t`: the tail of stack `k` at the node at position `p` denotes `t`. Each hop
lands inside the cells of its target, so it contributes at least one element. -/
inductive Den (nodes : List (Node (Lab Γ K E) (K + 1))) : ℕ → Fin K → List Γ → Prop
  | stop {p : ℕ} {k : Fin K} {lab : Lab Γ K E} :
      labelAt nodes p = some (some lab) → (lab k).2 = none → Den nodes p k []
  | hop {p off : ℕ} {k k' : Fin K} {j : Fin (E + 1)} {lab lab' : Lab Γ K E} {t : List Γ} :
      labelAt nodes p = some (some lab) → (lab k).2 = some (k', j) →
      edgeAt nodes p (edge k) = some off → labelAt nodes (p + off) = some (some lab') →
      j.val < (lab' k').1.val.length → Den nodes (p + off) k' t →
      Den nodes p k ((lab' k').1.val.drop j.val ++ t)

theorem Den.labelAt_isSome {nodes : List (Node (Lab Γ K E) (K + 1))} {p : ℕ} {k : Fin K}
    {t : List Γ} (h : Den nodes p k t) : ∃ lab, labelAt nodes p = some (some lab) := by
  cases h with
  | stop hl _ => exact ⟨_, hl⟩
  | hop hl _ _ _ _ _ => exact ⟨_, hl⟩

/-- Pushing a fresh node shifts every position by one. -/
theorem Den.shift {nodes : List (Node (Lab Γ K E) (K + 1))} (fresh : Node (Lab Γ K E) (K + 1))
    {p : ℕ} {k : Fin K} {t : List Γ} (h : Den nodes p k t) : Den (fresh :: nodes) (p + 1) k t := by
  induction h with
  | stop hl ht => exact .stop (by rwa [labelAt_cons_succ]) ht
  | @hop p off k k' j lab lab' t hl ht he hl' hj _ ih =>
    have hidx : p + 1 + off = p + off + 1 := by omega
    refine .hop (off := off) (by rwa [labelAt_cons_succ]) ht (by rwa [edgeAt_cons_succ]) ?_ hj ?_
    · rw [hidx, labelAt_cons_succ]; exact hl'
    · rw [hidx]; exact ih

/-- The machine's stack `k` is represented at the top of the scaffold. -/
def StackRep (s : Scaffold (Lab Γ K E) (K + 1)) (k : Fin K) (l : List Γ) : Prop :=
  match s.top.label with
  | none => l = []
  | some lab => ∃ t, Den s.nodes 0 k t ∧ l = (lab k).1.val ++ t

/-! ## Reading the top of a stack -/

section Read

variable (g : List (Fin (K + 1)) → Option (Option (Lab Γ K E)))

/-- Read up to `n` cells of the tail of stack `k` at the node at path `ds`. -/
def readTail : ℕ → List (Fin (K + 1)) → Fin K → ℕ → List Γ
  | 0, _, _, _ => []
  | _ + 1, _, _, 0 => []
  | fuel + 1, ds, k, n + 1 =>
    match g ds with
    | some (some lab) =>
      match (lab k).2 with
      | some (k', j) =>
        match g (ds ++ [edge k]) with
        | some (some lab') =>
          ((lab' k').1.val.drop j.val).take (n + 1) ++
            readTail fuel (ds ++ [edge k]) k' (n + 1 - ((lab' k').1.val.drop j.val).length)
        | _ => []
      | none => []
    | _ => []

/-- Locate the `d`-th cell of the tail of stack `k` at the node at path `ds`: the path to the
node holding it, the stack there, and the cell index. `none`: the tail has `≤ d` cells. -/
def locateTail : ℕ → List (Fin (K + 1)) → Fin K → ℕ → Option (List (Fin (K + 1)) × Fin K × ℕ)
  | 0, _, _, _ => none
  | fuel + 1, ds, k, d =>
    match g ds with
    | some (some lab) =>
      match (lab k).2 with
      | some (k', j) =>
        match g (ds ++ [edge k]) with
        | some (some lab') =>
          if d < ((lab' k').1.val.drop j.val).length then some (ds ++ [edge k], k', j.val + d)
          else locateTail fuel (ds ++ [edge k]) k' (d - ((lab' k').1.val.drop j.val).length)
        | _ => none
      | none => none
    | _ => none

/-- The cells of stack `k` recorded at the top node. -/
def topCells (k : Fin K) : List Γ :=
  match g [] with
  | some (some lab) => (lab k).1.val
  | _ => []

/-- The top `D` cells of stack `k`. -/
def view (D : ℕ) (k : Fin K) : List Γ :=
  (topCells g k).take D ++ readTail g D [] k (D - (topCells g k).length)

/-- Locate the `dr`-th cell of stack `i` (from the top). -/
def locateTop (D : ℕ) (i : Fin K) (dr : ℕ) : Option (List (Fin (K + 1)) × Fin K × ℕ) :=
  match g [] with
  | some (some lab) =>
    if dr < (lab i).1.val.length then some ([], i, dr)
    else locateTail g (D + 1) [] i (dr - (lab i).1.val.length)
  | _ => none

end Read

theorem readTail_of_none {g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))}
    (fuel : ℕ) (ds : List (Fin (K + 1))) (k : Fin K) (n : ℕ) (h : g ds = some none) :
    readTail g fuel ds k n = [] := by
  rcases fuel with _ | fuel <;> rcases n with _ | n <;> simp [readTail, h]

theorem readTail_eq {nodes : List (Node (Lab Γ K E) (K + 1))}
    {g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))} {R : ℕ} (hg : Agrees g nodes R)
    {p : ℕ} {k : Fin K} {t : List Γ} (hd : Den nodes p k t) :
    ∀ (fuel : ℕ) (ds : List (Fin (K + 1))) (n : ℕ), Scaffold.follow nodes 0 ds = some p →
      n ≤ fuel → ds.length + n ≤ R → readTail g fuel ds k n = t.take n := by
  induction hd with
  | @stop p k lab hl ht =>
    intro fuel ds n hf hn hR
    rcases n with _ | n
    · rcases fuel with _ | fuel <;> simp [readTail]
    rcases fuel with _ | fuel
    · omega
    have hg1 : g ds = some (some lab) := by
      rw [hg ds (by omega), hf, Option.bind_some]; exact hl
    simp [readTail, hg1, ht]
  | @hop p off k k' j lab lab' t hl ht he hl' hj _ ih =>
    intro fuel ds n hf hn hR
    rcases n with _ | n
    · rcases fuel with _ | fuel <;> simp [readTail]
    rcases fuel with _ | fuel
    · omega
    have hg1 : g ds = some (some lab) := by
      rw [hg ds (by omega), hf, Option.bind_some]; exact hl
    have hf2 : Scaffold.follow nodes 0 (ds ++ [edge k]) = some (p + off) :=
      follow_snoc nodes ds p off (edge k) _ hf he hl'
    have hg2 : g (ds ++ [edge k]) = some (some lab') := by
      rw [hg _ (by simp; omega), hf2, Option.bind_some]; exact hl'
    have hlen : 1 ≤ ((lab' k').1.val.drop j.val).length := by simp; omega
    simp only [readTail, hg1, ht, hg2]
    rw [ih fuel (ds ++ [edge k]) _ hf2 (by omega) (by simp; omega), List.take_append]

/-- A pointer: cell `j` of stack `k` at the node at position `q`, followed by that stack's
tail, denotes `l`. -/
def Ptr (nodes : List (Node (Lab Γ K E) (K + 1))) (q : ℕ) (k : Fin K) (j : ℕ) (l : List Γ) :
    Prop :=
  ∃ (lab : Lab Γ K E) (t : List Γ), labelAt nodes q = some (some lab) ∧
    j < (lab k).1.val.length ∧ Den nodes q k t ∧ l = (lab k).1.val.drop j ++ t

/-- The result of a location for dropping `d` cells of `l` is correct. -/
def LocOK (nodes : List (Node (Lab Γ K E) (K + 1))) (R : ℕ) (l : List Γ) (d : ℕ) :
    Option (List (Fin (K + 1)) × Fin K × ℕ) → Prop
  | none => l.length ≤ d
  | some (ds, k', j) => ds.length ≤ R ∧
      ∃ q, Scaffold.follow nodes 0 ds = some q ∧ Ptr nodes q k' j (l.drop d)

theorem LocOK.append {nodes : List (Node (Lab Γ K E) (K + 1))} {R : ℕ} {l : List Γ} {d : ℕ}
    {res : Option (List (Fin (K + 1)) × Fin K × ℕ)} (c : List Γ) (hc : c.length ≤ d)
    (h : LocOK nodes R l (d - c.length) res) : LocOK nodes R (c ++ l) d res := by
  rcases res with _ | ⟨ds, k', j⟩
  · simp only [LocOK, List.length_append] at h ⊢
    omega
  · simp only [LocOK] at h ⊢
    rwa [List.drop_append, List.drop_eq_nil_of_le hc, List.nil_append]

theorem locateTail_ok {nodes : List (Node (Lab Γ K E) (K + 1))}
    {g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))} {R : ℕ} (hg : Agrees g nodes R)
    {p : ℕ} {k : Fin K} {t : List Γ} (hd : Den nodes p k t) :
    ∀ (fuel : ℕ) (ds : List (Fin (K + 1))) (d : ℕ), Scaffold.follow nodes 0 ds = some p →
      d < fuel → ds.length + d + 1 ≤ R → LocOK nodes R t d (locateTail g fuel ds k d) := by
  induction hd with
  | @stop p k lab hl ht =>
    intro fuel ds d hf hdf hR
    rcases fuel with _ | fuel
    · omega
    have hg1 : g ds = some (some lab) := by
      rw [hg ds (by omega), hf, Option.bind_some]; exact hl
    simp [locateTail, hg1, ht, LocOK]
  | @hop p off k k' j lab lab' t hl ht he hl' hj hden ih =>
    intro fuel ds d hf hdf hR
    rcases fuel with _ | fuel
    · omega
    have hg1 : g ds = some (some lab) := by
      rw [hg ds (by omega), hf, Option.bind_some]; exact hl
    have hf2 : Scaffold.follow nodes 0 (ds ++ [edge k]) = some (p + off) :=
      follow_snoc nodes ds p off (edge k) _ hf he hl'
    have hg2 : g (ds ++ [edge k]) = some (some lab') := by
      rw [hg _ (by simp; omega), hf2, Option.bind_some]; exact hl'
    have hlen : 1 ≤ ((lab' k').1.val.drop j.val).length := by simp; omega
    simp only [locateTail, hg1, ht, hg2]
    split_ifs with hlt
    · refine ⟨by simp; omega, p + off, hf2, lab', t, hl', by simp at hlt; omega, hden, ?_⟩
      rw [List.drop_append_of_le_length hlt.le, List.drop_drop]
    · exact LocOK.append _ (by omega) (ih fuel _ _ hf2 (by omega) (by simp; omega))

theorem view_eq {D : ℕ} {s : Scaffold (Lab Γ K E) (K + 1)}
    {g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))} (hg : Agrees g s.nodes (D + 1))
    {k : Fin K} {l : List Γ} (h : StackRep s k l) : view g D k = l.take D := by
  have hg0 := hg.nil
  unfold StackRep at h
  cases hlab : s.top.label with
  | none =>
    rw [hlab] at h hg0
    subst h
    simp [view, topCells, hg0, readTail_of_none D [] k _ hg0]
  | some lab =>
    rw [hlab] at h hg0
    obtain ⟨t, hd, rfl⟩ := h
    simp only [view, topCells, hg0]
    rw [readTail_eq hg hd D [] _ (follow_zero_nil s) (Nat.sub_le _ _) (by simp; omega),
      List.take_append]

theorem locateTop_ok {D : ℕ} {s : Scaffold (Lab Γ K E) (K + 1)}
    {g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))} (hg : Agrees g s.nodes (D + 1))
    {i : Fin K} {l : List Γ} (h : StackRep s i l) {dr : ℕ} (hdr : dr ≤ D) :
    LocOK s.nodes (D + 1) l dr (locateTop g D i dr) := by
  have hg0 := hg.nil
  unfold StackRep at h
  cases hlab : s.top.label with
  | none =>
    rw [hlab] at h hg0
    subst h
    simp [locateTop, hg0, LocOK]
  | some lab =>
    rw [hlab] at h hg0
    obtain ⟨t, hd, rfl⟩ := h
    simp only [locateTop, hg0]
    split_ifs with hlt
    · refine ⟨by simp, 0, follow_zero_nil s, lab, t, ?_, hlt, hd, ?_⟩
      · rw [labelAt_zero, hlab]
      · rw [List.drop_append_of_le_length hlt.le]
    · exact LocOK.append _ (by omega)
        (locateTail_ok hg hd (D + 1) [] _ (follow_zero_nil s) (by omega) (by simp; omega))

/-! ## The compiled automaton -/

/-- Clamp a cell index into `Fin (E + 1)`. -/
def clampFin (E : ℕ) (j : ℕ) : Fin (E + 1) := ⟨min j E, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Store a list of at most `E` cells. -/
def encCells (E : ℕ) (l : List Γ) : Cells Γ E := ⟨l.take E, List.length_take_le _ _⟩

section Compile

variable {C : Type} {D : ℕ}

/-- Where the rewritten stack continues below its pushed cells. -/
def loc (D : ℕ) (g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))) (r : Rewrite Γ K) :
    Option (List (Fin (K + 1)) × Fin K × ℕ) :=
  r.src.bind (fun i => locateTop g D i r.drop)

/-- The new segment of the rewritten stack. -/
def newSeg (D : ℕ) (g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))) (r : Rewrite Γ K) :
    Seg Γ K E :=
  (encCells E r.pre, (loc D g r).map (fun x => (x.2.1, clampFin E x.2.2)))

/-- The edge target carrying the tail of the rewritten stack. -/
def tgt (D : ℕ) (g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))) (r : Rewrite Γ K) :
    LocalTarget (K + 1) (D + 1) :=
  match loc D g r with
  | none => .missing
  | some (ds, _, _) => if h : ds.length ≤ D + 1 then .path ds h else .missing

def targetFor (D : ℕ) (g : List (Fin (K + 1)) → Option (Option (Lab Γ K E)))
    (rw : Fin K → Rewrite Γ K) (e : Fin (K + 1)) : LocalTarget (K + 1) (D + 1) :=
  if h : e.val < K then tgt D g (rw ⟨e.val, h⟩) else .missing

/-- **The compiled scaffold automaton.** State: the control. Label: per-stack segments. -/
def toTyped (M : StackMachine Γ C K E D) : ScaTyped.Typed (Fin 2) C (Lab Γ K E) (K + 1) (D + 1)
    where
  degreePositive := Nat.succ_pos K
  initial := M.init
  accepting := M.accept
  transition c a n :=
    let g := lookupAt (D + 1) n
    let out := M.step c a (view g D)
    { nextState := out.1
      newLabel := fun k => newSeg D g (out.2 k)
      target := targetFor D g out.2 }

/-- The simulation relation. -/
def Rep (cfg : C × (Fin K → List Γ)) (x : C × Scaffold (Lab Γ K E) (K + 1)) : Prop :=
  x.1 = cfg.1 ∧ ∀ k, StackRep x.2 k (cfg.2 k)

theorem stackRep_extend (s : Scaffold (Lab Γ K E) (K + 1))
    {g : List (Fin (K + 1)) → Option (Option (Lab Γ K E))} (hg : Agrees g s.nodes (D + 1))
    {st : Fin K → List Γ} (hs : ∀ k, StackRep s k (st k)) (c : C) (rw : Fin K → Rewrite Γ K)
    (hpre : ∀ k, (rw k).pre.length ≤ E) (hdrop : ∀ k, (rw k).drop ≤ D) (k : Fin K) :
    StackRep (ScaTyped.Typed.extend s
      (⟨c, fun k => newSeg D g (rw k), targetFor D g rw⟩ :
        Action C (Lab Γ K E) (K + 1) (D + 1))) k (apply st (rw k)) := by
  set act : Action C (Lab Γ K E) (K + 1) (D + 1) :=
    ⟨c, fun k => newSeg D g (rw k), targetFor D g rw⟩ with hact
  set s' := ScaTyped.Typed.extend s act with hs'
  have hnodes : s'.nodes = s'.top :: s.nodes := rfl
  have hl0 : labelAt s'.nodes 0 = some (some act.newLabel) := rfl
  have hcells : (act.newLabel k).1.val = (rw k).pre := List.take_of_length_le (hpre k)
  have htarget : act.target (edge k) = tgt D g (rw k) := by
    simp [hact, targetFor, edge]
  unfold StackRep
  show ∃ t, Den s'.nodes 0 k t ∧ apply st (rw k) = (act.newLabel k).1.val ++ t
  rw [hcells]
  unfold apply
  cases hsrc : (rw k).src with
  | none =>
    refine ⟨[], .stop hl0 ?_, by simp⟩
    simp [hact, newSeg, loc, hsrc]
  | some i =>
    have hok := locateTop_ok hg (hs i) (hdrop k)
    cases hres : locateTop g D i (rw k).drop with
    | none =>
      rw [hres] at hok
      simp only [LocOK] at hok
      refine ⟨[], .stop hl0 ?_, by simp [List.drop_eq_nil_of_le hok]⟩
      simp [hact, newSeg, loc, hsrc, hres]
    | some res =>
      obtain ⟨ds, k', j⟩ := res
      rw [hres] at hok
      obtain ⟨hlen, q, hq, lab', t', hl', hj, hd', heq⟩ := hok
      have hjE : j ≤ E := by have := (lab' k').1.le; omega
      have hclamp : (clampFin E j).val = j := by simp [clampFin, hjE]
      have htgt : tgt D g (rw k) = .path ds hlen := by
        simp [tgt, loc, hsrc, hres, hlen]
      have hedge : edgeAt s'.nodes 0 (edge k) = some (q + 1) := by
        rw [hnodes]
        simp only [edgeAt, List.getElem?_cons_zero, Option.bind_some, hs', ScaTyped.Typed.extend]
        rw [htarget, htgt]
        simp [hq]
      refine ⟨_, .hop (off := q + 1) (k' := k') (j := clampFin E j) (lab' := lab') (t := t')
        hl0 ?_ hedge ?_ ?_ ?_, ?_⟩
      · simp [hact, newSeg, loc, hsrc, hres]
      · rw [Nat.zero_add, hnodes, labelAt_cons_succ]; exact hl'
      · rw [hclamp]; exact hj
      · rw [Nat.zero_add, hnodes]; exact hd'.shift _
      · simp only [heq, hclamp]

theorem step_rep (M : StackMachine Γ C K E D) {cfg : C × (Fin K → List Γ)}
    {x : C × Scaffold (Lab Γ K E) (K + 1)} (h : Rep cfg x) (a : Fin 2) :
    Rep (M.stepCfg cfg a) ((toTyped M).step x a) := by
  obtain ⟨c, st⟩ := cfg
  obtain ⟨c', s⟩ := x
  obtain ⟨hc, hs⟩ := h
  simp only at hc hs
  subst hc
  set g := lookupAt (D + 1) (s.topNeighborhood (D + 1)) with hgdef
  have hg : Agrees g s.nodes (D + 1) := fun ds hds => agrees_top s (D + 1) ds hds
  have hview : view g D = fun k => (st k).take D := funext fun k => view_eq hg (hs k)
  have hstep : (toTyped M).step (c', s) a =
      ((M.step c' a (view g D)).1,
        ScaTyped.Typed.extend s
          (⟨(M.step c' a (view g D)).1, fun k => newSeg D g ((M.step c' a (view g D)).2 k),
            targetFor D g (M.step c' a (view g D)).2⟩ :
            Action C (Lab Γ K E) (K + 1) (D + 1))) := rfl
  rw [hstep, hview]
  refine ⟨rfl, fun k => ?_⟩
  exact stackRep_extend s hg hs _ _ (fun k => M.pre_le _ _ _ k) (fun k => M.drop_le _ _ _ k) k

theorem init_rep (M : StackMachine Γ C K E D) :
    Rep (M.init, fun _ => []) ((toTyped M).initial,
      (⟨⟨none, fun _ => none⟩, []⟩ : Scaffold (Lab Γ K E) (K + 1))) :=
  ⟨rfl, fun _ => rfl⟩

theorem run_rep (M : StackMachine Γ C K E D) (w : List (Fin 2)) :
    Rep (M.run w) ((toTyped M).run w) := by
  unfold StackMachine.run ScaTyped.Typed.run
  suffices hsuff : ∀ (cfg : C × (Fin K → List Γ)) (x : C × Scaffold (Lab Γ K E) (K + 1)),
      Rep cfg x → Rep (w.foldl M.stepCfg cfg) (w.foldl (toTyped M).step x) from
    hsuff _ _ (init_rep M)
  induction w with
  | nil => intro cfg x h; exact h
  | cons a rest ih =>
    intro cfg x h
    simp only [List.foldl_cons]
    exact ih _ _ (step_rep M h a)

/-- **The compiled automaton accepts exactly what the machine accepts.** -/
theorem toTyped_accepts (M : StackMachine Γ C K E D) (w : List (Fin 2)) :
    (toTyped M).Accepts w ↔ M.Accepts w := by
  unfold ScaTyped.Typed.Accepts StackMachine.Accepts
  rw [(run_rep M w).1]
  rfl

/-- **Every multi-stack machine has an equivalent scaffold automaton over finite types.** -/
theorem exists_typed [Finite Γ] [Fintype C] (M : StackMachine Γ C K E D) :
    ∃ (S L : Type) (_ : Fintype S) (_ : Fintype L) (degree radius : ℕ)
      (A : ScaTyped.Typed (Fin 2) S L degree radius), ∀ w, A.Accepts w ↔ M.Accepts w :=
  ⟨C, Lab Γ K E, inferInstance, Fintype.ofFinite _, K + 1, D + 1, toTyped M, toTyped_accepts M⟩

/-- **A multi-stack machine's language is recognized by a scaffold automaton.** -/
theorem recognizedBySCA [Finite Γ] [Finite C] (M : StackMachine Γ C K E D) :
    RecognizedBySCA ({w | M.Accepts w} : Language (Fin 2)) := by
  haveI : Fintype C := Fintype.ofFinite C
  haveI : Fintype (Lab Γ K E) := Fintype.ofFinite _
  exact ScaTyped.Typed.recognizedBySCA (toTyped M) (fun w => (toTyped_accepts M w).trans Iff.rfl)

/-- **`PAL ∈ PEG` from a multi-stack machine recognizing `PAL`.** -/
theorem pal_in_peg_of_stackMachine [Finite Γ] [Finite C] (M : StackMachine Γ C K E D)
    (hM : ∀ w, M.Accepts w ↔ w ∈ PalPeg.PAL) : RecognizedByTotalPEG PalPeg.PAL := by
  haveI : Fintype C := Fintype.ofFinite C
  haveI : Fintype (Lab Γ K E) := Fintype.ofFinite _
  exact ScaTyped.pal_in_peg_of_typed (toTyped M) (fun w => (toTyped_accepts M w).trans (hM w))

end Compile

/-- info: 'PalPeg.ScaStackMachine.toTyped_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toTyped_accepts

/-- info: 'PalPeg.ScaStackMachine.exists_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_typed

/-- info: 'PalPeg.ScaStackMachine.recognizedBySCA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recognizedBySCA

/-- info: 'PalPeg.ScaStackMachine.pal_in_peg_of_stackMachine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg_of_stackMachine

end PalPeg.ScaStackMachine
