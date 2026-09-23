import PalPeg.PalInPegSca

/-!
# Scaffold automata over finite types

Kim–Park's `Scaffolding.Automaton` numbers its states and labels by `Fin`. Its neighborhoods,
actions and scaffolds are generic in the label and state types, so an automaton can be written
over structured finite types and transported along equivalences. Relabelling does not change how
edges are followed, and neighborhoods commute with the relabelling.
-/
set_option autoImplicit false
namespace PalPeg.ScaTyped
open PegSeparation PegSeparation.Scaffolding

variable {L L' : Type} {degree : ℕ}

/-- Relabel a neighborhood. -/
def mapNbhd (f : L → L') : (radius : ℕ) → Neighborhood L degree radius → Neighborhood L' degree radius
  | 0, n => (n : Option L).map f
  | radius + 1, n => ((n.1 : Option L).map f, fun d => (n.2 d).map (mapNbhd f radius))

def mapNode (f : L → L') (n : Node L degree) : Node L' degree := ⟨n.label.map f, n.edgeOffset⟩

def mapScaffold (f : L → L') (s : Scaffold L degree) : Scaffold L' degree :=
  ⟨mapNode f s.top, s.older.map (mapNode f)⟩

theorem nodes_map (f : L → L') (s : Scaffold L degree) :
    (mapScaffold f s).nodes = s.nodes.map (mapNode f) := rfl

theorem follow_map (f : L → L') (nodes : List (Node L degree)) :
    ∀ (p : ℕ) (ds : List (Fin degree)),
      Scaffold.follow (nodes.map (mapNode f)) p ds = Scaffold.follow nodes p ds
  | p, [] => by
    simp only [Scaffold.follow, List.getElem?_map, Option.map_map]
    cases nodes[p]? <;> rfl
  | p, d :: ds => by
    simp only [Scaffold.follow, List.getElem?_map]
    cases nodes[p]? with
    | none => rfl
    | some node =>
      cases h : node.edgeOffset d with
      | none => simp [mapNode, h]
      | some o => simp [mapNode, h, follow_map f nodes (p + o) ds]

theorem neighborhoodAt_map (f : L → L') (nodes : List (Node L degree)) :
    ∀ (radius p : ℕ), Scaffold.neighborhoodAt (nodes.map (mapNode f)) radius p
      = (Scaffold.neighborhoodAt nodes radius p).map (mapNbhd f radius)
  | 0, p => by
    simp only [Scaffold.neighborhoodAt, List.getElem?_map, Option.map_map]
    rfl
  | radius + 1, p => by
    simp only [Scaffold.neighborhoodAt, List.getElem?_map]
    cases nodes[p]? with
    | none => rfl
    | some node =>
      show some _ = some _
      congr 1
      refine Prod.ext rfl (funext fun d => ?_)
      cases h : node.edgeOffset d with
      | none => simp [h, mapNode, mapNbhd]
      | some o => simp [h, mapNode, mapNbhd, neighborhoodAt_map f nodes radius (p + o)]

theorem topNeighborhood_map (f : L → L') (s : Scaffold L degree) :
    ∀ radius, (mapScaffold f s).topNeighborhood radius = mapNbhd f radius (s.topNeighborhood radius)
  | 0 => rfl
  | radius + 1 => by
    show (_, _) = (_, _)
    refine Prod.ext rfl (funext fun d => ?_)
    show (do let offset ← s.top.edgeOffset d
             Scaffold.neighborhoodAt (mapScaffold f s).nodes radius offset) = _
    rw [nodes_map]
    cases h : s.top.edgeOffset d with
    | none => simp [h, Scaffold.topNeighborhood]
    | some o => simp [h, Scaffold.topNeighborhood, neighborhoodAt_map f s.nodes radius o]

theorem mapNbhd_comp {L'' : Type} (f : L → L') (g : L' → L'') :
    ∀ (radius : ℕ) (n : Neighborhood L degree radius),
      mapNbhd g radius (mapNbhd f radius n) = mapNbhd (g ∘ f) radius n
  | 0, n => by simp [mapNbhd, Option.map_map]
  | radius + 1, n => by
    refine Prod.ext (by simp [mapNbhd, Option.map_map]) (funext fun d => ?_)
    show Option.map (mapNbhd g radius) (Option.map (mapNbhd f radius) (n.2 d))
      = Option.map (mapNbhd (g ∘ f) radius) (n.2 d)
    cases n.2 d with
    | none => rfl
    | some m => simp [mapNbhd_comp f g radius m]

theorem mapNbhd_id : ∀ (radius : ℕ) (n : Neighborhood L degree radius), mapNbhd id radius n = n
  | 0, n => by simp [mapNbhd]
  | radius + 1, n => by
    refine Prod.ext (by simp [mapNbhd]) (funext fun d => ?_)
    show Option.map (mapNbhd id radius) (n.2 d) = n.2 d
    cases n.2 d with
    | none => rfl
    | some m => simp [mapNbhd_id radius m]

/-- A scaffold automaton whose states and labels are finite types. -/
structure Typed (T S L : Type) (degree radius : ℕ) where
  degreePositive : 0 < degree
  initial : S
  accepting : S → Bool
  transition : S → T → Neighborhood L degree radius → Action S L degree radius

namespace Typed

variable {T S : Type} {radius : ℕ}

def extend (old : Scaffold L degree) (action : Action S L degree radius) : Scaffold L degree where
  top :=
    { label := some action.newLabel
      edgeOffset := fun direction =>
        match action.target direction with
        | .missing => none
        | .self => some 0
        | .path directions _ =>
            (Scaffold.follow old.nodes 0 directions).map (fun endpoint => endpoint + 1) }
  older := old.nodes

def step (A : Typed T S L degree radius) (c : S × Scaffold L degree) (a : T) : S × Scaffold L degree :=
  let action := A.transition c.1 a (c.2.topNeighborhood radius)
  (action.nextState, extend c.2 action)

def run (A : Typed T S L degree radius) (input : List T) : S × Scaffold L degree :=
  input.foldl A.step (A.initial, ⟨⟨none, fun _ => none⟩, []⟩)

def Accepts (A : Typed T S L degree radius) (input : List T) : Prop :=
  A.accepting (A.run input).1 = true

/-- Number the states and labels. -/
def toAutomaton {s k : ℕ} (A : Typed T S L degree radius) (eS : S ≃ Fin s) (eL : L ≃ Fin k) :
    Automaton T s k degree radius where
  degreePositive := A.degreePositive
  initialState := eS A.initial
  accepting := Finset.univ.filter (fun q => A.accepting (eS.symm q) = true)
  transition q a n :=
    let act := A.transition (eS.symm q) a (mapNbhd eL.symm radius n)
    ⟨eS act.nextState, eL act.newLabel, act.target⟩

theorem extend_map {s k : ℕ} (eL : L ≃ Fin k) (old : Scaffold L degree)
    (act : Action S L degree radius) (eS : S ≃ Fin s) :
    Automaton.extendScaffold (stateCount := s) (mapScaffold eL old)
        ⟨eS act.nextState, eL act.newLabel, act.target⟩
      = mapScaffold eL (extend old act) := by
  unfold Automaton.extendScaffold extend mapScaffold
  simp only [mapNode]
  congr 1
  · congr 1
    funext d
    cases act.target d with
    | missing => rfl
    | self => rfl
    | path ds _ =>
      show Option.map _ (Scaffold.follow (mapScaffold eL old).nodes 0 ds) = _
      rw [nodes_map, follow_map]

theorem step_toAutomaton {s k : ℕ} (A : Typed T S L degree radius) (eS : S ≃ Fin s)
    (eL : L ≃ Fin k) (c : S × Scaffold L degree) (a : T) :
    (A.toAutomaton eS eL).step (eS c.1, mapScaffold eL c.2) a
      = (eS (A.step c a).1, mapScaffold eL (A.step c a).2) := by
  have hn : mapNbhd eL.symm radius ((mapScaffold eL c.2).topNeighborhood radius)
      = c.2.topNeighborhood radius := by
    rw [topNeighborhood_map, mapNbhd_comp,
      show (eL.symm ∘ eL : L → L) = id from funext eL.symm_apply_apply, mapNbhd_id]
  unfold Automaton.step
  simp only [toAutomaton, Equiv.symm_apply_apply, hn]
  rw [extend_map]
  rfl

theorem run_toAutomaton {s k : ℕ} (A : Typed T S L degree radius) (eS : S ≃ Fin s)
    (eL : L ≃ Fin k) (input : List T) :
    (A.toAutomaton eS eL).run input = (eS (A.run input).1, mapScaffold eL (A.run input).2) := by
  unfold Automaton.run run
  suffices h : ∀ (c : S × Scaffold L degree),
      input.foldl (A.toAutomaton eS eL).step (eS c.1, mapScaffold eL c.2)
        = (eS (input.foldl A.step c).1, mapScaffold eL (input.foldl A.step c).2) by
    exact h (A.initial, ⟨⟨none, fun _ => none⟩, []⟩)
  induction input with
  | nil => intro c; rfl
  | cons a rest ih =>
    intro c
    simp only [List.foldl_cons]
    rw [step_toAutomaton, ih]

theorem accepts_toAutomaton {s k : ℕ} (A : Typed T S L degree radius) (eS : S ≃ Fin s)
    (eL : L ≃ Fin k) (input : List T) :
    (A.toAutomaton eS eL).Accepts input ↔ A.Accepts input := by
  unfold Automaton.Accepts Accepts
  rw [run_toAutomaton]
  simp [toAutomaton]

/-- **A scaffold automaton over finite types recognizes its language in Kim–Park's sense.** -/
theorem recognizedBySCA {Lang : Language T} [Fintype S] [Fintype L]
    (A : Typed T S L degree radius) (hA : ∀ input, A.Accepts input ↔ input ∈ Lang) :
    RecognizedBySCA Lang :=
  ⟨_, _, degree, radius, A.toAutomaton (Fintype.equivFin S) (Fintype.equivFin L),
    fun input => (accepts_toAutomaton A _ _ input).trans (hA input)⟩

end Typed

/-- **`PAL ∈ PEG` from a scaffold automaton over finite types.** -/
theorem pal_in_peg_of_typed {S L : Type} [Fintype S] [Fintype L] {degree radius : ℕ}
    (A : Typed (Fin 2) S L degree radius) (hA : ∀ w, A.Accepts w ↔ w ∈ PalPeg.PAL) :
    RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.pal_recognizedByTotalPEG_of_sca (Typed.recognizedBySCA A hA)

/-- info: 'PalPeg.ScaTyped.pal_in_peg_of_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg_of_typed

end PalPeg.ScaTyped
