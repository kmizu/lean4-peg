import MacroPeg.CBV.FiniteSuffixBody
import MacroPeg.CBV.ParametricHelperControl
import MacroPeg.Properties.MExpEq

namespace Shallot.MacroPeg.CBV.FiniteSuffixCallCompiler
open RegularCaptureProduct (Node)
open FiniteSuffixBody (Body render)
open ExactWordCaptureMachine (observer)
open FiniteSuffixReplay (palette views)
open ClockFreezing (Table)

abbrev target (nodes : List Node) (R : List (List Char)) := RegularCaptureProduct.grammar nodes (observer (palette R))
def source (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) : MGrammar :=
  ⟨nodes.map (fun n => ⟨0,RegularCaptureProduct.body n⟩)++[⟨ids.length,render nodes.length R none B⟩]⟩
def sourceStart (nodes : List Node) (ids : List Nat) : MExp := .call nodes.length (ids.map (fun i => .call i []))
def targetStart (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) :=
  FiniteWordCaptureSelection.gather nodes (palette R) ids (fun V => render nodes.length R (some V) B)
abbrev sourceTable (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) (x : List Char) :=
  FilteredOverlapCaller.table (source nodes R ids B) x .callByValuePar
abbrev targetTable (nodes : List Node) (R : List (List Char)) (x : List Char) :=
  FiniteWordCaptureSelection.table nodes (palette R) x

theorem source_helper (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) (i : Nat) (hi : i<nodes.length) :
    ruleAtM (source nodes R ids B).rules i=some ⟨0,RegularCaptureProduct.body nodes[i]⟩ := by
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_eq_getElem hi]

theorem source_rule (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) :
    ruleAtM (source nodes R ids B).rules nodes.length=some ⟨ids.length,render nodes.length R none B⟩ := by
  simp [source,ruleAtM_eq_getElem?]

theorem installed (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) :
    RecursiveParserStability.Installed (nodes.map RegularCaptureProduct.body) (source nodes R ids B) := by
  intro i e he
  have hi : i<nodes.length := by simpa using (List.getElem?_eq_some_iff.mp he).1
  have hh : RegularCaptureProduct.body nodes[i]=e := by
    simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,Option.some.injEq] using he
  rw [←hh]
  exact source_helper nodes R ids B i hi

theorem helper_eq (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char))
    (ids : List Nat) (B : Body) (x : List Char) (E : List (List Char)) (i p : Nat) (hi : i<nodes.length) (hp : p≤x.length) :
    evV (source nodes R ids B) x .callByValuePar (sourceTable nodes R ids B x) E (.call i []) p=
      evV (target nodes R) x .callByValueSeq (targetTable nodes R x) [] (.call i []) p := by
  have hh := RegularCaptureProduct.canonical_helpers_eq (RegularCaptureProduct.helper_valid hn)
    (installed nodes R ids B) (RegularCaptureProduct.original_installed nodes (observer (palette R))) x
    .callByValuePar .callByValueSeq i p (by simpa using hi) hp
  rw [evV_call_par (source_helper nodes R ids B i hi) rfl (by decide),
    evV_call_seq (RegularCaptureProduct.original_rule nodes (observer (palette R)) i nodes[i] (List.getElem?_eq_getElem hi)) rfl]
  exact hh

theorem arguments_eq (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char))
    (ids : List Nat) (B : Body) (x : List Char) (p : Nat) (hp : p≤x.length) :
    ∀ (args : List Nat), (∀ i∈args, i<nodes.length) →
    evParArgs (source nodes R ids B) x .callByValuePar (sourceTable nodes R ids B x) [] (args.map (fun i => .call i [])) p=
      evParArgs (target nodes R) x .callByValueSeq (targetTable nodes R x) [] (args.map (fun i => .call i [])) p
  | [],_ => rfl
  | i::args,h => by
    simp only [List.map_cons,evParArgs]
    rw [helper_eq nodes hn R ids B x [] i p (h i (by simp)) hp]
    cases hv : evV (target nodes R) x .callByValueSeq (targetTable nodes R x) [] (.call i []) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q => rw [arguments_eq nodes hn R ids B x p hp args (by intro j hj; exact h j (by simp [hj]))]

theorem body_eq (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char))
    (ids : List Nat) (B : Body) (x : List Char) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source nodes R ids B) x .callByValuePar (sourceTable nodes R ids B x) E (render nodes.length R none B) p=
      evV (target nodes R) x .callByValueSeq (targetTable nodes R x) [] (render nodes.length R (some (views R E)) B) p :=
  FiniteSuffixBody.aligned _ _ x _ _ E nodes.length R (tblV_ok _ _ _ _)
    (fun i hi q hq => helper_eq nodes hn R ids B x E i q hi hq) B p hp

/-- Full original-call equality at actual physical stabilization tables.
The source does not contain product-filter rows; its helpers stay unchanged. -/
theorem canonical (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char))
    (ids : List Nat) (hids : ∀ i∈ids, i<nodes.length) (B : Body) (x : List Char) (p : Nat) (hp : p≤x.length) :
    evV (source nodes R ids B) x .callByValuePar (sourceTable nodes R ids B x) [] (sourceStart nodes ids) p=
      evV (target nodes R) x .callByValueSeq (targetTable nodes R x) [] (targetStart nodes R ids B) p := by
  rw [targetStart,FiniteWordCaptureSelection.gather_eval nodes hn (palette R) x ids hids p hp]
  rw [sourceStart,evV_call_par (source_rule nodes R ids B) (by simp) (by decide),arguments_eq nodes hn R ids B x p hp ids hids]
  cases hv : evParArgs (target nodes R) x .callByValueSeq (targetTable nodes R x) [] (ids.map (fun i => .call i [])) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      have hw : W∈words (subStrs x) ids.length := (mem_words _ _ _).mpr ⟨by simpa using evPar_length _ W hv,evPar_mem hp _ W hv⟩
      dsimp only []
      exact (FilteredOverlapCaller.canonical_row (source nodes R ids B) x .callByValuePar nodes.length _
        (source_rule nodes R ids B) W hw p hp).trans (body_eq nodes hn R ids B x W p hp)

theorem source_firstOrder (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) :
    (source nodes R ids B).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨n,_,rfl⟩ := List.mem_map.mp hr
    cases n <;> trivial
  · simp only [List.mem_singleton] at hr
    subst r
    exact FiniteSuffixBody.firstOrder _ _ _ _

theorem sourceStart_firstOrder (nodes : List Node) (ids : List Nat) : (sourceStart nodes ids).FirstOrder := by
  change MExp.FirstOrderArgs (ids.map (fun i => .call i []))
  induction ids <;> simp_all [MExp.FirstOrderArgs,MExp.FirstOrder]

theorem targetStart_firstOrder (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) :
    (targetStart nodes R ids B).FirstOrder :=
  FiniteWordCaptureSelection.gather_firstOrder nodes (palette R) ids _ (fun _ => FiniteSuffixBody.firstOrder _ _ _ _)

theorem observations_iff (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char))
    (ids : List Nat) (hids : ∀ i∈ids, i<nodes.length) (B : Body) (x : List Char) (rest : Option (List Char)) :
    SObs (source nodes R ids B) .callByValuePar (sourceStart nodes ids) x rest ↔
      SObs (target nodes R) .callByValueSeq (targetStart nodes R ids B) x rest := by
  rw [←decideObsV_iff (source_firstOrder nodes R ids B) (by decide) (sourceStart_firstOrder nodes ids),
    ←decideObsV_iff (RegularCaptureProduct.grammar_firstOrder nodes (observer (palette R))) (by decide) (targetStart_firstOrder nodes R ids B)]
  unfold decideObsV
  have hh := canonical nodes hn R ids hids B x x.length (Nat.le_refl _)
  simp only [sourceTable,targetTable,FiniteWordCaptureSelection.table,FilteredOverlapCaller.table] at hh
  rw [hh]

theorem language_translation (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char))
    (ids : List Nat) (hids : ∀ i∈ids, i<nodes.length) (B : Body) :
    (fun x => SObs (source nodes R ids B) .callByValuePar (sourceStart nodes ids) x (some []))=
      (fun x => SObs (target nodes R) .callByValueSeq (targetStart nodes R ids B) x (some [])) := by
  funext x
  exact propext (observations_iff nodes hn R ids hids B x (some []))


theorem defined_iff (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char))
    (ids : List Nat) (hids : ∀ i∈ids, i<nodes.length) (B : Body) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source nodes R ids B) x .callByValuePar (tblV (source nodes R ids B) x .callByValuePar k) [] (sourceStart nodes ids) x.length=some v) ↔
      ∃ k, evV (target nodes R) x .callByValueSeq (tblV (target nodes R) x .callByValueSeq k) [] (targetStart nodes R ids B) x.length=some v := by
  rw [tblV_stable _ _ _ (Nat.le_refl _),tblV_stable _ _ _ (Nat.le_refl _)]
  have hh := canonical nodes hn R ids hids B x x.length (Nat.le_refl _)
  simp only [sourceTable,targetTable,FiniteWordCaptureSelection.table,FilteredOverlapCaller.table] at hh
  rw [hh]

theorem undefined_iff (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char))
    (ids : List Nat) (hids : ∀ i∈ids, i<nodes.length) (B : Body) (x : List Char) :
    (∀ k, evV (source nodes R ids B) x .callByValuePar (tblV (source nodes R ids B) x .callByValuePar k) [] (sourceStart nodes ids) x.length=none) ↔
      ∀ k, evV (target nodes R) x .callByValueSeq (tblV (target nodes R) x .callByValueSeq k) [] (targetStart nodes R ids B) x.length=none := by
  constructor
  · intro h k
    cases he : evV (target nodes R) x .callByValueSeq (tblV (target nodes R) x .callByValueSeq k) [] (targetStart nodes R ids B) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff nodes hn R ids hids B x v).mpr ⟨k,he⟩
      rw [h j] at hj; cases hj
  · intro h k
    cases he : evV (source nodes R ids B) x .callByValuePar (tblV (source nodes R ids B) x .callByValuePar k) [] (sourceStart nodes ids) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff nodes hn R ids hids B x v).mp ⟨k,he⟩
      rw [h j] at hj; cases hj

def nodesCheck (nodes : List Node) := nodes.all (fun n => match n with
  | .lit _ => true
  | .seq a b | .alt a b => decide (a<nodes.length ∧ b<nodes.length)
  | .star a | .notP a => decide (a<nodes.length))

theorem nodes_checked (nodes : List Node) (hc : nodesCheck nodes=true) : RegularCaptureProduct.Valid nodes := by
  intro n hn
  have hh := List.all_eq_true.mp hc n hn
  cases n <;> simp_all [RegularCaptureProduct.Valid]

def sameRules : List MRule → List MRule → Bool
  | [],[] => true
  | r::rs,s::ss => decide (r.arity=s.arity) && MExp.beqE r.body s.body && sameRules rs ss
  | _,_ => false

theorem sameRules_checked : ∀ rs ss, sameRules rs ss=true → rs=ss
  | [],[],_ => rfl
  | [],_::_,h | _::_,[],h => by cases h
  | r::rs,s::ss,h => by
    obtain ⟨h,ht⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    have ha := of_decide_eq_true ha
    have hb := (MExp.beqE_iff _ _).mp hb
    have he : r=s := by cases r; cases s; simp_all
    rw [he,sameRules_checked rs ss ht]

def check (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body) : Bool :=
  nodesCheck nodes && ids.all (fun i => decide (i<nodes.length)) &&
    sameRules g.rules (source nodes R ids B).rules && MExp.beqE root (sourceStart nodes ids)

theorem checked (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body)
    (hc : check g root nodes R ids B=true) :
    RegularCaptureProduct.Valid nodes ∧ (∀ i∈ids, i<nodes.length) ∧ g=source nodes R ids B ∧ root=sourceStart nodes ids := by
  obtain ⟨h,he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨h,hg⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hn,hi⟩ := Bool.and_eq_true_iff.mp h
  have hg := sameRules_checked _ _ hg
  refine ⟨nodes_checked nodes hn,?_,?_,(MExp.beqE_iff _ _).mp he⟩
  · intro i hm; exact of_decide_eq_true (List.all_eq_true.mp hi i hm)
  · cases g; simp_all [source]

theorem checked_observations (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body)
    (hc : check g root nodes R ids B=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar root x rest ↔ SObs (target nodes R) .callByValueSeq (targetStart nodes R ids B) x rest := by
  obtain ⟨hn,hi,hg,he⟩ := checked g root nodes R ids B hc
  rw [hg,he]
  exact observations_iff nodes hn R ids hi B x rest

theorem checked_language (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (ids : List Nat) (B : Body)
    (hc : check g root nodes R ids B=true) :
    (fun x => SObs g .callByValuePar root x (some []))=
      (fun x => SObs (target nodes R) .callByValueSeq (targetStart nodes R ids B) x (some [])) := by
  funext x
  exact propext (checked_observations g root nodes R ids B hc x (some []))

end Shallot.MacroPeg.CBV.FiniteSuffixCallCompiler
