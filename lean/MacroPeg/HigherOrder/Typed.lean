import MacroPeg.HigherOrder.Semantics

/-!
# Intrinsically typed higher-order Macro PEG

`Tm R Γ τ` is a term of type `τ` in context `Γ` when rule `i` has type `R[i]`; only well-typed terms can be written.
`erase` forgets the types and gives the untyped `HExp` that the operational semantics (`hrun`) runs. A typed grammar
`TGrammar R` holds one closed body of type `R[i]` per rule.

The decision procedure (`Decide.lean`) and its correctness are stated for typed grammars: they need a type for every
subterm, which `Tm` carries by construction.
-/

namespace Shallot.MacroPeg.HO

inductive Tm (R : List Ty) : List Ty → Ty → Type where
  | eps {Γ : List Ty} : Tm R Γ .p
  | any {Γ : List Ty} : Tm R Γ .p
  | chr {Γ : List Ty} (c : Char) : Tm R Γ .p
  | range {Γ : List Ty} (lo hi : Char) : Tm R Γ .p
  | lit {Γ : List Ty} (s : List Char) : Tm R Γ .p
  | seq {Γ : List Ty} (a b : Tm R Γ .p) : Tm R Γ .p
  | alt {Γ : List Ty} (a b : Tm R Γ .p) : Tm R Γ .p
  | star {Γ : List Ty} (a : Tm R Γ .p) : Tm R Γ .p
  | notP {Γ : List Ty} (a : Tm R Γ .p) : Tm R Γ .p
  | var {Γ : List Ty} {τ : Ty} (i : Nat) (h : Γ[i]? = some τ) : Tm R Γ τ
  | rule {Γ : List Ty} {τ : Ty} (i : Nat) (h : R[i]? = some τ) : Tm R Γ τ
  | lam {Γ : List Ty} {a b : Ty} (body : Tm R (a :: Γ) b) : Tm R Γ (a ⇒ b)
  | app {Γ : List Ty} {a b : Ty} (f : Tm R Γ (a ⇒ b)) (x : Tm R Γ a) : Tm R Γ b

/-- Forget the types. -/
def Tm.erase {R : List Ty} : {Γ : List Ty} → {τ : Ty} → Tm R Γ τ → HExp
  | _, _, .eps => .eps
  | _, _, .any => .any
  | _, _, .chr c => .chr c
  | _, _, .range lo hi => .range lo hi
  | _, _, .lit s => .lit s
  | _, _, .seq a b => .seq a.erase b.erase
  | _, _, .alt a b => .alt a.erase b.erase
  | _, _, .star a => .star a.erase
  | _, _, .notP a => .notP a.erase
  | _, _, .var i _ => .var i
  | _, _, .rule i _ => .rule i
  | _, _, @Tm.lam _ _ a _ body => .lam a body.erase
  | _, _, .app f x => .app f.erase x.erase

/-- One closed body per type of `S`: `TBodies R S` lists the rule bodies of a grammar whose rule types are `R`. -/
def TBodies (R : List Ty) : List Ty → Type
  | [] => Unit
  | τ :: S => Tm R [] τ × TBodies R S

/-- The bodies as a list of untyped expressions. -/
def TBodies.erase {R : List Ty} : {S : List Ty} → TBodies R S → List HExp
  | [], _ => []
  | _ :: _, (t, ts) => t.erase :: TBodies.erase ts

/-- A typed grammar: rule `i` has type `R[i]` and a closed body of that type. -/
structure TGrammar (R : List Ty) where
  bodies : TBodies R R

/-- The untyped grammar that the operational semantics runs. -/
def TGrammar.erase {R : List Ty} (G : TGrammar R) : HGrammar :=
  ⟨List.zipWith (fun τ b => ⟨τ, b⟩) R G.bodies.erase⟩

/-! ## Typed terms are well typed -/

theorem Tm.hasTy {R : List Ty} : {Γ : List Ty} → {τ : Ty} → (t : Tm R Γ τ) → HasTy R Γ t.erase τ
  | _, _, .eps => .eps _
  | _, _, .any => .any _
  | _, _, .chr c => .chr _ c
  | _, _, .range lo hi => .range _ lo hi
  | _, _, .lit s => .lit _ s
  | _, _, .seq a b => .seq a.hasTy b.hasTy
  | _, _, .alt a b => .alt a.hasTy b.hasTy
  | _, _, .star a => .star a.hasTy
  | _, _, .notP a => .notP a.hasTy
  | _, _, .var _ h => .var h
  | _, _, .rule _ h => .rule h
  | _, _, .lam body => .lam body.hasTy
  | _, _, .app f x => .app f.hasTy x.hasTy

/-! ## Typing derivations give typed terms -/

/-- A well-typed expression is the erasure of a typed term. -/
theorem HasTy.toTm {R : List Ty} {Γ : List Ty} {e : HExp} {τ : Ty} (h : HasTy R Γ e τ) :
    ∃ t : Tm R Γ τ, t.erase = e := by
  induction h with
  | eps => exact ⟨.eps, rfl⟩
  | any => exact ⟨.any, rfl⟩
  | chr _ c => exact ⟨.chr c, rfl⟩
  | range _ lo hi => exact ⟨.range lo hi, rfl⟩
  | lit _ s => exact ⟨.lit s, rfl⟩
  | seq _ _ iha ihb =>
    obtain ⟨a, rfl⟩ := iha; obtain ⟨b, rfl⟩ := ihb; exact ⟨.seq a b, rfl⟩
  | alt _ _ iha ihb =>
    obtain ⟨a, rfl⟩ := iha; obtain ⟨b, rfl⟩ := ihb; exact ⟨.alt a b, rfl⟩
  | star _ iha => obtain ⟨a, rfl⟩ := iha; exact ⟨.star a, rfl⟩
  | notP _ iha => obtain ⟨a, rfl⟩ := iha; exact ⟨.notP a, rfl⟩
  | @var _ i _ h => exact ⟨.var i h, rfl⟩
  | @rule _ i _ h => exact ⟨.rule i h, rfl⟩
  | lam _ ih => obtain ⟨b, rfl⟩ := ih; exact ⟨.lam b, rfl⟩
  | app _ _ ihf iha => obtain ⟨f, rfl⟩ := ihf; obtain ⟨a, rfl⟩ := iha; exact ⟨.app f a, rfl⟩

theorem TBodies.exists_of_hasTy {R : List Ty} : ∀ rs : List HRule, (∀ r ∈ rs, HasTy R [] r.body r.ty) →
    ∃ bs : TBodies R (rs.map HRule.ty), List.zipWith (fun τ b => (⟨τ, b⟩ : HRule)) (rs.map HRule.ty) bs.erase = rs
  | [], _ => ⟨(), rfl⟩
  | r :: rs, h => by
    obtain ⟨t, ht⟩ := (h r List.mem_cons_self).toTm
    obtain ⟨bs, hbs⟩ := TBodies.exists_of_hasTy rs (fun r' hr => h r' (List.mem_cons_of_mem _ hr))
    refine ⟨(t, bs), ?_⟩
    simp only [List.map_cons, TBodies.erase, List.zipWith_cons_cons, ht, hbs]

/-- **A well-typed grammar is the erasure of a typed grammar**, so the decision procedure applies to it. -/
theorem HGrammar.WellTyped.toTGrammar {g : HGrammar} (hg : g.WellTyped) :
    ∃ G : TGrammar g.types, G.erase = g := by
  obtain ⟨bs, hbs⟩ := TBodies.exists_of_hasTy g.rules hg
  exact ⟨⟨bs⟩, by cases g; simp only [TGrammar.erase, HGrammar.mk.injEq]; exact hbs⟩

end Shallot.MacroPeg.HO
