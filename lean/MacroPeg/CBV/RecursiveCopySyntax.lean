import MacroPeg.CBV.DelimitedCopyCallTransfer

namespace Shallot.MacroPeg.CBV.RecursiveCopySyntax
open DelimiterTemplate DelimitedCopyTemplates

inductive Expr where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | user (i : Nat) | copy (a b : Expr)
  | seq (a b : Expr) | alt (a b : Expr) | notP (a : Expr) | star (a : Expr)
  deriving Repr

def render (n : Nat) (parallel : Bool) : Expr → MExp
  | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
  | .user i => .call i []
  | .copy a b => if parallel then DelimitedCopyCallTransfer.head n (render n parallel a) (render n parallel b)
      else DelimitedCopyCallTransfer.targetHead n (render n parallel a) (render n parallel b)
  | .seq a b => .seq (render n parallel a) (render n parallel b)
  | .alt a b => .alt (render n parallel a) (render n parallel b)
  | .notP a => .notP (render n parallel a)
  | .star a => .star (render n parallel a)

def sourceBodies (clients : List Expr) := clients.map (render clients.length true)
def targetBodies (clients : List Expr) := clients.map (render clients.length false)
def source (clients : List Expr) (d : Char) := DelimitedCopySyntax.source (sourceBodies clients) d
def target (clients : List Expr) (d : Char) := DelimitedCopySyntax.target (targetBodies clients) d

/-- Capture checks inspect the real source declarations, including copy
callbacks. Only positive output paths need exclude the separator. -/
def termCheck (clients : List Expr) (alphabet : List Char) (d : Char) : Expr → Bool
  | .user i => decide (i<clients.length)
  | .copy a b => (termCheck clients alphabet d a && termCheck clients alphabet d b) &&
      MaskedScannerAbsorption.check (sourceBodies clients) alphabet (render clients.length true a) &&
      MaskedScannerAbsorption.check (sourceBodies clients) alphabet (render clients.length true b)
  | .seq a b | .alt a b => termCheck clients alphabet d a && termCheck clients alphabet d b
  | .notP a | .star a => termCheck clients alphabet d a
  | _ => true

def check (clients : List Expr) (alphabet : List Char) (d : Char) (root : Expr) : Bool :=
  decide (d∉alphabet) && clients.all (termCheck clients alphabet d) && termCheck clients alphabet d root

theorem render_firstOrder (n : Nat) (parallel : Bool) : ∀ e, (render n parallel e).FirstOrder
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .user _ => True.intro
  | .copy a b => by
    cases parallel with
    | true => exact ⟨render_firstOrder n true a,render_firstOrder n true b,True.intro⟩
    | false => exact ⟨render_firstOrder n false a,render_firstOrder n false b,
        ⟨render_firstOrder n false a,True.intro⟩,render_firstOrder n false b,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder n parallel a,render_firstOrder n parallel b⟩
  | .notP a | .star a => render_firstOrder n parallel a

theorem render_closed (n : Nat) (parallel : Bool) : ∀ e, ReplayFallbackFusion.Closed (render n parallel e)
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .user _ => True.intro
  | .copy a b => by
    cases parallel with
    | true => exact ⟨render_closed n true a,render_closed n true b,True.intro⟩
    | false => exact ⟨render_closed n false a,render_closed n false b,
        ⟨render_closed n false a,True.intro⟩,render_closed n false b,True.intro⟩
  | .seq a b | .alt a b => ⟨render_closed n parallel a,render_closed n parallel b⟩
  | .notP a | .star a => render_closed n parallel a

theorem source_installed (clients : List Expr) (d : Char) : RecursiveParserStability.Installed (sourceBodies clients) (source clients d) :=
  DelimitedCopySyntax.source_installed _ _

theorem source_user (clients : List Expr) (d : Char) (i : Nat) (e : Expr) (hi : clients[i]?=some e) :
    ruleAtM (source clients d).rules i=some ⟨0,render clients.length true e⟩ :=
  source_installed clients d i _ (by simp [sourceBodies,List.getElem?_map,hi])

theorem target_user (clients : List Expr) (d : Char) (i : Nat) (e : Expr) (hi : clients[i]?=some e) :
    ruleAtM (target clients d).rules i=some ⟨0,render clients.length false e⟩ :=
  DelimitedCopySyntax.target_installed (targetBodies clients) d i _ (by simp [targetBodies,List.getElem?_map,hi])

theorem source_copy (clients : List Expr) (d : Char) :
    ruleAtM (source clients d).rules clients.length=some ⟨2,compile d (sourceBlockParts d)⟩ := by
  simpa [source,sourceBodies] using DelimitedCopySyntax.source_rule (sourceBodies clients) d

theorem target_short (clients : List Expr) (d : Char) :
    ruleAtM (target clients d).rules clients.length=some ⟨1,compile d (shortBlockParts d)⟩ := by
  simpa [target,targetBodies] using DelimitedCopySyntax.short_rule (targetBodies clients) d

theorem target_long (clients : List Expr) (d : Char) :
    ruleAtM (target clients d).rules (clients.length+1)=some ⟨1,compile d (longBlockParts d)⟩ := by
  simpa [target,targetBodies] using DelimitedCopySyntax.long_rule (targetBodies clients) d

theorem source_firstOrder (clients : List Expr) (d : Char) : (source clients d).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hl|hc
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hl
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
    exact render_firstOrder _ _ _
  · have he : r=⟨2,compile d (sourceBlockParts d)⟩ := by simpa using hc
    subst r
    exact compile_firstOrder _ _

theorem target_firstOrder (clients : List Expr) (d : Char) : (target clients d).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hl|hc
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hl
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
    exact render_firstOrder _ _ _
  · rcases (show r=⟨1,compile d (shortBlockParts d)⟩ ∨ r=⟨1,compile d (longBlockParts d)⟩ from by simpa using hc) with rfl|rfl <;> exact compile_firstOrder _ _

theorem checked (clients : List Expr) (alphabet : List Char) (d : Char) (root : Expr) (hc : check clients alphabet d root=true) :
    d∉alphabet ∧ (∀ (i : Nat) (e : Expr), clients[i]?=some e → termCheck clients alphabet d e=true) ∧ termCheck clients alphabet d root=true := by
  obtain ⟨h,hroot⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hd,hb⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true hd,fun i e hi => List.all_eq_true.mp hb e (List.mem_of_getElem? hi),hroot⟩

end Shallot.MacroPeg.CBV.RecursiveCopySyntax
