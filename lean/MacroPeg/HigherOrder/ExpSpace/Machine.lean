import MacroPeg.Properties.AtmHard

/-!
# Alternating machines with an exponentially long tape

The machine `M : ATM` (`AtmHard.lean`: states, kinds, transitions) now runs on a work tape of `2^n` cells, `n = |w|`.
A cell address is a vector of `n` bits, most significant first; a head move is the binary successor or predecessor of
the address (staying put at the last or the first address). The tape starts with cell `a` holding
`⋁ⱼ (aⱼ ∧ wⱼ)`, so cell `eⱼ` (only bit `j` set) holds `wⱼ`.

Alternating exponential space is doubly exponential time (`AEXPSPACE = 2-EXPTIME`, Chandra–Kozen–Stockmeyer 1981, an
external fact); a machine of this kind can first read `wⱼ` from cell `eⱼ`, so some fixed machine accepts a
`2-EXPTIME`-complete language this way (also external).
-/

namespace Shallot.MacroPeg.ExpSpace

open Shallot.MacroPeg (ATM Dir Kind)

/-! ## Binary successor and predecessor, most significant bit first -/

/-- Bit `j` flips iff all later (less significant) bits are `1`. -/
def incBits : List Bool → List Bool
  | [] => []
  | b :: rest => (b != rest.all id) :: incBits rest

/-- Bit `j` flips iff all later bits are `0`. -/
def decBits : List Bool → List Bool
  | [] => []
  | b :: rest => (b != rest.all (! ·)) :: decBits rest

/-- The successor, staying at the last address. -/
def vinc (v : List Bool) : List Bool := if v.all id then v else incBits v

/-- The predecessor, staying at the first address. -/
def vdec (v : List Bool) : List Bool := if v.all (! ·) then v else decBits v

theorem length_incBits : ∀ v : List Bool, (incBits v).length = v.length
  | [] => rfl
  | _ :: v => by simp [incBits, length_incBits v]

theorem length_decBits : ∀ v : List Bool, (decBits v).length = v.length
  | [] => rfl
  | _ :: v => by simp [decBits, length_decBits v]

theorem length_vinc (v : List Bool) : (vinc v).length = v.length := by
  unfold vinc; split
  · rfl
  · exact length_incBits v

theorem length_vdec (v : List Bool) : (vdec v).length = v.length := by
  unfold vdec; split
  · rfl
  · exact length_decBits v

/-! ## Configurations -/

structure Cfg where
  q : Nat
  /-- The head address. -/
  h : List Bool
  t : List Bool → Bool

def moveH : Dir → List Bool → List Bool
  | .left, h => vdec h
  | .right, h => vinc h

/-- Write `b` at the head, move, go to `q'`. -/
def succOf (c : Cfg) (tr : Nat × Bool × Dir) : Cfg :=
  ⟨tr.1, moveH tr.2.2 c.h, fun a => if a = c.h then tr.2.1 else c.t a⟩

def succs (M : ATM) (c : Cfg) : List Cfg := (M.delta c.q (c.t c.h)).map (succOf c)

/-- Every branch from `c` is finite. -/
inductive Halts (M : ATM) : Cfg → Prop
  | mk (c : Cfg) : (∀ c' ∈ succs M c, Halts M c') → Halts M c

mutual
  inductive Val (M : ATM) : Cfg → Bool → Prop
    | acc (c : Cfg) : M.kind c.q = .acc → Val M c true
    | rej (c : Cfg) : M.kind c.q = .rej → Val M c false
    | univ (c : Cfg) (bs : List Bool) : M.kind c.q = .univ → ValList M (succs M c) bs → Val M c (bs.all id)
    | exist (c : Cfg) (bs : List Bool) : M.kind c.q = .exist → ValList M (succs M c) bs → Val M c (bs.any id)

  inductive ValList (M : ATM) : List Cfg → List Bool → Prop
    | nil : ValList M [] []
    | cons (c : Cfg) (cs : List Cfg) (b : Bool) (bs : List Bool) : Val M c b → ValList M cs bs →
        ValList M (c :: cs) (b :: bs)
end

/-- The initial tape: cell `a` holds `⋁ⱼ (aⱼ ∧ wⱼ)`. -/
def initTape (w : List Bool) (a : List Bool) : Bool := (a.zip w).any (fun p => p.1 && p.2)

def init (M : ATM) (w : List Bool) : Cfg := ⟨M.start, List.replicate w.length false, initTape w⟩

def Accepts (M : ATM) (w : List Bool) : Prop := Val M (init M w) true

theorem val_functional (M : ATM) {c : Cfg} {b : Bool} (h : Val M c b) : ∀ b', Val M c b' → b = b' := by
  induction h using Val.rec (motive_2 := fun cs bs _ => ∀ bs', ValList M cs bs' → bs = bs') with
  | acc c hk => intro b' h'; cases h' <;> simp_all
  | rej c hk => intro b' h'; cases h' <;> simp_all
  | univ c bs hk _ ih =>
    intro b' h'
    cases h' with
    | univ _ bs' _ hl => rw [ih bs' hl]
    | _ => simp_all
  | exist c bs hk _ ih =>
    intro b' h'
    cases h' with
    | exist _ bs' _ hl => rw [ih bs' hl]
    | _ => simp_all
  | nil => rename_i bs' h'; cases h'; rfl
  | cons c cs b bs _ _ ih₁ ih₂ =>
    rename_i bs' h'
    cases h' with
    | cons _ _ b' bs'' h₁ h₂ => rw [ih₁ b' h₁, ih₂ bs'' h₂]

theorem valList_functional (M : ATM) : ∀ {cs : List Cfg} {bs bs' : List Bool},
    ValList M cs bs → ValList M cs bs' → bs = bs'
  | _, _, _, .nil, h => by cases h; rfl
  | _, _, _, .cons _ _ _ _ h₁ h₂, h' => by
    cases h' with
    | cons _ _ b' bs'' h₁' h₂' => rw [val_functional M h₁ b' h₁', valList_functional M h₂ h₂']

theorem vals_exist (M : ATM) (c : Cfg) : ∀ trs : List (Nat × Bool × Dir),
    (∀ tr ∈ trs, ∃ b, Val M (succOf c tr) b) → ∃ bs, ValList M (trs.map (succOf c)) bs
  | [], _ => ⟨[], .nil⟩
  | tr :: trs, H => by
    obtain ⟨b, hb⟩ := H tr List.mem_cons_self
    obtain ⟨bs, hbs⟩ := vals_exist M c trs (fun t ht => H t (List.mem_cons_of_mem _ ht))
    exact ⟨b :: bs, .cons _ _ _ _ hb hbs⟩

end Shallot.MacroPeg.ExpSpace
