import Complexity.Qbf

/-!
# Output templates

A small language for describing token lists built by nested counting loops: emit a token, emit a name whose components
are constants or counter values, loop a counter over `0 … N - 1` (`N` a constant, the space bound `S` or the level
bound `T` of the environment), branch on counter comparisons and on the input bits. `Tmpl.denote` is the token list a
template describes; a list program interpreting templates is verified once, so that concrete outputs (the formulas of
the hardness reduction) only need functional proofs.
-/

namespace Complexity

structure TEnv where
  w : List Bool
  S : Nat
  T : Nat
  ctr : Nat → Nat

def TEnv.set (e : TEnv) (i v : Nat) : TEnv := { e with ctr := fun j => if j = i then v else e.ctr j }

inductive Bound where
  | const (n : Nat)
  | S
  | T

def Bound.val (e : TEnv) : Bound → Nat
  | .const n => n
  | .S => e.S
  | .T => e.T

inductive Part where
  | const (n : Nat)
  | ctr (i : Nat)
  /-- `T - ctr i + c` (levels counted down) -/
  | rev (i c : Nat)

def Part.val (e : TEnv) : Part → Nat
  | .const n => n
  | .ctr i => e.ctr i
  | .rev i c => e.T - e.ctr i + c

inductive Cond where
  | tt
  | lt (i j : Nat)
  | eq (i j : Nat)
  | eqc (i n : Nat)
  /-- `ctr i = ctr j + 1` -/
  | succ (i j : Nat)
  /-- the input has bit `b` at position `ctr i` -/
  | inBit (i : Nat) (b : Bool)
  | not (c : Cond)
  | and (c d : Cond)
  | or (c d : Cond)

def Cond.eval (e : TEnv) : Cond → Bool
  | .tt => true
  | .lt i j => decide (e.ctr i < e.ctr j)
  | .eq i j => decide (e.ctr i = e.ctr j)
  | .eqc i n => decide (e.ctr i = n)
  | .succ i j => decide (e.ctr i = e.ctr j + 1)
  | .inBit i b => decide (e.w[e.ctr i]? = some b)
  | .not c => !c.eval e
  | .and c d => c.eval e && d.eval e
  | .or c d => c.eval e || d.eval e

inductive Tmpl where
  | nil
  | tok (t : Nat)
  | name (ps : List Part)
  | seq (a b : Tmpl)
  | forR (i : Nat) (b : Bound) (body : Tmpl)
  | ite (c : Cond) (a b : Tmpl)

def Tmpl.denote (e : TEnv) : Tmpl → List Nat
  | .nil => []
  | .tok t => [t]
  | .name ps => encName (ps.map (Part.val e))
  | .seq a b => a.denote e ++ b.denote e
  | .forR i b body => (List.range (b.val e)).flatMap (fun v => body.denote (e.set i v))
  | .ite c a b => if c.eval e then a.denote e else b.denote e

/-- Concatenate a list of templates. -/
def Tmpl.seqs : List Tmpl → Tmpl
  | [] => .nil
  | t :: ts => .seq t (Tmpl.seqs ts)

theorem Tmpl.denote_seqs (e : TEnv) : ∀ ts : List Tmpl, (Tmpl.seqs ts).denote e = ts.flatMap (·.denote e)
  | [] => rfl
  | t :: ts => by simp [Tmpl.seqs, Tmpl.denote, Tmpl.denote_seqs e ts]

end Complexity
