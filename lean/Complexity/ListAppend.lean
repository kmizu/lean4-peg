import Complexity.UnarySpec

/-! Append a fixed finite list, with a capacity covering every intermediate push. -/
namespace Complexity

def appendP {k : Nat} (dst : Fin k) : List Nat → LProg k
  | [] => skipP dst
  | v :: vs => .seq (.push dst v) (appendP dst vs)

theorem append_runs {k : Nat} (dst : Fin k) (vs : List Nat) {B : Nat} {L : Lists k}
    (hL : LenOK B L) (hcap : (L dst).length+vs.length+2 ≤ B) :
    Runs (LenOK B) (appendP dst vs) L (L.set dst (L dst ++ vs)) (vs.length+1) := by
  induction vs generalizing L with
  | nil => simpa [appendP,Lists.set_get_self] using runs_skip dst hL
  | cons v vs ih =>
    have hM : LenOK B (L.set dst (L dst ++ [v])) := lenOK_set hL dst (by simp; simp at hcap; omega)
    have hp := runs_push (i := dst) (e := v) hL hM
    have hh := ih hM (by simp; simp at hcap; omega)
    have he := hp.seq hh
    simpa [appendP,Lists.set_set_u,List.append_assoc,Nat.add_comm] using he

/-- A complete transfer is bounded by its initial and final states. -/
theorem moveAll_runs_bounded {k : Nat} {src dst : Fin k} (hd : src ≠ dst)
    {B : Nat} {L : Lists k} (hL : LenOK B L) (hcap : (L dst).length+(L src).length+2 ≤ B) :
    Runs (LenOK B) (moveAll src dst) L ((L.set dst (L dst ++ (L src).reverse)).set src [])
      (((L src).length+1)*3) := by
  have hr := runs_moveAll (L := L) hd (fun i j _ _ => lenOK_moving hL hd hcap i j)
  simpa only [Lists.moveAll] using hr

end Complexity
