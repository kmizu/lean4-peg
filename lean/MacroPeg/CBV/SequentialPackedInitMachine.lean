import MacroPeg.CBV.SequentialPackedLoopMachine

/-! Construct all packed initial streams by scanning the actual original
input once. Position and clock counts are generated, not supplied as advice. -/
namespace Shallot.MacroPeg.CBV.SequentialPackedInitMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialCaptureCopyMachine (characters)

def input (X : List Nat) : Lists 8 := fun i => if i=6 then X else []

def stage (K : Nat) (C X R : List Nat) (p : Nat) : Lists 8 := fun i =>
  if i=0 then [0] ++ unary p else if i=2 then C else if i=3 then [0] ++ unary (K*(p+1))
  else if i=5 then R else if i=6 then X else []

def body (K : Nat) : LProg 8 := .seq (moveTop 6 5) (.seq (.push 0 1) (appendP 3 (unary K)))
def scan (K : Nat) : LProg 8 := .loop 6 nonEmpty (body K)
def seed (K : Nat) (C : List Nat) : LProg 8 := .seq (appendP 0 [0])
  (.seq (appendP 2 C) (appendP 3 ([0] ++ unary K)))
def program (K : Nat) (C : List Nat) : LProg 8 := .seq (seed K C) (.seq (scan K) (moveAll 5 6))

theorem input_fits (X : List Nat) {B : Nat} (hX : X.length+2 ≤ B) : LenOK B (input X) := by
  intro i
  by_cases hi : i=6 <;> simp [input,hi] <;> omega

theorem stage_fits (K : Nat) (C X R : List Nat) (p : Nat) {B : Nat}
    (hC : C.length+2 ≤ B) (hX : X.length+2 ≤ B) (hR : R.length+2 ≤ B)
    (hp : p+3 ≤ B) (hclock : K*(p+1)+3 ≤ B) : LenOK B (stage K C X R p) := by
  intro i
  by_cases h0 : i=0 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp [stage,h0,h2,h3,h5,h6] <;> omega

theorem body_runs (K : Nat) (C X R : List Nat) (v p : Nat) {B : Nat}
    (hL : LenOK B (stage K C (X ++ [v]) R p)) (hR : R.length+3 ≤ B)
    (hp : p+4 ≤ B) (hclock : K*(p+2)+3 ≤ B) :
    ∃ T, Runs (LenOK B) (body K) (stage K C (X ++ [v]) R p) (stage K C X (R ++ [v]) (p+1)) T := by
  let L := stage K C (X ++ [v]) R p
  let N := (L.set 6 X).set 5 (R ++ [v])
  have hm : Runs (LenOK B) (moveTop 6 5) L N 2 :=
    SequentialCaptureSpliceMachine.moveLast_runs (src := (6 : Fin 8)) (tmp := 5) (by decide) X v L rfl hL hR
  have hn : LenOK B N := end_fits hm
  let M := N.set 0 ([0] ++ unary p ++ [1])
  have hu : Runs (LenOK B) (.push 0 1) N M 1 := runs_push (i := (0 : Fin 8)) (e := 1) hn (by
    apply lenOK_set hn 0
    simpa [N,L,stage,Lists.set] using hp)
  have hh : Runs (LenOK B) (appendP 3 (unary K)) M (M.set 3 (M 3 ++ unary K)) ((unary K).length+1) :=
    append_runs (3 : Fin 8) (unary K) (end_fits hu) (by
      simp [M,N,L,stage,Lists.set,Nat.mul_succ]
      simp only [Nat.mul_succ] at hclock
      omega)
  have he : M.set 3 (M 3 ++ unary K)=stage K C X (R ++ [v]) (p+1) := by
    funext i
    by_cases h0 : i=0 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
      simp [M,N,L,stage,Lists.set,h0,h2,h3,h5,h6,List.replicate_succ',
        List.replicate_append_replicate,Nat.mul_succ,Nat.add_assoc]
  rw [he] at hh
  exact ⟨_,hm.seq (hu.seq hh)⟩

private theorem reverse_induction {P : List Nat → Prop} (nil : P [])
    (snoc : ∀ X v, P X → P (X ++ [v])) (X : List Nat) : P X := by
  have aux : ∀ Y : List Nat, P Y.reverse := by
    intro Y
    induction Y with
    | nil => exact nil
    | cons v Y ih => simpa only [List.reverse_cons] using snoc Y.reverse v ih
  simpa only [List.reverse_reverse] using aux X.reverse

theorem scan_runs (K : Nat) (C X R : List Nat) (p : Nat) {B : Nat}
    (hC : C.length+2 ≤ B) (hinput : R.length+X.length+2 ≤ B)
    (hcursor : p+X.length+3 ≤ B) (hclock : K*(p+X.length+1)+3 ≤ B) :
    ∃ T, Runs (LenOK B) (scan K) (stage K C X R p)
      (stage K C [] (R ++ X.reverse) (p+X.length)) T := by
  induction X using reverse_induction generalizing R p with
  | nil =>
    have hL := stage_fits K C [] R p hC (by simp at hcursor ⊢; omega) (by simpa using hinput)
      (by simpa using hcursor) (by simpa using hclock)
    have he : stage K C [] (R ++ [].reverse) (p+([] : List Nat).length)=stage K C [] R p := by simp
    rw [he]
    exact ⟨1,1,by omega,.loopF hL rfl⟩
  | snoc X v ih =>
    have hclock0 : K*(p+1)+3 ≤ B := by
      have hm := Nat.mul_le_mul_left K (show p+1 ≤ p+(X ++ [v]).length+1 by simp)
      omega
    have hL := stage_fits K C (X ++ [v]) R p hC (by simp at hinput ⊢; omega)
      (by simp at hinput; omega) (by simp at hcursor; omega) hclock0
    have hclock1 : K*(p+2)+3 ≤ B := by
      have hm := Nat.mul_le_mul_left K (show p+2 ≤ p+(X ++ [v]).length+1 by simp)
      omega
    obtain ⟨Tb,hb⟩ := body_runs K C X R v p hL (by simp at hinput; omega) (by simp at hcursor; omega) hclock1
    obtain ⟨Ti,hi⟩ := ih (R ++ [v]) (p+1) (by simp only [List.length_append,List.length_singleton] at hinput ⊢; omega)
      (by simp only [List.length_append,List.length_singleton] at hcursor ⊢; omega)
      (by simpa [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hclock)
    have he : stage K C [] ((R ++ [v]) ++ X.reverse) (p+1+X.length)=
        stage K C [] (R ++ (X ++ [v]).reverse) (p+(X ++ [v]).length) := by
      simp [List.reverse_append,List.append_assoc,Nat.add_comm,Nat.add_left_comm]
    rw [he] at hi
    obtain ⟨t1,ht1,hx1⟩ := hb
    obtain ⟨t2,ht2,hx2⟩ := hi
    exact ⟨t1+1+t2,t1+1+t2,by omega,.loopC hL (by simp [stage,lastSym_append,nonEmpty]) hx1 hx2⟩

theorem seed_runs (K : Nat) (C X : List Nat) {B : Nat}
    (hC : C.length+2 ≤ B) (hX : X.length+2 ≤ B) (hp : 3 ≤ B) (hclock : K+3 ≤ B) :
    ∃ T, Runs (LenOK B) (seed K C) (input X) (stage K C X [] 0) T := by
  let L := input X
  let N := L.set 0 [0]
  let M := N.set 2 C
  have hL := input_fits X hX
  have h0 : Runs (LenOK B) (appendP 0 [0]) L N 2 :=
    append_runs (0 : Fin 8) [0] hL (by simpa [L,input] using hp)
  have h2 : Runs (LenOK B) (appendP 2 C) N M (C.length+1) :=
    append_runs (2 : Fin 8) C (end_fits h0) (by simpa [N,L,input,Lists.set] using hC)
  have h3 : Runs (LenOK B) (appendP 3 ([0] ++ unary K)) M (M.set 3 ([0] ++ unary K))
      (([0] ++ unary K).length+1) :=
    append_runs (3 : Fin 8) ([0] ++ unary K) (end_fits h2)
      (by simpa [M,N,L,input,Lists.set,Nat.add_assoc] using hclock)
  have he : M.set 3 ([0] ++ unary K)=stage K C X [] 0 := by
    funext i
    by_cases h0 : i=0 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
      simp [M,N,L,input,stage,Lists.set,h0,h2,h3,h5,h6]
  rw [he] at h3
  exact ⟨_,h0.seq (h2.seq h3)⟩

theorem program_runs (K : Nat) (C X : List Nat) {B : Nat}
    (hC : C.length+2 ≤ B) (hX : X.length+2 ≤ B)
    (hcursor : X.length+3 ≤ B) (hclock : K*(X.length+1)+3 ≤ B) :
    ∃ T, Runs (LenOK B) (program K C) (input X) (stage K C X [] X.length) T := by
  have hk : K+3 ≤ B := by
    have hm := Nat.mul_le_mul_left K (show 1 ≤ X.length+1 by omega)
    simp only [Nat.mul_one] at hm
    omega
  obtain ⟨Ts,hs⟩ := seed_runs K C X hC hX (by omega) hk
  obtain ⟨Tl,hl⟩ := scan_runs K C X [] 0 hC (by simpa using hX) (by simpa using hcursor) (by simpa using hclock)
  let M := stage K C [] X.reverse X.length
  have hl' : Runs (LenOK B) (scan K) (stage K C X [] 0) M Tl := by simpa using hl
  have hM : LenOK B M := end_fits hl'
  have hr := moveAll_runs_bounded (src := (5 : Fin 8)) (dst := 6) (by decide) hM (by simpa [M,stage] using hX)
  have he : (M.set 6 (M 6 ++ (M 5).reverse)).set 5 []=stage K C X [] X.length := by
    funext i
    by_cases h0 : i=0 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
      simp [M,stage,Lists.set,h0,h2,h3,h5,h6]
  rw [he] at hr
  exact ⟨_,hs.seq (hl'.seq hr)⟩


def control (g : MGrammar) (e : MExp) : List Nat :=
  blocks [0,0,0,SequentialStackCodec.exprId (CBVtoCBN.compilerNodes g e) e]

def initProgram (g : MGrammar) (e : MExp) : LProg 8 := program (g.rules.length+1) (control g e)

theorem initial_shape (g : MGrammar) (x : List Char) (e : MExp) :
    stage (g.rules.length+1) (control g e) (characters x) [] x.length =
      SequentialPackedLoopMachine.state g x e (SequentialSharedWords.initial g x e) := by
  let ns := CBVtoCBN.compilerNodes g e
  have he : SequentialSharedStateCodec.encode ns (SequentialSharedWords.initial g x e)=
      (⟨SequentialCursorChain.encodeDeltas [SequentialClock.positionClock g x.length],
        SequentialCursorChain.encodeDeltas [0,0,0,SequentialStackCodec.exprId ns e],
        SequentialCursorChain.encode [x.length],[]⟩ : SequentialSharedStateCodec.Packed) := by
    rfl
  change _=SequentialCaptureCopyMachine.withInput (SequentialSharedStateCodec.encode ns _) x
  rw [he]
  have hb (n : Nat) : blocks [n]=[0] ++ unary n := by rw [blocks_cons]; rfl
  funext i
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | (change [0] ++ unary _=blocks [_]; rw [hb]; simp [SequentialClock.positionClock])

/-- Generate the real initial cursor, shared clock, and syntax control from
only the original input word, leaving that input intact. -/
theorem initialize_runs (g : MGrammar) (x : List Char) (e : MExp) :
    ∃ T, Runs (LenOK (SequentialPackedLoopMachine.capacity g e x.length)) (initProgram g e)
      (input (characters x)) (SequentialPackedLoopMachine.state g x e (SequentialSharedWords.initial g x e)) T := by
  have hf := SequentialPackedLoopMachine.reachable_fits g x e (SequentialSharedWords.initial g x e) (.refl _)
  rw [← initial_shape] at hf
  obtain ⟨T,ht⟩ := program_runs (g.rules.length+1) (control g e) (characters x)
    (by simpa [stage] using hf 2) (by simpa [stage] using hf 6)
    (by simpa [stage,characters,Nat.add_assoc] using hf 0)
    (by simpa [stage,characters,Nat.add_assoc] using hf 3)
  have hh : stage (g.rules.length+1) (control g e) (characters x) [] (characters x).length =
      SequentialPackedLoopMachine.state g x e (SequentialSharedWords.initial g x e) := by
    simpa only [characters,List.length_map] using initial_shape g x e
  rw [hh] at ht
  exact ⟨T,ht⟩

end Shallot.MacroPeg.CBV.SequentialPackedInitMachine
