import MacroPeg.CBV.SequentialSharedWordSpace

/-! An invertible binary encoding of bounded increasing cursor lists.
Only differences are written in unary, so the data bits telescope. -/
namespace Shallot.MacroPeg.CBV.SequentialCursorChain

inductive Chain : Nat → List Nat → Nat → Prop where
  | nil {p n} (hp : p ≤ n) : Chain p [] n
  | cons {p q n qs} (hp : p ≤ q) (tail : Chain q qs n) : Chain p (q :: qs) n

theorem Chain.bound {p n : Nat} {ps : List Nat} (h : Chain p ps n) : p ≤ n := by
  induction h with
  | nil hp => exact hp
  | cons hp ht ih => omega

theorem Chain.lower {p q n : Nat} {ps : List Nat} (h : Chain q ps n) (hp : p ≤ q) :
    Chain p ps n := by
  cases h with
  | nil hq => exact .nil (Nat.le_trans hp hq)
  | cons hq ht => exact .cons (Nat.le_trans hp hq) ht

def deltas (p : Nat) : List Nat → List Nat
  | [] => []
  | q :: qs => (q-p) :: deltas q qs

def restore (p : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => (p+d) :: restore (p+d) ds

theorem Chain.restore {p n : Nat} {ps : List Nat} (h : Chain p ps n) :
    restore p (deltas p ps) = ps := by
  induction h with
  | nil => rfl
  | @cons p q n qs hp ht ih =>
    have he : p + (q-p) = q := by omega
    simp only [deltas,SequentialCursorChain.restore,he,ih]

theorem Chain.delta_sum {p n : Nat} {ps : List Nat} (h : Chain p ps n) :
    (deltas p ps).sum ≤ n-p := by
  induction h with
  | nil => simp [deltas]
  | cons hp ht ih =>
    have hb := ht.bound
    simp only [deltas,List.sum_cons]
    omega

theorem deltas_length (p : Nat) (ps : List Nat) : (deltas p ps).length = ps.length := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih => simp only [deltas,List.length_cons,ih]

/-- A run of `true` bits is a nonnegative difference; `false` terminates it. -/
def encodeDeltas : List Nat → List Bool
  | [] => []
  | d :: ds => List.replicate d true ++ false :: encodeDeltas ds

def decodeDeltas : List Bool → Option (List Nat)
  | [] => some []
  | false :: bs => (decodeDeltas bs).map (0 :: ·)
  | true :: bs =>
    match decodeDeltas bs with
    | some (d :: ds) => some ((d+1) :: ds)
    | _ => none

theorem decodeDeltas_block (d : Nat) (bs : List Bool) :
    decodeDeltas (List.replicate d true ++ false :: bs) = (decodeDeltas bs).map (d :: ·) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [List.replicate_succ,List.cons_append,decodeDeltas,ih]
    cases decodeDeltas bs <;> rfl

theorem decodeDeltas_encodeDeltas (ds : List Nat) :
    decodeDeltas (encodeDeltas ds) = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [encodeDeltas,decodeDeltas_block,ih,Option.map_some]

theorem encodeDeltas_length (ds : List Nat) :
    (encodeDeltas ds).length = ds.sum + ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [encodeDeltas,List.length_append,List.length_replicate,List.length_cons,
      List.sum_cons,ih]
    omega

def encode (ps : List Nat) : List Bool := encodeDeltas (deltas 0 ps)
def decode (bs : List Bool) : Option (List Nat) := (decodeDeltas bs).map (restore 0)

theorem Chain.decode_encode {n : Nat} {ps : List Nat} (h : Chain 0 ps n) :
    decode (encode ps) = some ps := by
  simp only [decode,encode,decodeDeltas_encodeDeltas,Option.map_some,h.restore]

theorem Chain.encode_length {n : Nat} {ps : List Nat} (h : Chain 0 ps n) :
    (encode ps).length ≤ n + ps.length := by
  have hs := h.delta_sum
  simp only [encode,encodeDeltas_length,deltas_length]
  omega

/-- Saturating subtraction is lossless on the proved increasing domain. -/
theorem Chain.encode_injective {n m : Nat} {ps qs : List Nat}
    (hp : Chain 0 ps n) (hq : Chain 0 qs m) (he : encode ps = encode qs) : ps = qs := by
  have hh := congrArg decode he
  simpa only [hp.decode_encode,hq.decode_encode,Option.some.injEq] using hh

end Shallot.MacroPeg.CBV.SequentialCursorChain
