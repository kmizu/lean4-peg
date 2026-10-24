import MacroPeg.CBV.StatefulScannerFamily

/-! Synchronize two independent finite-state scanners until either stops.
The actual compiled selector identifies both residual states together. -/
namespace Shallot.MacroPeg.CBV.StatefulScannerProduct
open StatefulScanner

def pack {n m : Nat} (a : Fin n) (b : Fin m) : Fin (n*m) :=
  ⟨a.val*m+b.val,by
    have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt a.isLt)
    simp only [Nat.succ_mul] at h
    have hb := b.isLt
    omega⟩

def left {n m : Nat} (hm : 0<m) (q : Fin (n*m)) : Fin n :=
  ⟨q.val/m,(Nat.div_lt_iff_lt_mul hm).mpr q.isLt⟩
def right {n m : Nat} (hm : 0<m) (q : Fin (n*m)) : Fin m :=
  ⟨q.val%m,Nat.mod_lt _ hm⟩

theorem left_pack {n m : Nat} (hm : 0<m) (a : Fin n) (b : Fin m) : left hm (pack a b) = a := by
  apply Fin.ext
  change (a.val*m+b.val)/m = a.val
  rw [Nat.add_comm (a.val*m) b.val,Nat.add_mul_div_right _ _ hm,Nat.div_eq_of_lt b.isLt,Nat.zero_add]
theorem right_pack {n m : Nat} (hm : 0<m) (a : Fin n) (b : Fin m) : right hm (pack a b) = b := by
  apply Fin.ext
  simp [right,pack,Nat.add_mod,Nat.mod_eq_of_lt b.isLt]

def joint {n m : Nat} (B : List (Char × Fin m)) :
    List (Char × Fin n) → List (Char × Fin (n*m))
  | [] => []
  | (c,a)::arcs => match next B c with
    | none => joint B arcs
    | some b => (c,pack a b)::joint B arcs

theorem next_joint {n m : Nat} (A : List (Char × Fin n)) (B : List (Char × Fin m)) (c : Char) :
    next (joint B A) c = (next A c).bind (fun a => (next B c).map (pack a)) := by
  induction A with
  | nil => rfl
  | cons arc A ih =>
    obtain ⟨d,a⟩ := arc
    by_cases hd : Shallot.beqChar d c = true
    · have he : d=c := by
        have hh : d.toNat=c.toNat := by simpa only [Shallot.beqChar,beq_iff_eq] using hd
        exact Char.toNat_inj.mp hh
      subst c
      cases hb : next B d <;> simp [joint,next,hb,Shallot.beqChar,ih]
    · cases hb : next B d <;> simp [joint,next,hb,hd,ih]

def product {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) : Machine (n*m) :=
  ⟨fun q => joint (B.arcs (right hm q)) (A.arcs (left hm q))⟩

theorem product_next {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (a : Fin n) (b : Fin m) (c : Char) :
    next ((product A B hm).arcs (pack a b)) c =
      (next (A.arcs a) c).bind (fun a => (next (B.arcs b) c).map (pack a)) := by
  simp only [product,left_pack,right_pack,next_joint]

def common {n m : Nat} (A : Machine n) (B : Machine m) :
    Fin n → Fin m → List Char → (Fin n × Fin m) × List Char
  | a,b,[] => ((a,b),[])
  | a,b,c::x => match next (A.arcs a) c,next (B.arcs b) c with
    | some a',some b' => common A B a' b' x
    | _,_ => ((a,b),c::x)

theorem run_product {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (a : Fin n) (b : Fin m) (x : List Char) :
    run (product A B hm) (pack a b) x =
      (pack (common A B a b x).1.1 (common A B a b x).1.2,(common A B a b x).2) := by
  induction x generalizing a b with
  | nil => rfl
  | cons c x ih =>
    rw [run,product_next]
    cases ha : next (A.arcs a) c <;> cases hb : next (B.arcs b) c <;>
      simp only [Option.bind_none,Option.bind_some,Option.map_none,Option.map_some,common,ha,hb]
    exact ih _ _

/-- Both original scanners can resume from the exact states at the common
frontier, even when their state transitions depend on all earlier symbols. -/
theorem residual_runs {n m : Nat} (A : Machine n) (B : Machine m)
    (a : Fin n) (b : Fin m) (x : List Char) :
    run A a x = run A (common A B a b x).1.1 (common A B a b x).2 ∧
    run B b x = run B (common A B a b x).1.2 (common A B a b x).2 := by
  induction x generalizing a b with
  | nil => exact ⟨rfl,rfl⟩
  | cons c x ih =>
    cases ha : next (A.arcs a) c <;> cases hb : next (B.arcs b) c <;>
      simp only [common,ha,hb]
    · constructor <;> trivial
    · constructor <;> trivial
    · constructor <;> trivial
    · simpa only [run,ha,hb] using ih _ _

/-- The common frontier is reached by consuming one actual shared prefix,
and each independently running source scanner reaches the recorded state. -/
theorem common_prefix {n m : Nat} (A : Machine n) (B : Machine m)
    (a : Fin n) (b : Fin m) (x : List Char) :
    ∃ word, x = word ++ (common A B a b x).2 ∧
      advance A a word = some (common A B a b x).1.1 ∧
      advance B b word = some (common A B a b x).1.2 := by
  induction x generalizing a b with
  | nil => exact ⟨[],rfl,rfl,rfl⟩
  | cons c x ih =>
    cases ha : next (A.arcs a) c <;> cases hb : next (B.arcs b) c <;>
      simp only [common,ha,hb]
    · exact ⟨[],rfl,rfl,rfl⟩
    · exact ⟨[],rfl,rfl,rfl⟩
    · exact ⟨[],rfl,rfl,rfl⟩
    · obtain ⟨word,hw,hA,hB⟩ := ih _ _
      refine ⟨c::word,?_,?_,?_⟩
      · exact congrArg (List.cons c) hw
      · simpa only [advance,ha,Option.bind_some] using hA
      · simpa only [advance,hb,Option.bind_some] using hB

/-- This is an actual fixed-grammar runtime probe for the pair of residual
states. Neither reached state nor the common-prefix length is an input. -/
theorem common_probe {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (a : Fin n) (b : Fin m) (x : List Char) (s : Strategy) (hs : s ≠ .callByName) :
    SObs (StatefulScannerFamily.grammar (product A B hm)) s
      (StatefulScannerFamily.probe (pack a b)
        (pack (common A B a b x).1.1 (common A B a b x).1.2)) x (some x) := by
  have he := StatefulScannerFamily.probe_observation (product A B hm) x s hs (pack a b)
    (pack (common A B a b x).1.1 (common A B a b x).1.2)
  simpa only [run_product,if_true] using he


theorem pack_eq_iff {n m : Nat} (hm : 0<m) (a c : Fin n) (b d : Fin m) :
    pack a b = pack c d ↔ a=c ∧ b=d := by
  constructor
  · intro h
    exact ⟨by simpa only [left_pack] using congrArg (left hm) h,
      by simpa only [right_pack] using congrArg (right hm) h⟩
  · rintro ⟨rfl,rfl⟩; rfl

/-- Every candidate state pair has its own fixed prefix parser in the same
compiled grammar; an incorrect candidate fails finitely on the real input. -/
theorem common_entry {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (a c : Fin n) (b d : Fin m) (x : List Char) (s : Strategy) (hs : s ≠ .callByName) :
    SObs (StatefulScannerFamily.grammar (product A B hm)) s
      (StatefulScannerFamily.entry (pack a b) (pack c d)) x
      (if (common A B a b x).1.1=c ∧ (common A B a b x).1.2=d
        then some (common A B a b x).2 else none) := by
  simpa only [run_product,pack_eq_iff hm] using
    StatefulScannerFamily.entry_observation (product A B hm) x s hs (pack a b) (pack c d)

theorem common_probe_observation {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (a c : Fin n) (b d : Fin m) (x : List Char) (s : Strategy) (hs : s ≠ .callByName) :
    SObs (StatefulScannerFamily.grammar (product A B hm)) s
      (StatefulScannerFamily.probe (pack a b) (pack c d)) x
      (if (common A B a b x).1.1=c ∧ (common A B a b x).1.2=d then some x else none) := by
  simpa only [run_product,pack_eq_iff hm] using
    StatefulScannerFamily.probe_observation (product A B hm) x s hs (pack a b) (pack c d)

/-- At a nonempty common frontier at least one source scanner has no next
transition. Both may stop, which gives a coincident endpoint. -/
theorem frontier_stops {n m : Nat} (A : Machine n) (B : Machine m)
    (a : Fin n) (b : Fin m) (x : List Char) : ∀ c rest,
    (common A B a b x).2 = c::rest →
      next (A.arcs (common A B a b x).1.1) c = none ∨
      next (B.arcs (common A B a b x).1.2) c = none := by
  induction x generalizing a b with
  | nil => intro c rest h; cases h
  | cons ch x ih =>
    cases ha : next (A.arcs a) ch <;> cases hb : next (B.arcs b) ch <;>
      simp only [common,ha,hb]
    · intro c rest h; cases h; exact Or.inl ha
    · intro c rest h; cases h; exact Or.inl ha
    · intro c rest h; cases h; exact Or.inr hb
    · exact ih _ _


/-- The selected common prefix is an actual captured Seq argument, with
both reached states selected through finite static rule slots. -/
theorem common_capture {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (a c : Fin n) (b d : Fin m) (x : List Char) (clock : Nat) (hclock : x.length+1 ≤ clock) :
    evSeqArgs (StatefulScannerFamily.grammar (product A B hm)) x .callByValueSeq
      (tblV (StatefulScannerFamily.grammar (product A B hm)) x .callByValueSeq clock) []
      [StatefulScannerFamily.entry (pack a b) (pack c d)] x.length =
      some (if (common A B a b x).1.1=c ∧ (common A B a b x).1.2=d then
        some ([pre x x.length (common A B a b x).2.length],(common A B a b x).2.length) else none) := by
  simpa only [sfx_self,run_product,pack_eq_iff hm] using
    StatefulScannerFamily.capture_eval (product A B hm) x (pack a b) (pack c d) []
      x.length clock (Nat.le_refl _) hclock

end Shallot.MacroPeg.CBV.StatefulScannerProduct
