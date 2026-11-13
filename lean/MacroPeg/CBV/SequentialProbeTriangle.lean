import MacroPeg.CBV.SequentialProbeTrace

/-! A fixed source evaluation makes quadratically many distinct Seq row
requests on a linear-size input family. This obstructs a linear bound for
literal memoization of source calls. The target rule is epsilon: a compiler
can erase these calls, so this is not a language lower bound or a lower bound
for all evaluators, preprocessing schemes, or dynamic data structures. -/
namespace Shallot.MacroPeg.CBV.SequentialProbeTriangle

open SequentialProbeTrace (Request)

def as (n : Nat) : List Char := List.replicate n 'a'
def input (n : Nat) : List Char := as n ++ '#' :: as n ++ ['#']
def scan : MExp := .star (.chr 'a')
def inner : MExp := .seq (.andP (.call 1 [.param 0, scan])) (.chr 'a')
def body : MExp := .seq (.chr '#') (.seq (.star inner) (.seq scan (.chr '#')))
def grammar : MGrammar := ⟨[⟨1,body⟩,⟨2,.eps⟩]⟩
def outer : MExp := .seq (.andP (.call 0 [scan])) (.chr 'a')
def start : MExp := .seq (.star outer) (.seq (.chr '#') (.seq scan (.chr '#')))

def targets (n : Nat) : List Request :=
  (SequentialProbeTrace.run grammar (input n) 2 start).2.filter (fun r => r.rule == 1)

def request (m r : Nat) : Request := ⟨1, [(m+r+1,r+1),(r+1,1)], 1⟩

def row (m t : Nat) : List Request :=
  ((List.range (t+1)).reverse).map (request m)

def triangle (n : Nat) : List Request :=
  ((List.range (n+1)).reverse).flatMap (fun m => row m (n-m))

private theorem scan_suffix (g : MGrammar) (x : List Char) (Q : SequentialProbeTrace.Query)
    (E : SequentialSpanRecompute.Env) : ∀ m pre0 tail,
    x = pre0 ++ (as m ++ '#' :: tail) →
    SequentialProbeTrace.eval g x Q E scan (m + tail.length + 1) =
      (some (some (tail.length+1)), []) := by
  intro m
  induction m with
  | zero =>
    intro pre0 tail hx
    have hs : sfx x (tail.length+1) = '#' :: tail := by
      simpa [as] using (sfx_suffix hx)
    change SequentialProbeTrace.star _ (0 + tail.length + 1) = _
    simp only [Nat.zero_add]
    apply SequentialProbeTrace.star_fail
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, hs, Shallot.beqChar]
  | succ m ih =>
    intro pre0 tail hx
    have hs : sfx x (m+1+tail.length+1) = 'a' :: (as m ++ '#' :: tail) := by
      simpa [as, List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (sfx_suffix hx)
    have hh : SequentialProbeTrace.eval g x Q E (.chr 'a') (m+1+tail.length+1) =
        (some (some (m+tail.length+1)), []) := by
      simp only [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, hs]
      simp [as, Shallot.beqChar, Nat.add_assoc]
    have hx' : x = (pre0 ++ ['a']) ++ (as m ++ '#' :: tail) := by
      simpa [as, List.replicate_succ, List.append_assoc] using hx
    have ht := ih (pre0 ++ ['a']) tail hx'
    change SequentialProbeTrace.star _ (m+1+tail.length+1) = _
    rw [SequentialProbeTrace.star_step hh (by omega)]
    change ((SequentialProbeTrace.eval g x Q E scan (m+tail.length+1)).1,
      [] ++ (SequentialProbeTrace.eval g x Q E scan (m+tail.length+1)).2) = _
    simp [ht]

private theorem split_first {n m : Nat} (hm : m ≤ n) :
    input n = as (n-m) ++ (as m ++ '#' :: (as n ++ ['#'])) := by
  have hr : as (n-m) ++ as m = as n := by simp [as, Nat.sub_add_cancel hm]
  simp only [input, List.append_assoc, List.cons_append]
  rw [← List.append_assoc, hr]

private theorem split_second {n k : Nat} (hk : k ≤ n) :
    input n = (as n ++ '#' :: as (n-k)) ++ (as k ++ ['#']) := by
  have hr : as (n-k) ++ as k = as n := by simp [as, Nat.sub_add_cancel hk]
  simp only [input, List.append_assoc, List.cons_append]
  rw [← List.append_assoc (as (n-k)), hr]

private theorem first_suffix {n m : Nat} (hm : m ≤ n) :
    sfx (input n) (m+n+2) = as m ++ '#' :: (as n ++ ['#']) := by
  simpa [as, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (sfx_suffix (split_first hm))

private theorem second_suffix {n k : Nat} (hk : k ≤ n) :
    sfx (input n) (k+1) = as k ++ ['#'] := by
  simpa [as] using (sfx_suffix (split_second hk))

private theorem match_count (tail : List Char) : ∀ m k,
    SequentialSpanRecompute.matchCount m (as m ++ '#' :: tail) (as k ++ ['#']) =
      if m ≤ k then some (k-m+1) else none := by
  intro m
  induction m with
  | zero => intro k; simp [SequentialSpanRecompute.matchCount, as]
  | succ m ih =>
    intro k
    cases k with
    | zero => simp [as, List.replicate_succ, SequentialSpanRecompute.matchCount, Shallot.beqChar]
    | succ k => simpa [as, List.replicate_succ, SequentialSpanRecompute.matchCount,
        Shallot.beqChar, Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub] using ih k

private theorem param_result {n m k : Nat} (hm : m ≤ n) (hk : k ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 1)
      [(m+n+2,n+2)] (.param 0) (k+1) =
      (some (if m ≤ k then some (k-m+1) else none), []) := by
  simp only [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, List.getElem?_cons_zero]
  simp only [SequentialSpanRecompute.matchSpan]
  rw [show m+n+2-(n+2)=m by omega, first_suffix hm, second_suffix hk, match_count]

private theorem target_query (n q : Nat) (W : SequentialSpanRecompute.Env)
    (hq : q ≤ (input n).length) :
    SequentialProbeTrace.query grammar (input n) 1 1 W q = (some (some q), []) := by
  simp [SequentialProbeTrace.query, hq, grammar, ruleAtM, SequentialProbeTrace.eval,
    SequentialSpanRecompute.eval]

private theorem scan_second (n k : Nat) (hk : k ≤ n) (Q : SequentialProbeTrace.Query)
    (E : SequentialSpanRecompute.Env) :
    SequentialProbeTrace.eval grammar (input n) Q E scan (k+1) = (some (some 1), []) := by
  simpa using (scan_suffix grammar (input n) Q E k (as n ++ '#' :: as (n-k)) [] (split_second hk))

private theorem inner_result {n m k : Nat} (hm : m ≤ n) (hk : k ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 1)
      [(m+n+2,n+2)] inner (k+1) =
      if m ≤ k then
        (if k = 0 then some none else some (some k), [request m (k-m)])
      else (some none, []) := by
  have hp := param_result hm hk
  by_cases hmk : m ≤ k
  · have hs := scan_second n (k-m) (by omega)
      (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)]
    have hq := target_query n 1 [(k+1,k-m+1),(k-m+1,1)] (by simp [input,as]; omega)
    have hargs : SequentialProbeTrace.evalArgs grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)] [.param 0, scan] (k+1) =
        (some (some ([(k+1,k-m+1),(k-m+1,1)],1)), []) := by
      rw [SequentialProbeTrace.evalArgs, hp]
      simp only [if_pos hmk]
      rw [SequentialProbeTrace.evalArgs, hs]
      simp [SequentialProbeTrace.evalArgs, Nat.min_eq_left (show k-m+1 ≤ k+1 by omega),
        Nat.min_eq_left (show 1 ≤ k-m+1 by omega)]
    have hcall : SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)]
        (.call 1 [.param 0,scan]) (k+1) = (some (some 1), [request m (k-m)]) := by
      rw [SequentialProbeTrace.eval]
      simp only [show ruleAtM grammar.rules 1 = some ⟨2,.eps⟩ by rfl, List.length_cons, List.length_nil, ite_true, hargs]
      simp [hq, request, show m+(k-m)+1=k+1 by omega]
    have hand : SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)]
        (.andP (.call 1 [.param 0,scan])) (k+1) =
        (some (some (k+1)), [request m (k-m)]) := by
      rw [MExp.andP, SequentialProbeTrace.eval, SequentialProbeTrace.eval, hcall]
    rw [inner, SequentialProbeTrace.eval, hand]
    simp only [if_pos hmk]
    cases k with
    | zero => simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval,
        second_suffix (n := n) (k := 0) (by omega), as, Shallot.beqChar]
    | succ k =>
      simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, second_suffix hk,
        as, List.replicate_succ, Shallot.beqChar]
  · have hargs : SequentialProbeTrace.evalArgs grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)] [.param 0, scan] (k+1) =
        (some none, []) := by
      rw [SequentialProbeTrace.evalArgs, hp]
      simp [hmk]
    have hcall : SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)]
        (.call 1 [.param 0,scan]) (k+1) = (some none, []) := by
      rw [SequentialProbeTrace.eval]
      simp only [show ruleAtM grammar.rules 1 = some ⟨2,.eps⟩ by rfl, List.length_cons, List.length_nil, ite_true, hargs]
    rw [inner, SequentialProbeTrace.eval, MExp.andP, SequentialProbeTrace.eval,
      SequentialProbeTrace.eval, hcall]
    simp [hmk]

private theorem row_succ (m t : Nat) : row m (t+1) = request m (t+1) :: row m t := by
  simp [row, List.range_succ, List.reverse_append]

private theorem inner_star {n m k : Nat} (hm : m ≤ n) (hk : k ≤ n) (hmk : m ≤ k) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 1)
      [(m+n+2,n+2)] (.star inner) (k+1) =
      (some (some (max m 1)), row m (k-m)) := by
  induction k with
  | zero =>
    have hm0 : m=0 := by omega
    subst m
    change SequentialProbeTrace.star _ 1 = _
    rw [SequentialProbeTrace.star_fail (by simpa using inner_result hm hk)]
    rfl
  | succ k ih =>
    have hh := inner_result hm hk
    simp only [if_pos hmk, Nat.succ_ne_zero, if_false] at hh
    change SequentialProbeTrace.star _ (k+1+1) = _
    rw [SequentialProbeTrace.star_step hh (by omega)]
    by_cases hprev : m ≤ k
    · have ht := ih (by omega) hprev
      change ((SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)] (.star inner) (k+1)).1,
        [request m (k+1-m)] ++ (SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)] (.star inner) (k+1)).2) = _
      rw [ht]
      simp only [List.singleton_append]
      rw [show k+1-m=(k-m)+1 by omega, row_succ]
    · have hm' : m=k+1 := by omega
      have hf := inner_result hm (show k≤n by omega)
      simp only [if_neg hprev] at hf
      rw [SequentialProbeTrace.star_fail hf]
      simp [hm', row, Nat.max_eq_left (show 1 ≤ k+1 by omega)]

private theorem body_result {n m : Nat} (hm : m ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 1)
      [(m+n+2,n+2)] body (n+2) = (some (some 0), row m (n-m)) := by
  have hhead : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)] (.chr '#') (n+2) =
      (some (some (n+1)), []) := by
    have hs := first_suffix (n := n) (m := 0) (by omega)
    simp only [Nat.zero_add] at hs
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, hs, as, Shallot.beqChar]
  have hstar := inner_star hm (Nat.le_refl n) hm
  have hscan := scan_second n (max m 1 - 1) (by omega)
    (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)]
  rw [show max m 1 - 1 + 1 = max m 1 by omega] at hscan
  have hclose : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 1) [(m+n+2,n+2)] (.chr '#') 1 =
      (some (some 0), []) := by
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval,
      second_suffix (n := n) (k := 0) (by omega), as, Shallot.beqChar]
  rw [body, SequentialProbeTrace.eval, hhead]
  simp only []
  rw [SequentialProbeTrace.eval, hstar]
  simp only []
  rw [SequentialProbeTrace.eval, hscan]
  simp [hclose]

def frameRequest (n m : Nat) : Request := ⟨0, [(m+n+2,n+2)], n+2⟩

def outerTrace (n m : Nat) : List Request :=
  ((List.range (m+1)).reverse).flatMap (fun j => frameRequest n j :: row j (n-j))

private theorem outer_result {n m : Nat} (hm : m ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 2)
      [] outer (m+n+2) =
      (if m=0 then some none else some (some (m+n+1)), frameRequest n m :: row m (n-m)) := by
  have hscan : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] scan (m+n+2) =
      (some (some (n+2)), []) := by
    simpa [as, Nat.add_assoc] using (scan_suffix grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] m (as (n-m))
      (as n ++ ['#']) (split_first hm))
  have hb := body_result hm
  have hq : SequentialProbeTrace.query grammar (input n) 2 0 [(m+n+2,n+2)] (n+2) =
      (some (some 0), row m (n-m)) := by
    rw [SequentialProbeTrace.query]
    dsimp only []
    rw [if_pos (show n+2 ≤ (input n).length by simp [input,as])]
    simpa only [show ruleAtM grammar.rules 0 = some ⟨1,body⟩ by rfl] using hb
  have hargs : SequentialProbeTrace.evalArgs grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] [scan] (m+n+2) =
      (some (some ([(m+n+2,n+2)],n+2)), []) := by
    rw [SequentialProbeTrace.evalArgs, hscan]
    simp [SequentialProbeTrace.evalArgs, Nat.min_eq_left (show n+2 ≤ m+n+2 by omega)]
  have hcall : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.call 0 [scan]) (m+n+2) =
      (some (some 0), frameRequest n m :: row m (n-m)) := by
    rw [SequentialProbeTrace.eval]
    simp only [show ruleAtM grammar.rules 0 = some ⟨1,body⟩ by rfl,
      List.length_cons, List.length_nil, ite_true, hargs]
    simp [hq, frameRequest]
  have hand : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.andP (.call 0 [scan])) (m+n+2) =
      (some (some (m+n+2)), frameRequest n m :: row m (n-m)) := by
    rw [MExp.andP, SequentialProbeTrace.eval, SequentialProbeTrace.eval, hcall]
  rw [outer, SequentialProbeTrace.eval, hand]
  cases m with
  | zero =>
    have hsf := first_suffix hm
    simp only [Nat.zero_add] at hsf
    simp only [Nat.zero_add, SequentialProbeTrace.eval, SequentialSpanRecompute.eval, hsf]
    simp [as, Shallot.beqChar]
  | succ m =>
    simp only [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, first_suffix hm]
    simp [as, List.replicate_succ, Shallot.beqChar, Nat.add_assoc]
    omega

private theorem outer_star {n m : Nat} (hm : m ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 2)
      [] (.star outer) (m+n+2) = (some (some (n+2)), outerTrace n m) := by
  induction m with
  | zero =>
    have hh := outer_result hm
    simp only [ite_true, Nat.zero_add] at hh
    change SequentialProbeTrace.star _ (0+n+2) = _
    simp only [Nat.zero_add]
    rw [SequentialProbeTrace.star_fail hh]
    simp [outerTrace]
  | succ m ih =>
    have hh := outer_result hm
    simp only [Nat.succ_ne_zero, if_false] at hh
    change SequentialProbeTrace.star _ (m+1+n+2) = _
    rw [SequentialProbeTrace.star_step hh (by omega)]
    have ht := ih (show m≤n by omega)
    rw [show m+1+n+1=m+n+2 by omega]
    change ((SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.star outer) (m+n+2)).1,
      (frameRequest n (m+1) :: row (m+1) (n-(m+1))) ++
      (SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.star outer) (m+n+2)).2) = _
    rw [ht]
    simp [outerTrace, List.range_succ, List.reverse_append]

theorem run_formula (n : Nat) :
    SequentialProbeTrace.run grammar (input n) 2 start = (some (some 0), outerTrace n n) := by
  have hstar := outer_star (Nat.le_refl n)
  have hs := scan_second n n (Nat.le_refl _) (SequentialProbeTrace.query grammar (input n) 2) []
  have hhead : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.chr '#') (n+2) =
      (some (some (n+1)), []) := by
    have hx := first_suffix (n := n) (m := 0) (by omega)
    simp only [Nat.zero_add] at hx
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, hx, as, Shallot.beqChar]
  have hclose : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.chr '#') 1 =
      (some (some 0), []) := by
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval,
      second_suffix (n := n) (k := 0) (by omega), as, Shallot.beqChar]
  unfold SequentialProbeTrace.run
  rw [show (input n).length = n+n+2 by simp [input,as]; omega]
  rw [start, SequentialProbeTrace.eval, hstar]
  simp only []
  rw [SequentialProbeTrace.eval, hhead]
  simp only []
  rw [SequentialProbeTrace.eval, hs]
  simp [hclose]

theorem targets_eq_triangle (n : Nat) : targets n = triangle n := by
  unfold targets
  rw [run_formula]
  have hf (xs : List Nat) : xs.filter (fun _ => true) = xs :=
    List.filter_eq_self.mpr (by intro a ha; rfl)
  simp [outerTrace, triangle, List.filter_flatMap, List.filter_map, row, frameRequest, request, Function.comp_def, hf]

theorem request_injective {m r m' r' : Nat} (h : request m r = request m' r') :
    m=m' ∧ r=r' := by
  simp only [request, Request.mk.injEq, List.cons.injEq, Prod.mk.injEq] at h
  omega

private theorem row_mem {m t : Nat} {req : Request} :
    req ∈ row m t ↔ ∃ r, r≤t ∧ request m r = req := by
  simp only [row, List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨r, hr, he⟩; exact ⟨r, by omega, he⟩
  · rintro ⟨r, hr, he⟩; exact ⟨r, by omega, he⟩

private theorem row_nodup (m t : Nat) : (row m t).Nodup := by
  unfold row
  apply List.Pairwise.map (R := fun a b : Nat => a ≠ b) _
    (fun a b hab he => hab (request_injective he).2)
  exact List.pairwise_reverse.mpr (List.nodup_range.imp (fun h => Ne.symm h))

private theorem blocks_nodup (n : Nat) (ms : List Nat) (hms : ms.Nodup) :
    (ms.flatMap (fun m => row m (n-m))).Nodup := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    rw [List.nodup_cons] at hms
    simp only [List.flatMap_cons, List.Nodup, List.pairwise_append]
    refine ⟨row_nodup _ _, ih hms.2, ?_⟩
    intro a ha b hb he
    obtain ⟨r, hr, rfl⟩ := row_mem.mp ha
    obtain ⟨m', hm', hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨r', hr', rfl⟩ := row_mem.mp hb
    have heq := (request_injective he).1
    subst m'
    exact hms.1 hm'

theorem targets_nodup (n : Nat) : (targets n).Nodup := by
  rw [targets_eq_triangle]
  exact blocks_nodup n _ (List.pairwise_reverse.mpr
    (List.nodup_range.imp (fun h => Ne.symm h)))

private theorem triangle_length_succ (n : Nat) :
    (triangle (n+1)).length = (n+2) + (triangle n).length := by
  simp only [triangle, List.length_flatMap, List.map_reverse, List.sum_reverse,
    row, List.length_map, List.length_reverse, List.length_range]
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def, Nat.succ_sub_succ_eq_sub]

theorem targets_count (n : Nat) : 2 * (targets n).length = (n+1)*(n+2) := by
  rw [targets_eq_triangle]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [triangle_length_succ, Nat.mul_add, ih]
    simp only [Nat.succ_mul, Nat.mul_succ]
    omega

theorem targets_mem (n : Nat) (req : Request) :
    req ∈ targets n ↔ ∃ m r, m+r≤n ∧ request m r = req := by
  rw [targets_eq_triangle]
  simp only [triangle, List.mem_flatMap, List.mem_reverse, List.mem_range, row_mem]
  constructor
  · rintro ⟨m, hm, r, hr, he⟩
    exact ⟨m,r,by omega,he⟩
  · rintro ⟨m,r,hmr,he⟩
    exact ⟨m,by omega,r,by omega,he⟩

theorem input_length (n : Nat) : (input n).length = 2*n+2 := by simp [input,as]; omega

theorem no_linear_cache_bound :
    ∀ C : Nat, ∃ n, C * ((input n).length + 1) < (targets n).length := by
  intro C
  refine ⟨4*C+4, ?_⟩
  have hc := targets_count (4*C+4)
  rw [input_length]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hc ⊢
  have hp := Nat.mul_left_comm C 2 (4*C)
  omega

theorem request_words {n m r : Nat} (hmr : m+r≤n) :
    SequentialSpanRecompute.decodeEnv (input n) (request m r).env = [as m, as r] := by
  have hp : pre (input n) (m+r+1) (r+1) = as m := by
    simp only [pre, second_suffix hmr, show m+r+1-(r+1)=m by omega]
    simp [as, List.take_append, Nat.min_eq_left (show m ≤ m+r by omega)]
  have ht : pre (input n) (r+1) 1 = as r := by
    simp [pre, second_suffix (show r≤n by omega), as]
  simp only [request, SequentialSpanRecompute.decodeEnv, List.map_cons, List.map_nil, hp, ht]

theorem targets_word_keys_nodup (n : Nat) :
    ((targets n).map (fun req =>
      (req.rule, SequentialSpanRecompute.decodeEnv (input n) req.env, req.cursor))).Nodup := by
  apply List.pairwise_map.mpr
  apply (targets_nodup n).imp_of_mem
  intro a b ha hb hne he
  obtain ⟨m,r,hmr,rfl⟩ := (targets_mem n a).mp ha
  obtain ⟨m',r',hmr',rfl⟩ := (targets_mem n b).mp hb
  have hw : [as m, as r] = [as m', as r'] := by
    have hw := congrArg (fun key : Nat × List (List Char) × Nat => key.2.1) he
    change SequentialSpanRecompute.decodeEnv (input n) (request m r).env =
      SequentialSpanRecompute.decodeEnv (input n) (request m' r').env at hw
    simpa only [request_words hmr, request_words hmr'] using hw
  have hm : m=m' := by
    have hh := congrArg List.length (List.cons.inj hw).1
    simpa [as] using hh
  have hr : r=r' := by
    have hh := congrArg List.length (List.cons.inj (List.cons.inj hw).2).1
    simpa [as] using hh
  subst m'; subst r'
  exact hne rfl

theorem targets_one_cursor (n : Nat) : ∀ req ∈ targets n, req.cursor=1 := by
  intro req hreq
  obtain ⟨m,r,hmr,rfl⟩ := (targets_mem n req).mp hreq
  rfl

theorem grammar_firstOrder : grammar.FirstOrder := by
  intro r hr
  simp only [grammar, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    simp [body, inner, scan, MExp.andP, MExp.FirstOrder, MExp.FirstOrderArgs]

theorem start_firstOrder : start.FirstOrder := by
  simp [start, outer, scan, MExp.andP, MExp.FirstOrder, MExp.FirstOrderArgs]

theorem source_accepts (n : Nat) : SObs grammar .callByValueSeq start (input n) (some []) := by
  have hv : evV grammar (input n) .callByValueSeq (tblV grammar (input n) .callByValueSeq 2)
      [] start (input n).length = some (some 0) := by
    rw [← SequentialProbeTrace.run_correct, run_formula]
  obtain ⟨out,hd,ho⟩ := evV_derives grammar_firstOrder (by decide) start_firstOrder 2 (Nat.le_refl _) hv
  cases out with
  | fail => cases ho
  | ok tree rest =>
    have hr : rest=[] := List.eq_nil_of_length_eq_zero (by simpa [obsR] using ho)
    subst rest
    exact ⟨_, by simpa only [sfx_self] using hd, rfl⟩


end Shallot.MacroPeg.CBV.SequentialProbeTriangle
