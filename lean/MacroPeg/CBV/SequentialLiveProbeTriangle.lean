import MacroPeg.CBV.SequentialProbeTriangle
import MacroPeg.CBV.CaptureReadSupport
import MacroPeg.CBV.LiveCaptureQuotient

/-! Test literal call caching after removing unused fields and replacing
retained words by their exact future-context profiles. This is a source-trace
obstruction, not a language lower bound or a lower bound for all evaluators. -/
namespace Shallot.MacroPeg.CBV.SequentialLiveProbeTriangle

open SequentialProbeTrace (Request)

def as (n : Nat) : List Char := List.replicate n 'a'
def input (n : Nat) : List Char := as n ++ '#' :: as n ++ '#' :: as n
def scan : MExp := .star (.chr 'a')
def inner : MExp := .seq (.andP (.call 1 [.param 0, scan])) (.chr 'a')
def body : MExp := .seq (.chr '#') (.seq (.star inner) (.seq scan (.chr '#')))
def target : MExp := .seq (.chr '#') (.seq (.andP (.param 0)) (.andP (.param 1)))
def grammar : MGrammar := ⟨[⟨1,body⟩,⟨2,target⟩]⟩
def outer : MExp := .seq (.andP (.call 0 [scan])) (.chr 'a')
def prefixStart : MExp := .seq (.star outer) (.seq (.chr '#') (.seq scan (.chr '#')))
def start : MExp := .seq prefixStart scan

def targets (n : Nat) : List Request :=
  (SequentialProbeTrace.run grammar (input n) 2 start).2.filter (fun r => r.rule == 1)

def request (n m r : Nat) : Request := ⟨1, [(m+r+n+1,r+n+1),(r+n+1,n+1)], n+1⟩

def row (n m t : Nat) : List Request :=
  ((List.range (t+1)).reverse).map (request n m)

def triangle (n : Nat) : List Request :=
  ((List.range (n+1)).reverse).flatMap (fun m => row n m (n-m))

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
    input n = as (n-m) ++ (as m ++ '#' :: (as n ++ '#' :: as n)) := by
  have hr : as (n-m) ++ as m = as n := by simp [as, Nat.sub_add_cancel hm]
  simp only [input, List.append_assoc, List.cons_append]
  rw [← List.append_assoc, hr]

private theorem split_second {n k : Nat} (hk : k ≤ n) :
    input n = (as n ++ '#' :: as (n-k)) ++ (as k ++ '#' :: as n) := by
  have hr : as (n-k) ++ as k = as n := by simp [as, Nat.sub_add_cancel hk]
  simp only [input, List.append_assoc, List.cons_append]
  rw [← List.append_assoc (as (n-k)), hr]

private theorem first_suffix {n m : Nat} (hm : m ≤ n) :
    sfx (input n) (m+2*n+2) = as m ++ '#' :: (as n ++ '#' :: as n) := by
  simpa [as, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.two_mul] using (sfx_suffix (split_first hm))

private theorem second_suffix {n k : Nat} (hk : k ≤ n) :
    sfx (input n) (k+n+1) = as k ++ '#' :: as n := by
  simpa [as,Nat.add_assoc] using (sfx_suffix (split_second hk))

private theorem match_count {n : Nat} (tail : List Char) : ∀ m k,
    SequentialSpanRecompute.matchCount m (as m ++ '#' :: tail) (as k ++ '#' :: as n) =
      if m ≤ k then some (k-m+n+1) else none := by
  intro m
  induction m with
  | zero => intro k; simp [SequentialSpanRecompute.matchCount, as,Nat.add_assoc]
  | succ m ih =>
    intro k
    cases k with
    | zero => simp [as, List.replicate_succ, SequentialSpanRecompute.matchCount, Shallot.beqChar]
    | succ k => simpa [as, List.replicate_succ, SequentialSpanRecompute.matchCount,
        Shallot.beqChar, Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub] using ih k

private theorem param_result {n m k : Nat} (hm : m ≤ n) (hk : k ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 1)
      [(m+2*n+2,2*n+2)] (.param 0) (k+n+1) =
      (some (if m ≤ k then some (k-m+n+1) else none), []) := by
  simp only [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, List.getElem?_cons_zero]
  simp only [SequentialSpanRecompute.matchSpan]
  rw [show m+2*n+2-(2*n+2)=m by omega, first_suffix hm, second_suffix hk, match_count]

private theorem last_suffix (n : Nat) : sfx (input n) n = as n := by
  simpa [as] using (sfx_suffix (x := input n) (y := as n)
    (pre := as n ++ '#' :: as n ++ ['#']) (by simp [input,List.append_assoc]))

private theorem request_words {n m r : Nat} (hmr : m+r≤n) :
    pre (input n) (m+r+n+1) (r+n+1) = as m ∧
    pre (input n) (r+n+1) (n+1) = as r := by
  constructor
  · simp only [pre,second_suffix hmr,show m+r+n+1-(r+n+1)=m by omega]
    simp [as,List.take_append,Nat.min_eq_left (show m≤m+r by omega)]
  · simp [pre,second_suffix (show r≤n by omega),as]

private theorem strip_as {m n : Nat} (hm : m≤n) :
    Shallot.stripPrefix? (as m) (as n) = some (as (n-m)) := by
  apply (CBVtoCBN.stripPrefix_exact _ _ _).mpr
  simp [as,show m+(n-m)=n by omega]

private theorem target_query {n m r : Nat} (hmr : m+r≤n) :
    SequentialProbeTrace.query grammar (input n) 1 1 (request n m r).env (n+1) =
      (some (some n), []) := by
  have hwords := request_words hmr
  have hp0 : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 0) (request n m r).env (.param 0) n =
      (some (some (n-m)),[]) := by
    simp only [SequentialProbeTrace.eval,SequentialSpanRecompute.eval,request,
      List.getElem?_cons_zero]
    rw [SequentialSpanRecompute.matchSpan_eq _ _ _ _ (by simp [input,as]; omega),
      hwords.1,last_suffix,strip_as (show m≤n by omega)]
    simp [as]
  have hp1 : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 0) (request n m r).env (.param 1) n =
      (some (some (n-r)),[]) := by
    simp only [SequentialProbeTrace.eval,SequentialSpanRecompute.eval,request,
      List.getElem?_cons_succ,List.getElem?_cons_zero]
    rw [SequentialSpanRecompute.matchSpan_eq _ _ _ _ (by simp [input,as]; omega),
      hwords.2,last_suffix,strip_as (show r≤n by omega)]
    simp [as]
  have hhead : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 0) (request n m r).env (.chr '#') (n+1) =
      (some (some n),[]) := by
    simp [SequentialProbeTrace.eval,SequentialSpanRecompute.eval,
      show sfx (input n) (n+1)='#'::as n by simpa [as] using (second_suffix (n := n) (k := 0) (by omega)),as,Shallot.beqChar]
  simp only [SequentialProbeTrace.query] at hp0 hp1 hhead
  simp only [SequentialProbeTrace.query,show n+1≤(input n).length by simp [input,as],
    if_true,show ruleAtM grammar.rules 1=some ⟨2,target⟩ by rfl]
  rw [target,SequentialProbeTrace.eval,hhead]
  simp only []
  rw [SequentialProbeTrace.eval,MExp.andP,SequentialProbeTrace.eval,SequentialProbeTrace.eval,hp0]
  simp only []
  rw [MExp.andP,SequentialProbeTrace.eval,SequentialProbeTrace.eval,hp1]
  rfl

private theorem scan_second (n k : Nat) (hk : k ≤ n) (Q : SequentialProbeTrace.Query)
    (E : SequentialSpanRecompute.Env) :
    SequentialProbeTrace.eval grammar (input n) Q E scan (k+n+1) = (some (some (n+1)), []) := by
  simpa [as] using (scan_suffix grammar (input n) Q E k (as n ++ '#' :: as (n-k)) (as n) (split_second hk))

private theorem inner_result {n m k : Nat} (hm : m ≤ n) (hk : k ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 1)
      [(m+2*n+2,2*n+2)] inner (k+n+1) =
      if m ≤ k then
        (if k = 0 then some none else some (some (k+n)), [request n m (k-m)])
      else (some none, []) := by
  have hp := param_result hm hk
  by_cases hmk : m ≤ k
  · have hs := scan_second n (k-m) (by omega)
      (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)]
    have hq := target_query (n := n) (m := m) (r := k-m) (by omega)
    have hargs : SequentialProbeTrace.evalArgs grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)] [.param 0, scan] (k+n+1) =
        (some (some ([(k+n+1,k-m+n+1),(k-m+n+1,n+1)],n+1)), []) := by
      rw [SequentialProbeTrace.evalArgs, hp]
      simp only [if_pos hmk]
      rw [SequentialProbeTrace.evalArgs, hs]
      simp [SequentialProbeTrace.evalArgs, Nat.min_eq_left (show k-m+n+1 ≤ k+n+1 by omega),
        Nat.min_eq_left (show n+1 ≤ k-m+n+1 by omega)]
    have hcall : SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)]
        (.call 1 [.param 0,scan]) (k+n+1) = (some (some n), [request n m (k-m)]) := by
      rw [SequentialProbeTrace.eval]
      simp only [show ruleAtM grammar.rules 1 = some ⟨2,target⟩ by rfl, List.length_cons, List.length_nil, ite_true, hargs]
      simp only [request,show m+(k-m)+n+1=k+n+1 by omega] at hq
      simp [hq,request,show m+(k-m)+n+1=k+n+1 by omega]
    have hand : SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)]
        (.andP (.call 1 [.param 0,scan])) (k+n+1) =
        (some (some (k+n+1)), [request n m (k-m)]) := by
      rw [MExp.andP, SequentialProbeTrace.eval, SequentialProbeTrace.eval, hcall]
    rw [inner, SequentialProbeTrace.eval, hand]
    simp only [if_pos hmk]
    cases k with
    | zero => simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval,
        show sfx (input n) (n+1)='#'::as n by simpa [as] using (second_suffix (n := n) (k := 0) (by omega)), as, Shallot.beqChar]
    | succ k =>
      simp only [SequentialProbeTrace.eval,SequentialSpanRecompute.eval]
      rw [second_suffix hk]
      simp [as,List.replicate_succ,Shallot.beqChar,Nat.add_comm,Nat.add_left_comm]
  · have hargs : SequentialProbeTrace.evalArgs grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)] [.param 0, scan] (k+n+1) =
        (some none, []) := by
      rw [SequentialProbeTrace.evalArgs, hp]
      simp [hmk]
    have hcall : SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)]
        (.call 1 [.param 0,scan]) (k+n+1) = (some none, []) := by
      rw [SequentialProbeTrace.eval]
      simp only [show ruleAtM grammar.rules 1 = some ⟨2,target⟩ by rfl, List.length_cons, List.length_nil, ite_true, hargs]
    rw [inner, SequentialProbeTrace.eval, MExp.andP, SequentialProbeTrace.eval,
      SequentialProbeTrace.eval, hcall]
    simp [hmk]

private theorem row_succ (n m t : Nat) : row n m (t+1) = request n m (t+1) :: row n m t := by
  simp [row, List.range_succ, List.reverse_append]

private theorem inner_star {n m k : Nat} (hm : m ≤ n) (hk : k ≤ n) (hmk : m ≤ k) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 1)
      [(m+2*n+2,2*n+2)] (.star inner) (k+n+1) =
      (some (some ((max m 1)+n)), row n m (k-m)) := by
  induction k with
  | zero =>
    have hm0 : m=0 := by omega
    subst m
    simp only [Nat.zero_add]
    change SequentialProbeTrace.star _ (n+1) = _
    rw [SequentialProbeTrace.star_fail (by simpa using inner_result hm hk)]
    simp [row,Nat.add_comm]
  | succ k ih =>
    have hh := inner_result hm hk
    simp only [if_pos hmk, Nat.succ_ne_zero, if_false] at hh
    change SequentialProbeTrace.star _ (k+1+n+1) = _
    rw [SequentialProbeTrace.star_step hh (by omega)]
    rw [show k+1+n=k+n+1 by omega]
    by_cases hprev : m ≤ k
    · have ht := ih (by omega) hprev
      change ((SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)] (.star inner) (k+n+1)).1,
        [request n m (k+1-m)] ++ (SequentialProbeTrace.eval grammar (input n)
        (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)] (.star inner) (k+n+1)).2) = _
      rw [ht]
      simp only [List.singleton_append]
      rw [show k+1-m=(k-m)+1 by omega, row_succ]
    · have hm' : m=k+1 := by omega
      have hf := inner_result hm (show k≤n by omega)
      simp only [if_neg hprev] at hf
      rw [SequentialProbeTrace.star_fail hf]
      simp [hm', row, Nat.max_eq_left (show 1 ≤ k+1 by omega),Nat.add_assoc,Nat.add_comm]

private theorem body_result {n m : Nat} (hm : m ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 1)
      [(m+2*n+2,2*n+2)] body (2*n+2) = (some (some n), row n m (n-m)) := by
  have hhead : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)] (.chr '#') (2*n+2) =
      (some (some (2*n+1)), []) := by
    have hs := first_suffix (n := n) (m := 0) (by omega)
    simp only [Nat.zero_add] at hs
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, hs, as, Shallot.beqChar] <;> omega
  have hstar := inner_star hm (Nat.le_refl n) hm
  rw [show n+n+1=2*n+1 by omega] at hstar
  have hscan := scan_second n (max m 1 - 1) (by omega)
    (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)]
  rw [show max m 1 - 1 + n + 1 = (max m 1)+n by omega] at hscan
  have hclose : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 1) [(m+2*n+2,2*n+2)] (.chr '#') (n+1) =
      (some (some n), []) := by
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval,
      show sfx (input n) (n+1)='#'::as n by simpa [as] using (second_suffix (n := n) (k := 0) (by omega)), as, Shallot.beqChar]
  rw [body, SequentialProbeTrace.eval, hhead]
  simp only []
  rw [SequentialProbeTrace.eval, hstar]
  simp only []
  rw [SequentialProbeTrace.eval, hscan]
  simp [hclose]

def frameRequest (n m : Nat) : Request := ⟨0, [(m+2*n+2,2*n+2)], 2*n+2⟩

def outerTrace (n m : Nat) : List Request :=
  ((List.range (m+1)).reverse).flatMap (fun j => frameRequest n j :: row n j (n-j))

private theorem outer_result {n m : Nat} (hm : m ≤ n) :
    SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 2)
      [] outer (m+2*n+2) =
      (if m=0 then some none else some (some (m+2*n+1)), frameRequest n m :: row n m (n-m)) := by
  have hscan : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] scan (m+2*n+2) =
      (some (some (2*n+2)), []) := by
    simpa [as, Nat.add_assoc,Nat.two_mul] using (scan_suffix grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] m (as (n-m))
      (as n ++ '#' :: as n) (split_first hm))
  have hb := body_result hm
  have hq : SequentialProbeTrace.query grammar (input n) 2 0 [(m+2*n+2,2*n+2)] (2*n+2) =
      (some (some n), row n m (n-m)) := by
    rw [SequentialProbeTrace.query]
    dsimp only []
    rw [if_pos (show 2*n+2 ≤ (input n).length by simp [input,as]; omega)]
    simpa only [show ruleAtM grammar.rules 0 = some ⟨1,body⟩ by rfl] using hb
  have hargs : SequentialProbeTrace.evalArgs grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] [scan] (m+2*n+2) =
      (some (some ([(m+2*n+2,2*n+2)],2*n+2)), []) := by
    rw [SequentialProbeTrace.evalArgs, hscan]
    simp [SequentialProbeTrace.evalArgs, Nat.min_eq_left (show 2*n+2 ≤ m+2*n+2 by omega)]
  have hcall : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.call 0 [scan]) (m+2*n+2) =
      (some (some n), frameRequest n m :: row n m (n-m)) := by
    rw [SequentialProbeTrace.eval]
    simp only [show ruleAtM grammar.rules 0 = some ⟨1,body⟩ by rfl,
      List.length_cons, List.length_nil, ite_true, hargs]
    simp [hq, frameRequest]
  have hand : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.andP (.call 0 [scan])) (m+2*n+2) =
      (some (some (m+2*n+2)), frameRequest n m :: row n m (n-m)) := by
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
      [] (.star outer) (m+2*n+2) = (some (some (2*n+2)), outerTrace n m) := by
  induction m with
  | zero =>
    have hh := outer_result hm
    simp only [ite_true, Nat.zero_add] at hh
    change SequentialProbeTrace.star _ (0+2*n+2) = _
    simp only [Nat.zero_add]
    rw [SequentialProbeTrace.star_fail hh]
    simp [outerTrace]
  | succ m ih =>
    have hh := outer_result hm
    simp only [Nat.succ_ne_zero, if_false] at hh
    change SequentialProbeTrace.star _ (m+1+2*n+2) = _
    rw [SequentialProbeTrace.star_step hh (by omega)]
    have ht := ih (show m≤n by omega)
    rw [show m+1+2*n+1=m+2*n+2 by omega]
    change ((SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.star outer) (m+2*n+2)).1,
      (frameRequest n (m+1) :: row n (m+1) (n-(m+1))) ++
      (SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.star outer) (m+2*n+2)).2) = _
    rw [ht]
    simp [outerTrace, List.range_succ, List.reverse_append]

theorem prefix_formula (n : Nat) :
    SequentialProbeTrace.run grammar (input n) 2 prefixStart = (some (some n), outerTrace n n) := by
  have hstar := outer_star (Nat.le_refl n)
  have hs := scan_second n n (Nat.le_refl _) (SequentialProbeTrace.query grammar (input n) 2) []
  rw [show n+n+1=2*n+1 by omega] at hs
  have hhead : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.chr '#') (2*n+2) =
      (some (some (2*n+1)), []) := by
    have hx := first_suffix (n := n) (m := 0) (by omega)
    simp only [Nat.zero_add] at hx
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval, hx, as, Shallot.beqChar] <;> omega
  have hclose : SequentialProbeTrace.eval grammar (input n)
      (SequentialProbeTrace.query grammar (input n) 2) [] (.chr '#') (n+1) =
      (some (some n), []) := by
    simp [SequentialProbeTrace.eval, SequentialSpanRecompute.eval,
      show sfx (input n) (n+1)='#'::as n by simpa [as] using (second_suffix (n := n) (k := 0) (by omega)), as, Shallot.beqChar]
  unfold SequentialProbeTrace.run
  rw [show (input n).length = n+2*n+2 by simp [input,as]; omega]
  rw [prefixStart, SequentialProbeTrace.eval, hstar]
  simp only []
  rw [SequentialProbeTrace.eval, hhead]
  simp only []
  rw [SequentialProbeTrace.eval, hs]
  simp [hclose]

private theorem scan_final (g : MGrammar) (x : List Char) (Q : SequentialProbeTrace.Query)
    (E : SequentialSpanRecompute.Env) : ∀ m pre0, x=pre0++as m →
      SequentialProbeTrace.eval g x Q E scan m = (some (some 0),[]) := by
  intro m
  induction m with
  | zero =>
    intro pre0 hx
    change SequentialProbeTrace.star _ 0 = _
    apply SequentialProbeTrace.star_fail
    simp [SequentialProbeTrace.eval,SequentialSpanRecompute.eval,sfx]
  | succ m ih =>
    intro pre0 hx
    have hs : sfx x (m+1) = 'a' :: as m := by
      simpa [as,List.replicate_succ] using (sfx_suffix hx)
    have hh : SequentialProbeTrace.eval g x Q E (.chr 'a') (m+1) =
        (some (some m),[]) := by
      simp [SequentialProbeTrace.eval,SequentialSpanRecompute.eval,hs,as,Shallot.beqChar]
    have hx' : x=(pre0++['a'])++as m := by
      simpa [as,List.replicate_succ,List.append_assoc] using hx
    change SequentialProbeTrace.star _ (m+1) = _
    rw [SequentialProbeTrace.star_step hh (by omega)]
    have ht := ih (pre0++['a']) hx'
    change ((SequentialProbeTrace.eval g x Q E scan m).1,
      []++(SequentialProbeTrace.eval g x Q E scan m).2)=_
    simp [ht]

theorem run_formula (n : Nat) :
    SequentialProbeTrace.run grammar (input n) 2 start = (some (some 0),outerTrace n n) := by
  have hp := prefix_formula n
  change SequentialProbeTrace.eval grammar (input n) (SequentialProbeTrace.query grammar (input n) 2)
    [] prefixStart (input n).length = _ at hp
  have ht := scan_final grammar (input n) (SequentialProbeTrace.query grammar (input n) 2)
    [] n (as n ++ '#' :: as n ++ ['#']) (by simp [input,List.append_assoc])
  unfold SequentialProbeTrace.run
  rw [start,SequentialProbeTrace.eval,hp]
  simp [ht]

theorem targets_eq_triangle (n : Nat) : targets n = triangle n := by
  unfold targets
  rw [run_formula]
  have hf (xs : List Nat) : xs.filter (fun _ => true) = xs :=
    List.filter_eq_self.mpr (by intro a ha; rfl)
  simp [outerTrace, triangle, List.filter_flatMap, List.filter_map, row, frameRequest, request, Function.comp_def, hf]

theorem request_injective {n m r m' r' : Nat} (h : request n m r = request n m' r') :
    m=m' ∧ r=r' := by
  simp only [request, Request.mk.injEq, List.cons.injEq, Prod.mk.injEq] at h
  omega

private theorem row_mem {n m t : Nat} {req : Request} :
    req ∈ row n m t ↔ ∃ r, r≤t ∧ request n m r = req := by
  simp only [row, List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨r, hr, he⟩; exact ⟨r, by omega, he⟩
  · rintro ⟨r, hr, he⟩; exact ⟨r, by omega, he⟩

private theorem row_nodup (n m t : Nat) : (row n m t).Nodup := by
  unfold row
  apply List.Pairwise.map (R := fun a b : Nat => a ≠ b) _
    (fun a b hab he => hab (request_injective he).2)
  exact List.pairwise_reverse.mpr (List.nodup_range.imp (fun h => Ne.symm h))

private theorem blocks_nodup (n : Nat) (ms : List Nat) (hms : ms.Nodup) :
    (ms.flatMap (fun m => row n m (n-m))).Nodup := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    rw [List.nodup_cons] at hms
    simp only [List.flatMap_cons, List.Nodup, List.pairwise_append]
    refine ⟨row_nodup _ _ _, ih hms.2, ?_⟩
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
    req ∈ targets n ↔ ∃ m r, m+r≤n ∧ request n m r = req := by
  rw [targets_eq_triangle]
  simp only [triangle, List.mem_flatMap, List.mem_reverse, List.mem_range, row_mem]
  constructor
  · rintro ⟨m, hm, r, hr, he⟩
    exact ⟨m,r,by omega,he⟩
  · rintro ⟨m,r,hmr,he⟩
    exact ⟨m,by omega,r,by omega,he⟩

theorem input_length (n : Nat) : (input n).length = 3*n+2 := by simp [input,as]; omega

theorem no_linear_cache_bound :
    ∀ C : Nat, ∃ n, C * ((input n).length + 1) < (targets n).length := by
  intro C
  refine ⟨8*C+8, ?_⟩
  have hc := targets_count (8*C+8)
  rw [input_length]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hc ⊢
  have hp := Nat.mul_left_comm C 3 (8*C)
  omega

theorem request_decode {n m r : Nat} (hmr : m+r≤n) :
    SequentialSpanRecompute.decodeEnv (input n) (request n m r).env = [as m,as r] := by
  have hw := request_words hmr
  simp only [request,SequentialSpanRecompute.decodeEnv,List.map_cons,List.map_nil,hw.1,hw.2]

def profiles (n : Nat) (req : Request) : List (Option (List Char)) :=
  (SequentialSpanRecompute.decodeEnv (input n) req.env).map
    (fun w => LiveCaptureQuotient.profile (sfx (input n) req.cursor) (some w))

theorem live_profile {n m : Nat} (hm : m≤n) :
    LiveCaptureQuotient.profile ('#' :: as n) (some (as m)) = some (as m) := by
  have hv : LiveCaptureQuotient.visible ('#' :: as n) (as m) = true := by
    apply (LiveCaptureQuotient.visible_iff ('#' :: as n) (as m)).mpr
    refine ⟨n,by simp [as],?_⟩
    have hs : sfx ('#' :: as n) n = as n := by
      simpa [as] using (sfx_suffix (x := '#' :: as n) (y := as n) (pre := ['#']) rfl)
    rw [hs,strip_as hm]
    rfl
  simp [LiveCaptureQuotient.profile,hv]

theorem request_profiles {n m r : Nat} (hmr : m+r≤n) :
    profiles n (request n m r) = [some (as m),some (as r)] := by
  unfold profiles
  rw [request_decode hmr]
  have hs : sfx (input n) (request n m r).cursor = '#' :: as n := by
    simpa [request,as] using (second_suffix (n := n) (k := 0) (by omega))
  simp [hs,live_profile (show m≤n by omega),live_profile (show r≤n by omega)]

theorem profile_keys_nodup (n : Nat) : ((targets n).map (profiles n)).Nodup := by
  apply List.pairwise_map.mpr
  apply (targets_nodup n).imp_of_mem
  intro a b ha hb hne he
  obtain ⟨m,r,hmr,rfl⟩ := (targets_mem n a).mp ha
  obtain ⟨m',r',hmr',rfl⟩ := (targets_mem n b).mp hb
  rw [request_profiles hmr,request_profiles hmr'] at he
  have hm : m=m' := by
    have h := congrArg List.length (Option.some.inj (List.cons.inj he).1)
    simpa [as] using h
  have hr : r=r' := by
    have h := congrArg List.length (Option.some.inj (List.cons.inj (List.cons.inj he).2).1)
    simpa [as] using h
  subst m'; subst r'
  exact hne rfl

theorem target_reads_both : CaptureReadSupport.reads target = [0,1] := by rfl

theorem no_linear_profile_cache_bound :
    ∀ C : Nat, ∃ n, C*((input n).length+1) < ((targets n).map (profiles n)).length := by
  simpa only [List.length_map] using no_linear_cache_bound

theorem grammar_firstOrder : grammar.FirstOrder := by
  intro r hr
  simp only [grammar,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;>
    simp [body,inner,scan,target,MExp.andP,MExp.FirstOrder,MExp.FirstOrderArgs]

theorem start_firstOrder : start.FirstOrder := by
  simp [start,prefixStart,outer,scan,MExp.andP,MExp.FirstOrder,MExp.FirstOrderArgs]

theorem source_accepts (n : Nat) : SObs grammar .callByValueSeq start (input n) (some []) := by
  have hv : evV grammar (input n) .callByValueSeq (tblV grammar (input n) .callByValueSeq 2)
      [] start (input n).length = some (some 0) := by
    rw [← SequentialProbeTrace.run_correct,run_formula]
  obtain ⟨out,hd,ho⟩ := evV_derives grammar_firstOrder (by decide) start_firstOrder 2 (Nat.le_refl _) hv
  cases out with
  | fail => cases ho
  | ok tree rest =>
    have hr : rest=[] := List.eq_nil_of_length_eq_zero (by simpa [obsR] using ho)
    subst rest
    exact ⟨_,by simpa only [sfx_self] using hd,rfl⟩

end Shallot.MacroPeg.CBV.SequentialLiveProbeTriangle
