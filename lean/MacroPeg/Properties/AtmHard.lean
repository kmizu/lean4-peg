import MacroPeg.Properties.QbfHard
import MacroPeg.Properties.Decide

/-!
# First-order call-by-name Macro PEG simulates linear-space alternating Turing machines

For every alternating Turing machine `M` whose head stays on the input (`n` cells, clamped at the ends) there is a fixed
first-order call-by-name Macro PEG `atmG M` such that, whenever every computation branch of `M` from the initial
configuration on `w` is finite (`M.Halts`), `atmG M` consumes the whole encoding `sitesStr w 0` iff `M` accepts `w`
(`atm_reduction`). The encoding has length `O(n²)` (`sitesStr_length`).

Alternating linear space with halting branches is EXPTIME (APSPACE = EXPTIME, Chandra–Kozen–Stockmeyer 1981; an
APSPACE machine can be made to halt on all branches with a clock in its space; both external facts). With a fixed
machine whose language is EXPTIME-complete, recognition by a fixed first-order call-by-name Macro PEG is EXPTIME-hard;
with `Decide.lean` / `DecideCost.lean` it is EXPTIME-complete.

How the configuration lives in the arguments (call-by-name arguments can be built but never taken apart):

* the input is a list of sites, one per cell: `1^j 0`, then `y` if the input symbol is 1, then `x;`;
* the tape is a parser `A` run at a site: the newest *fact* about the cell decides how far it reads (through the `x`
  for 1, before it for 0). A write prepends a fact (`fact / A`); the ordered choice makes the newest fact win;
* the head is the code test `codeP h`; the state is the rule;
* every rule runs at the start of the input. A cell is inspected with the lookahead rule `FT(K, X)` ("find the site
  of cell `K` and test `X` there"). The rule of a state scans `K = 0, 1, …` with a counter `1^K` until the head is at
  `K`; the counter gives the codes of the neighbours for the head move.
-/

namespace Shallot.MacroPeg

/-! ## Machines -/

inductive Dir where
  | left
  | right
  deriving DecidableEq

inductive Kind where
  | acc
  | rej
  | univ
  | exist
  deriving DecidableEq

/-- An alternating Turing machine over `{0, 1}` with states `0 … states-1`. -/
structure ATM where
  states : Nat
  start : Nat
  kind : Nat → Kind
  delta : Nat → Bool → List (Nat × Bool × Dir)

structure Cfg where
  q : Nat
  h : Nat
  t : List Bool

def moveHead (n : Nat) : Dir → Nat → Nat
  | .left, h => h - 1
  | .right, h => if h + 1 < n then h + 1 else h

def succOf (c : Cfg) (tr : Nat × Bool × Dir) : Cfg :=
  ⟨tr.1, moveHead c.t.length tr.2.2 c.h, c.t.set c.h tr.2.1⟩

def ATM.succs (M : ATM) (c : Cfg) : List Cfg := (M.delta c.q (c.t.getD c.h false)).map (succOf c)

/-- Every branch from `c` is finite. -/
inductive ATM.Halts (M : ATM) : Cfg → Prop
  | mk (c : Cfg) : (∀ c' ∈ M.succs c, M.Halts c') → M.Halts c

mutual
  /-- The acceptance value of a configuration (on finite computation trees). -/
  inductive ATM.Val (M : ATM) : Cfg → Bool → Prop
    | acc (c : Cfg) : M.kind c.q = .acc → M.Val c true
    | rej (c : Cfg) : M.kind c.q = .rej → M.Val c false
    | univ (c : Cfg) (bs : List Bool) : M.kind c.q = .univ → M.ValList (M.succs c) bs → M.Val c (bs.all id)
    | exist (c : Cfg) (bs : List Bool) : M.kind c.q = .exist → M.ValList (M.succs c) bs → M.Val c (bs.any id)

  inductive ATM.ValList (M : ATM) : List Cfg → List Bool → Prop
    | nil : M.ValList [] []
    | cons (c : Cfg) (cs : List Cfg) (b : Bool) (bs : List Bool) : M.Val c b → M.ValList cs bs →
        M.ValList (c :: cs) (b :: bs)
end

def ATM.init (M : ATM) (w : List Bool) : Cfg := ⟨M.start, 0, w⟩

def ATM.Accepts (M : ATM) (w : List Bool) : Prop := M.Val (M.init w) true

/-- Transitions stay among the states. -/
def ATM.WF (M : ATM) : Prop := M.start < M.states ∧ ∀ q b tr, tr ∈ M.delta q b → tr.1 < M.states

theorem ATM.val_functional (M : ATM) {c : Cfg} {b : Bool} (h : M.Val c b) : ∀ b', M.Val c b' → b = b' := by
  induction h using ATM.Val.rec (motive_2 := fun cs bs _ => ∀ bs', M.ValList cs bs' → bs = bs') with
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

/-! ## The grammar -/

def optY : MExp := .alt (.lit ['y']) .eps
def codeE : MExp := .seq (.star one) zero
def siteE : MExp := .seq (.seq codeE optY) (.seq (.lit ['x']) (.lit [';']))
def semi : MExp := .lit [';']

/-- The initial tape: read through the `x` iff the site carries `y` (input symbol 1). -/
def tape0 : MExp := .seq codeE (.alt (.seq (.lit ['y']) (.lit ['x'])) .eps)

/-- The fact "cell `k` holds `b`". -/
def factE (k : MExp) (b : Bool) : MExp := .seq (.seq k zero) (if b then .seq optY (.lit ['x']) else optY)

def ftCall (f : Nat) (a b : MExp) : MExp := .call f [a, b]

/-- `FT(K, X)`: find the site of cell `K` and test `X` there (lookahead tests only). -/
def ftBody (f : Nat) : MExp :=
  .alt (.seq (andP (.seq (.param 0) zero)) (andP (.param 1))) (.seq siteE (.call f [.param 0, .param 1]))

def allChain : List MExp → MExp
  | [] => .eps
  | e :: es => .seq (andP e) (allChain es)

def anyChain : List MExp → MExp
  | [] => .notP .eps
  | e :: es => .alt e (anyChain es)

section Builders

variable (M : ATM)

/-- A branch: write, move, continue in the target state (from the start of the input, scanning from cell 0). -/
def brC (A P K : MExp) (tr : Nat × Bool × Dir) : MExp :=
  match tr.2.2 with
  | .left => .call tr.1 [P, .alt (factE K tr.2.1) A, codeP 0, .eps]
  | .right =>
    .alt (.seq (andP (ftCall M.states (.seq K one) .eps))
        (.call tr.1 [.seq (.seq K one) zero, .alt (factE K tr.2.1) A, codeP 0, .eps]))
      (.seq (.notP (ftCall M.states (.seq K one) .eps)) (.call tr.1 [.seq K zero, .alt (factE K tr.2.1) A, codeP 0, .eps]))

def transC (q : Nat) (b : Bool) (A P K : MExp) : MExp :=
  match M.kind q with
  | .acc => .eps
  | .rej => .notP .eps
  | .univ => allChain ((M.delta q b).map (brC M A P K))
  | .exist => anyChain ((M.delta q b).map (brC M A P K))

def stepC (q : Nat) (A P K : MExp) : MExp :=
  .alt (.seq (andP (ftCall M.states K (.seq A semi))) (transC M q true A P K))
    (.seq (.notP (ftCall M.states K (.seq A semi))) (transC M q false A P K))

def scanC (q : Nat) (H A P K : MExp) : MExp :=
  .alt (.seq (andP (ftCall M.states K H)) (stepC M q A P K))
    (.seq (.notP (ftCall M.states K H))
      (.seq (andP (ftCall M.states (.seq K one) .eps)) (.call q [H, A, .seq K zero, .seq K one])))

end Builders

/-- The rule of state `q` (parameters `H, A, P, K`). -/
def scanBody (M : ATM) (q : Nat) : MExp := scanC M q (.param 0) (.param 1) (.param 2) (.param 3)

def atmG (M : ATM) : MGrammar :=
  ⟨(List.range M.states).map (fun q => ⟨4, scanBody M q⟩) ++ [⟨2, ftBody M.states⟩]⟩

def atmStart (M : ATM) : MExp := .seq (.call M.start [codeP 0, tape0, codeP 0, .eps]) (.star .any)

/-! ## Substitution -/

section Subst

variable (σ : List MExp)

theorem subst_codeP (k : Nat) : MExp.subst σ (codeP k) = codeP k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [codeP, MExp.subst] at ih ⊢
    simp only [cNum, MExp.subst] at ih ⊢
    simp only [MExp.seq.injEq] at ih
    rw [ih.1]; rfl

theorem subst_factE (k : MExp) (b : Bool) : MExp.subst σ (factE k b) = factE (MExp.subst σ k) b := by
  cases b <;> rfl

theorem subst_allChain : ∀ es : List MExp, MExp.subst σ (allChain es) = allChain (es.map (MExp.subst σ))
  | [] => rfl
  | e :: es => by simp only [allChain, MExp.subst, andP, List.map_cons, subst_allChain es]

theorem subst_anyChain : ∀ es : List MExp, MExp.subst σ (anyChain es) = anyChain (es.map (MExp.subst σ))
  | [] => rfl
  | e :: es => by simp only [anyChain, MExp.subst, List.map_cons, subst_anyChain es]

theorem subst_brC (M : ATM) (A P K : MExp) (tr : Nat × Bool × Dir) :
    MExp.subst σ (brC M A P K tr) = brC M (MExp.subst σ A) (MExp.subst σ P) (MExp.subst σ K) tr := by
  obtain ⟨q', b', d⟩ := tr
  cases d <;> simp [brC, MExp.subst, MExp.substArgs, subst_factE, subst_codeP, ftCall, andP, one, zero]

theorem subst_transC (M : ATM) (q : Nat) (b : Bool) (A P K : MExp) :
    MExp.subst σ (transC M q b A P K) = transC M q b (MExp.subst σ A) (MExp.subst σ P) (MExp.subst σ K) := by
  unfold transC
  split
  · rfl
  · rfl
  · rw [subst_allChain, List.map_map]; congr 2; funext tr; exact subst_brC σ M A P K tr
  · rw [subst_anyChain, List.map_map]; congr 2; funext tr; exact subst_brC σ M A P K tr

theorem subst_stepC (M : ATM) (q : Nat) (A P K : MExp) :
    MExp.subst σ (stepC M q A P K) = stepC M q (MExp.subst σ A) (MExp.subst σ P) (MExp.subst σ K) := by
  simp only [stepC, MExp.subst, MExp.substArgs, andP, ftCall, subst_transC]
  rfl

theorem subst_scanC (M : ATM) (q : Nat) (H A P K : MExp) :
    MExp.subst σ (scanC M q H A P K) =
      scanC M q (MExp.subst σ H) (MExp.subst σ A) (MExp.subst σ P) (MExp.subst σ K) := by
  simp only [scanC, MExp.subst, MExp.substArgs, andP, ftCall, subst_stepC]
  rfl

end Subst

theorem subst_scanBody (M : ATM) (q : Nat) (H A P K : MExp) :
    MExp.subst [H, A, P, K] (scanBody M q) = scanC M q H A P K := by
  unfold scanBody; rw [subst_scanC]; rfl

theorem subst_ftBody (f : Nat) (K X : MExp) :
    MExp.subst [K, X] (ftBody f) =
      .alt (.seq (andP (.seq K zero)) (andP X)) (.seq siteE (.call f [K, X])) := rfl

theorem atmG_scan (M : ATM) {q : Nat} (hq : q < M.states) :
    ruleAtM (atmG M).rules q = some ⟨4, scanBody M q⟩ := by
  rw [ruleAtM_eq_getElem?, atmG, List.getElem?_append_left (by simpa using hq), List.getElem?_map,
    List.getElem?_range hq]
  rfl

theorem atmG_ft (M : ATM) : ruleAtM (atmG M).rules M.states = some ⟨2, ftBody M.states⟩ := by
  rw [ruleAtM_eq_getElem?, atmG, List.getElem?_append_right (by simp)]
  simp

/-! ## The input -/

def siteStr (j : Nat) (b : Bool) : List Char := codeStr j ++ (if b then ['y'] else []) ++ ['x', ';']

/-- The sites of cells `j, j+1, …` holding the input symbols `w`, then `#`. -/
def sitesStr : List Bool → Nat → List Char
  | [], _ => ['#']
  | b :: w, j => siteStr j b ++ sitesStr w (j + 1)

theorem sitesStr_length : ∀ (w : List Bool) (j : Nat),
    (sitesStr w j).length ≤ w.length * (j + w.length + 4) + 1
  | [], _ => by simp [sitesStr]
  | b :: w, j => by
    have ih := sitesStr_length w (j + 1)
    simp only [sitesStr, siteStr, codeStr, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    have hb : (if b = true then ['y'] else ([] : List Char)).length ≤ 1 := by split <;> simp
    have : w.length * (j + 1 + w.length + 4) ≤ w.length * (j + (w.length + 1) + 4) := by
      apply Nat.mul_le_mul_left; omega
    rw [Nat.succ_mul]
    omega

/-! ## Basic parsers on sites (any grammar) -/

section Basic

variable {g : MGrammar}

theorem codeE_ok (j : Nat) (rest : List Char) : MacroObs g codeE (codeStr j ++ rest) (some rest) := by
  unfold codeStr codeE
  rw [List.append_assoc, List.singleton_append]
  exact obs_seq (star_one rest j) (obs_lit_ok (g := g) ['0'] rest)

theorem siteE_ok (j : Nat) (b : Bool) (rest : List Char) : MacroObs g siteE (siteStr j b ++ rest) (some rest) := by
  unfold siteStr siteE
  cases b with
  | true =>
    simp only [if_pos, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
    refine obs_seq (obs_seq (codeE_ok j _) (obs_alt_some (obs_lit_ok (g := g) ['y'] _))) ?_
    exact obs_seq (obs_lit_ok (g := g) ['x'] _) (obs_lit_ok (g := g) [';'] rest)
  | false =>
    simp only [List.append_assoc, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte]
    refine obs_seq (obs_seq (codeE_ok j _) (obs_alt_none (obs_char_fail _ (by decide)) (obs_eps _))) ?_
    exact obs_seq (obs_lit_ok (g := g) ['x'] _) (obs_lit_ok (g := g) [';'] rest)

/-- What a tape parser leaves after reading a site: `;…` for 1, `x;…` for 0. -/
def tapeRest (t : Bool) (rest : List Char) : List Char := if t then ';' :: rest else 'x' :: ';' :: rest

/-- `A` represents the tape `t` on the sites of the input `w`. -/
def Rep (g : MGrammar) (A : MExp) (t w : List Bool) : Prop :=
  ∀ j, j < w.length → ∀ rest, MacroObs g A (siteStr j (w.getD j false) ++ rest) (some (tapeRest (t.getD j false) rest))

theorem tape0_rep (w : List Bool) : Rep g tape0 w w := by
  intro j _ rest
  unfold siteStr tape0 tapeRest
  cases w.getD j false with
  | true =>
    simp only [if_pos, List.append_assoc, List.cons_append, List.nil_append]
    exact obs_seq (codeE_ok j _) (obs_alt_some (obs_seq (obs_lit_ok (g := g) ['y'] _) (obs_lit_ok (g := g) ['x'] _)))
  | false =>
    simp only [List.append_assoc, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte]
    exact obs_seq (codeE_ok j _) (obs_alt_none (obs_seq_none (obs_char_fail _ (by decide))) (obs_eps _))

theorem getD_set_eq (t : List Bool) {k : Nat} (hk : k < t.length) (b : Bool) : (t.set k b).getD k false = b := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, hk]

theorem getD_set_ne (t : List Bool) {k j : Nat} (h : k ≠ j) (b : Bool) : (t.set k b).getD j false = t.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem fact_rep {A : MExp} {t w : List Bool} (hA : Rep g A t w) {k : Nat} (hk : k < t.length) (b : Bool) :
    Rep g (.alt (factE (cNum k) b) A) (t.set k b) w := by
  intro j hj rest
  have hc := codeP_match (g := g) k j ((if w.getD j false then ['y'] else []) ++ ['x', ';'] ++ rest)
  unfold siteStr
  rw [List.append_assoc, List.append_assoc] at *
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl] at hc
    rw [getD_set_eq t hk b]
    refine obs_alt_some (obs_seq hc ?_)
    unfold tapeRest
    cases b <;> cases w.getD j false <;>
      simp only [if_pos, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append]
    · exact obs_alt_none (obs_char_fail _ (by decide)) (obs_eps _)
    · exact obs_alt_some (obs_lit_ok (g := g) ['y'] _)
    · exact obs_seq (obs_alt_none (obs_char_fail _ (by decide)) (obs_eps _)) (obs_lit_ok (g := g) ['x'] _)
    · exact obs_seq (obs_alt_some (obs_lit_ok (g := g) ['y'] _)) (obs_lit_ok (g := g) ['x'] _)
  · rw [if_neg hjk] at hc
    rw [getD_set_ne t (Ne.symm hjk) b]
    have := hA j hj rest
    unfold siteStr at this
    rw [List.append_assoc, List.append_assoc] at this
    exact obs_alt_none (obs_seq_none hc) this

end Basic

/-! ## Finding a cell -/

section Find

variable {g : MGrammar}

theorem cNum_hash : ∀ (k : Nat) (rest : List Char),
    MacroObs g (cNum k) ('#' :: rest) (if k = 0 then some ('#' :: rest) else none)
  | 0, rest => obs_eps _
  | k + 1, rest => by
    have ih := cNum_hash k rest
    rw [if_neg (by omega)]
    by_cases hk : k = 0
    · rw [if_pos hk] at ih; exact obs_seq ih (obs_char_fail _ (by decide))
    · rw [if_neg hk] at ih; exact obs_seq_none ih

theorem codeP_hash (k : Nat) (rest : List Char) : MacroObs g (codeP k) ('#' :: rest) none := by
  have h := cNum_hash (g := g) k rest
  by_cases hk : k = 0
  · rw [if_pos hk] at h; exact obs_seq h (obs_char_fail _ (by decide))
  · rw [if_neg hk] at h; exact obs_seq_none h

theorem siteE_hash (rest : List Char) : MacroObs g siteE ('#' :: rest) none := by
  refine obs_seq_none (obs_seq_none ?_)
  exact obs_seq (obs_star_none (obs_char_fail _ (by decide))) (obs_char_fail _ (by decide))

/-- The site of cell `K` in the sites from `i`. -/
theorem sitesStr_split (b : Bool) (v : List Bool) (i : Nat) :
    sitesStr (b :: v) i = siteStr i b ++ sitesStr v (i + 1) := rfl

theorem ft_hit {f : Nat} (hf : ruleAtM g.rules f = some ⟨2, ftBody f⟩) (K : Nat) (X : MExp) :
    ∀ (v : List Bool) (i : Nat), i ≤ K → K - i < v.length → ∀ y,
      MacroObs g X (sitesStr (v.drop (K - i)) K) (some y) →
      MacroObs g (ftCall f (cNum K) X) (sitesStr v i) (some (sitesStr (v.drop (K - i)) K))
  | [], _, _, h, _, _ => by simp at h
  | b :: v, i, hi, hlt, y, hX => by
    refine obs_call hf rfl ?_
    rw [subst_ftBody, sitesStr_split]
    have hc := codeP_match (g := g) K i ((if b then ['y'] else []) ++ ['x', ';'] ++ sitesStr v (i + 1))
    by_cases hiK : i = K
    · subst hiK
      rw [if_pos rfl] at hc
      simp only [Nat.sub_self, List.drop_zero, sitesStr_split] at hX ⊢
      have hc' : MacroObs g (codeP i) (siteStr i b ++ sitesStr v (i + 1))
          (some ((if b then ['y'] else []) ++ ['x', ';'] ++ sitesStr v (i + 1))) := by
        unfold siteStr; simpa [List.append_assoc] using hc
      exact obs_alt_some (obs_seq (obs_and_some hc') (obs_and_some hX))
    · rw [if_neg hiK] at hc
      have hc' : MacroObs g (codeP K) (siteStr i b ++ sitesStr v (i + 1)) none := by
        unfold siteStr; simpa [List.append_assoc] using hc
      have hd : K - i = (K - (i + 1)) + 1 := by omega
      rw [hd, List.drop_succ_cons] at hX ⊢
      refine obs_alt_none (obs_seq_none (obs_and_none hc')) (obs_seq (siteE_ok i b _) ?_)
      exact ft_hit hf K X v (i + 1) (by omega) (by simp at hlt; omega) y hX

theorem ft_miss {f : Nat} (hf : ruleAtM g.rules f = some ⟨2, ftBody f⟩) (K : Nat) (X : MExp) :
    ∀ (v : List Bool) (i : Nat), (i ≤ K → K - i < v.length → MacroObs g X (sitesStr (v.drop (K - i)) K) none) →
      MacroObs g (ftCall f (cNum K) X) (sitesStr v i) none
  | [], i, _ => by
    refine obs_call hf rfl ?_
    rw [subst_ftBody]
    exact obs_alt_none (obs_seq_none (obs_and_none (codeP_hash K []))) (obs_seq_none (siteE_hash []))
  | b :: v, i, hX => by
    refine obs_call hf rfl ?_
    rw [subst_ftBody, sitesStr_split]
    have hc := codeP_match (g := g) K i ((if b then ['y'] else []) ++ ['x', ';'] ++ sitesStr v (i + 1))
    have hrec : MacroObs g (ftCall f (cNum K) X) (sitesStr v (i + 1)) none := by
      refine ft_miss hf K X v (i + 1) (fun h₁ h₂ => ?_)
      have := hX (by omega) (by simp; omega)
      rwa [show K - i = (K - (i + 1)) + 1 by omega, List.drop_succ_cons] at this
    by_cases hiK : i = K
    · subst hiK
      rw [if_pos rfl] at hc
      have hc' : MacroObs g (codeP i) (siteStr i b ++ sitesStr v (i + 1))
          (some ((if b then ['y'] else []) ++ ['x', ';'] ++ sitesStr v (i + 1))) := by
        unfold siteStr; simpa [List.append_assoc] using hc
      have hX' := hX (Nat.le_refl _) (by simp)
      simp only [Nat.sub_self, List.drop_zero, sitesStr_split] at hX'
      exact obs_alt_none (obs_seq (obs_and_some hc') (obs_and_none hX')) (obs_seq (siteE_ok i b _) hrec)
    · rw [if_neg hiK] at hc
      have hc' : MacroObs g (codeP K) (siteStr i b ++ sitesStr v (i + 1)) none := by
        unfold siteStr; simpa [List.append_assoc] using hc
      exact obs_alt_none (obs_seq_none (obs_and_none hc')) (obs_seq (siteE_ok i b _) hrec)

end Find

/-! ## Guards, tests and the scan -/

section Sim

variable {g : MGrammar}

theorem guard_pos {C X Y : MExp} {x y : List Char} {r : Option (List Char)} (hC : MacroObs g C x (some y))
    (hX : MacroObs g X x r) : MacroObs g (.alt (.seq (andP C) X) (.seq (.notP C) Y)) x r := by
  cases r with
  | none => exact obs_alt_none (obs_seq (obs_and_some hC) hX) (obs_seq_none (obs_not_some hC))
  | some z => exact obs_alt_some (obs_seq (obs_and_some hC) hX)

theorem guard_neg {C X Y : MExp} {x : List Char} {r : Option (List Char)} (hC : MacroObs g C x none)
    (hY : MacroObs g Y x r) : MacroObs g (.alt (.seq (andP C) X) (.seq (.notP C) Y)) x r :=
  obs_alt_none (obs_seq_none (obs_and_none hC)) (obs_seq (obs_not_none hC) hY)

theorem star_any_all : ∀ x : List Char, MacroObs g (.star .any) x (some [])
  | [] => obs_star_none obs_any_nil
  | c :: x => obs_star_some (obs_any_some c x) (star_any_all x)

theorem sitesStr_drop {w : List Bool} {K : Nat} (hK : K < w.length) :
    sitesStr (w.drop K) K = siteStr K (w.getD K false) ++ sitesStr (w.drop (K + 1)) (K + 1) := by
  rw [List.drop_eq_getElem_cons hK, sitesStr_split]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hK]

end Sim

section Machine

variable (M : ATM) (w : List Bool)

local notation "G" => atmG M
local notation "L" => sitesStr w 0

def res (b : Bool) : Option (List Char) := if b then some (sitesStr w 0) else none

theorem ft_at {K : Nat} {X : MExp} (hK : K < w.length) {y : List Char}
    (hX : MacroObs G X (sitesStr (w.drop K) K) (some y)) :
    MacroObs G (ftCall M.states (cNum K) X) L (some (sitesStr (w.drop K) K)) := by
  have := ft_hit (atmG_ft M) K X w 0 (Nat.zero_le _) (by simpa using hK) y (by simpa using hX)
  simpa using this

theorem ft_not {K : Nat} {X : MExp} (hX : K < w.length → MacroObs G X (sitesStr (w.drop K) K) none) :
    MacroObs G (ftCall M.states (cNum K) X) L none :=
  ft_miss (atmG_ft M) K X w 0 (fun _ h => by simpa using hX (by simpa using h))

theorem head_hit {K : Nat} (hK : K < w.length) :
    MacroObs G (ftCall M.states (cNum K) (codeP K)) L (some (sitesStr (w.drop K) K)) := by
  refine ft_at M w hK (y := (if w.getD K false then ['y'] else []) ++ ['x', ';'] ++ sitesStr (w.drop (K + 1)) (K + 1)) ?_
  rw [sitesStr_drop hK]
  have := codeP_match (g := G) K K ((if w.getD K false then ['y'] else []) ++ ['x', ';'] ++
    sitesStr (w.drop (K + 1)) (K + 1))
  rw [if_pos rfl] at this
  unfold siteStr; simpa [List.append_assoc] using this

theorem head_miss {K h : Nat} (hne : K ≠ h) : MacroObs G (ftCall M.states (cNum K) (codeP h)) L none := by
  refine ft_not M w (fun hK => ?_)
  rw [sitesStr_drop hK]
  have := codeP_match (g := G) h K ((if w.getD K false then ['y'] else []) ++ ['x', ';'] ++
    sitesStr (w.drop (K + 1)) (K + 1))
  rw [if_neg hne] at this
  unfold siteStr; simpa [List.append_assoc] using this

theorem exists_hit {K : Nat} (hK : K < w.length) :
    MacroObs G (ftCall M.states (cNum K) .eps) L (some (sitesStr (w.drop K) K)) :=
  ft_at M w hK (obs_eps _)

theorem exists_miss {K : Nat} (hK : w.length ≤ K) : MacroObs G (ftCall M.states (cNum K) .eps) L none :=
  ft_not M w (fun h => absurd h (by omega))

theorem sym_test {A : MExp} {t : List Bool} (hA : Rep G A t w) {K : Nat} (hK : K < w.length) :
    MacroObs G (ftCall M.states (cNum K) (.seq A semi)) L
      (if t.getD K false then some (sitesStr (w.drop K) K) else none) := by
  have hrep := hA K hK (sitesStr (w.drop (K + 1)) (K + 1))
  rw [← sitesStr_drop hK] at hrep
  unfold tapeRest at hrep
  split
  · rename_i ht
    rw [if_pos ht] at hrep
    exact ft_at M w hK (obs_seq hrep (obs_lit_ok (g := G) [';'] _))
  · rename_i ht
    rw [if_neg ht] at hrep
    exact ft_not M w (fun _ => obs_seq hrep (obs_char_fail _ (by decide)))

/-- The scan of the state's rule reaches the head and runs the step there. -/
theorem scan_ok {q h : Nat} (hq : q < M.states) (hh : h < w.length) {A : MExp} {r : Option (List Char)}
    (hstep : MacroObs G (stepC M q A (codeP (h - 1)) (cNum h)) L r) :
    ∀ d K, K + d = h → MacroObs G (.call q [codeP h, A, codeP (K - 1), cNum K]) L r := by
  intro d
  induction d with
  | zero =>
    intro K hK
    simp only [Nat.add_zero] at hK
    subst hK
    refine obs_call (atmG_scan M hq) rfl ?_
    rw [subst_scanBody]
    exact guard_pos (head_hit M w hh) hstep
  | succ d ih =>
    intro K hK
    refine obs_call (atmG_scan M hq) rfl ?_
    rw [subst_scanBody]
    refine guard_neg (head_miss M w (by omega)) ?_
    have hnext := ih (K + 1) (by omega)
    rw [show K + 1 - 1 = K by omega] at hnext
    exact obs_seq (obs_and_some (exists_hit M w (K := K + 1) (by omega))) hnext

/-- One branch: the successor configuration's rule, called with the new head and the extended tape. -/
theorem br_ok {c : Cfg} (hh : c.h < w.length) (ht : c.t.length = w.length) {A : MExp} (hA : Rep G A c.t w)
    (tr : Nat × Bool × Dir) {b : Bool}
    (hIH : ∀ A', Rep G A' (succOf c tr).t w →
      MacroObs G (.call (succOf c tr).q [codeP (succOf c tr).h, A', codeP 0, .eps]) L (res w b)) :
    MacroObs G (brC M A (codeP (c.h - 1)) (cNum c.h) tr) L (res w b) := by
  obtain ⟨q', b', d⟩ := tr
  have hrep : Rep G (.alt (factE (cNum c.h) b') A) (c.t.set c.h b') w := fact_rep hA (by omega) b'
  cases d with
  | left => exact hIH _ hrep
  | right =>
    have hIH' := hIH _ hrep
    simp only [succOf, moveHead, ht] at hIH'
    by_cases hn : c.h + 1 < w.length
    · rw [if_pos hn] at hIH'
      exact guard_pos (exists_hit M w (K := c.h + 1) hn) hIH'
    · rw [if_neg hn] at hIH'
      exact guard_neg (exists_miss M w (K := c.h + 1) (by omega)) hIH'

theorem chain_all {c : Cfg} (hh : c.h < w.length) (ht : c.t.length = w.length) {A : MExp} (hA : Rep G A c.t w) :
    ∀ trs : List (Nat × Bool × Dir), (∀ tr ∈ trs, ∃ b, M.Val (succOf c tr) b ∧ ∀ A', Rep G A' (succOf c tr).t w →
        MacroObs G (.call (succOf c tr).q [codeP (succOf c tr).h, A', codeP 0, .eps]) L (res w b)) →
      ∃ bs, M.ValList (trs.map (succOf c)) bs ∧
        MacroObs G (allChain (trs.map (brC M A (codeP (c.h - 1)) (cNum c.h)))) L (res w (bs.all id))
  | [], _ => ⟨[], .nil, obs_eps _⟩
  | tr :: trs, H => by
    obtain ⟨b, hv, hobs⟩ := H tr List.mem_cons_self
    obtain ⟨bs, hvs, hrest⟩ := chain_all hh ht hA trs (fun t ht' => H t (List.mem_cons_of_mem _ ht'))
    refine ⟨b :: bs, .cons _ _ _ _ hv hvs, ?_⟩
    have hbr := br_ok M w hh ht hA tr hobs
    simp only [List.map_cons, allChain]
    cases b with
    | true => exact obs_seq (obs_and_some hbr) (by simpa [res] using hrest)
    | false => exact obs_seq_none (obs_and_none hbr)

theorem chain_any {c : Cfg} (hh : c.h < w.length) (ht : c.t.length = w.length) {A : MExp} (hA : Rep G A c.t w) :
    ∀ trs : List (Nat × Bool × Dir), (∀ tr ∈ trs, ∃ b, M.Val (succOf c tr) b ∧ ∀ A', Rep G A' (succOf c tr).t w →
        MacroObs G (.call (succOf c tr).q [codeP (succOf c tr).h, A', codeP 0, .eps]) L (res w b)) →
      ∃ bs, M.ValList (trs.map (succOf c)) bs ∧
        MacroObs G (anyChain (trs.map (brC M A (codeP (c.h - 1)) (cNum c.h)))) L (res w (bs.any id))
  | [], _ => ⟨[], .nil, obs_not_some (obs_eps _)⟩
  | tr :: trs, H => by
    obtain ⟨b, hv, hobs⟩ := H tr List.mem_cons_self
    obtain ⟨bs, hvs, hrest⟩ := chain_any hh ht hA trs (fun t ht' => H t (List.mem_cons_of_mem _ ht'))
    refine ⟨b :: bs, .cons _ _ _ _ hv hvs, ?_⟩
    have hbr := br_ok M w hh ht hA tr hobs
    simp only [List.map_cons, anyChain]
    cases b with
    | true => exact obs_alt_some (by simpa [res] using hbr)
    | false => exact obs_alt_none (by simpa [res] using hbr) (by simpa [res] using hrest)

end Machine

/-! ## The simulation -/

theorem ATM.valList_functional (M : ATM) : ∀ {cs : List Cfg} {bs bs' : List Bool},
    M.ValList cs bs → M.ValList cs bs' → bs = bs'
  | _, _, _, .nil, h => by cases h; rfl
  | _, _, _, .cons _ _ _ _ h₁ h₂, h' => by
    cases h' with
    | cons _ _ b' bs'' h₁' h₂' => rw [M.val_functional h₁ b' h₁', M.valList_functional h₂ h₂']

theorem ATM.vals_exist (M : ATM) (c : Cfg) : ∀ trs : List (Nat × Bool × Dir),
    (∀ tr ∈ trs, ∃ b, M.Val (succOf c tr) b) → ∃ bs, M.ValList (trs.map (succOf c)) bs
  | [], _ => ⟨[], .nil⟩
  | tr :: trs, H => by
    obtain ⟨b, hb⟩ := H tr List.mem_cons_self
    obtain ⟨bs, hbs⟩ := M.vals_exist c trs (fun t ht => H t (List.mem_cons_of_mem _ ht))
    exact ⟨b :: bs, .cons _ _ _ _ hb hbs⟩

section Main

variable (M : ATM) (w : List Bool)

local notation "G" => atmG M
local notation "L" => sitesStr w 0

theorem step_ok {c : Cfg} (hh : c.h < w.length) {A : MExp} (hA : Rep G A c.t w) {r : Option (List Char)}
    (htr : MacroObs G (transC M c.q (c.t.getD c.h false) A (codeP (c.h - 1)) (cNum c.h)) L r) :
    MacroObs G (stepC M c.q A (codeP (c.h - 1)) (cNum c.h)) L r := by
  have hs := sym_test M w hA hh
  unfold stepC
  cases htb : c.t.getD c.h false with
  | true => rw [htb] at hs htr; exact guard_pos hs htr
  | false => rw [htb] at hs htr; exact guard_neg hs htr

/-- **The simulation.** For a configuration all of whose branches are finite, the rule of its state, called with its
head and any parser representing its tape, succeeds without consuming input iff the configuration accepts. -/
theorem atm_sim (hM : M.WF) : ∀ c, M.Halts c → c.q < M.states → c.h < w.length → c.t.length = w.length →
    ∃ b, M.Val c b ∧ ∀ A, Rep G A c.t w → MacroObs G (.call c.q [codeP c.h, A, codeP 0, .eps]) L (res w b) := by
  intro c hc
  induction hc with
  | mk c _ ih =>
    intro hq hh ht
    have H : ∀ tr ∈ M.delta c.q (c.t.getD c.h false), ∃ b, M.Val (succOf c tr) b ∧ ∀ A', Rep G A' (succOf c tr).t w →
        MacroObs G (.call (succOf c tr).q [codeP (succOf c tr).h, A', codeP 0, .eps]) L (res w b) := by
      intro tr htr
      have hmem : succOf c tr ∈ M.succs c := List.mem_map_of_mem htr
      refine ih _ hmem (hM.2 _ _ tr htr) ?_ (by simp [succOf, ht])
      obtain ⟨q', b', d⟩ := tr
      cases d <;> simp only [succOf, moveHead, ht] <;> (try split) <;> omega
    have hvals := M.vals_exist c _ (fun tr htr => (H tr htr).imp fun _ h => h.1)
    have hscan : ∀ {A : MExp} {r : Option (List Char)}, Rep G A c.t w →
        MacroObs G (transC M c.q (c.t.getD c.h false) A (codeP (c.h - 1)) (cNum c.h)) L r →
        MacroObs G (.call c.q [codeP c.h, A, codeP 0, .eps]) L r := by
      intro A r hA htr
      exact scan_ok M w hq hh (step_ok M w hh hA htr) c.h 0 (by omega)
    cases hk : M.kind c.q with
    | acc =>
      refine ⟨true, .acc c hk, fun A hA => hscan hA ?_⟩
      simp only [transC, hk, res, if_pos]
      exact obs_eps _
    | rej =>
      refine ⟨false, .rej c hk, fun A hA => hscan hA ?_⟩
      simp only [transC, hk, res, Bool.false_eq_true, ↓reduceIte]
      exact obs_not_some (obs_eps _)
    | univ =>
      obtain ⟨bs, hbs⟩ := hvals
      refine ⟨bs.all id, .univ c bs hk hbs, fun A hA => hscan hA ?_⟩
      obtain ⟨bs', hbs', hobs⟩ := chain_all M w hh ht hA _ H
      rw [M.valList_functional hbs' hbs] at hobs
      simp only [transC, hk]
      exact hobs
    | exist =>
      obtain ⟨bs, hbs⟩ := hvals
      refine ⟨bs.any id, .exist c bs hk hbs, fun A hA => hscan hA ?_⟩
      obtain ⟨bs', hbs', hobs⟩ := chain_any M w hh ht hA _ H
      rw [M.valList_functional hbs' hbs] at hobs
      simp only [transC, hk]
      exact hobs

/-- **The reduction.** If every branch of `M` on `w` is finite, `atmG M` consumes the whole encoding of `w` iff `M`
accepts `w`. -/
theorem atm_reduction (hM : M.WF) (hw : w ≠ []) (hh : M.Halts (M.init w)) :
    MRecognizesAll G (atmStart M) L ↔ M.Accepts w := by
  have hlen : 0 < w.length := List.length_pos_iff.2 hw
  obtain ⟨b, hv, hobs⟩ := atm_sim M w hM (M.init w) hh hM.1 hlen rfl
  have hcall := hobs tape0 (tape0_rep w)
  cases b with
  | true =>
    simp only [res, if_pos] at hcall
    exact ⟨fun _ => hv, fun _ => obs_seq hcall (star_any_all _)⟩
  | false =>
    simp only [res, Bool.false_eq_true, ↓reduceIte] at hcall
    have hstart : MacroObs G (atmStart M) L none := obs_seq_none hcall
    constructor
    · intro h; have := macroObs_unique h hstart; cases this
    · intro h; have := M.val_functional hv true h; cases this

end Main

/-! ## Example: accept iff the first cell holds 1 -/

def firstBitM : ATM where
  states := 2
  start := 0
  kind := fun q => if q = 0 then .exist else .acc
  delta := fun q b => if q = 0 ∧ b = true then [(1, true, .right)] else []

theorem firstBitM_wf : firstBitM.WF := by
  refine ⟨by decide, fun q b tr htr => ?_⟩
  simp only [firstBitM] at htr
  split at htr
  · simp at htr; rw [htr]; decide
  · simp at htr

theorem firstBitM_halts (b : Bool) : firstBitM.Halts (firstBitM.init [b]) := by
  refine .mk _ (fun c hc => ?_)
  cases b with
  | false => simp [ATM.succs, firstBitM, ATM.init] at hc
  | true =>
    simp [ATM.succs, firstBitM, ATM.init, succOf, moveHead] at hc
    subst hc
    exact .mk _ (fun c' hc' => by simp [ATM.succs, firstBitM] at hc')

example : MRecognizesAll (atmG firstBitM) (atmStart firstBitM) (sitesStr [true] 0) := by
  refine (atm_reduction firstBitM [true] firstBitM_wf (by simp) (firstBitM_halts true)).2 ?_
  exact .exist _ [true] rfl (.cons _ _ _ _ (.acc _ rfl) .nil)

example : ¬ MRecognizesAll (atmG firstBitM) (atmStart firstBitM) (sitesStr [false] 0) := by
  rw [atm_reduction firstBitM [false] firstBitM_wf (by simp) (firstBitM_halts false)]
  intro h
  have := firstBitM.val_functional h false (.exist _ [] rfl .nil)
  cases this

/-! ## The grammar is first-order: EXPTIME-completeness -/

theorem allChain_fo : ∀ es : List MExp, (∀ e ∈ es, e.FirstOrder) → (allChain es).FirstOrder
  | [], _ => trivial
  | e :: es, h => ⟨h e List.mem_cons_self, allChain_fo es (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem anyChain_fo : ∀ es : List MExp, (∀ e ∈ es, e.FirstOrder) → (anyChain es).FirstOrder
  | [], _ => trivial
  | e :: es, h => ⟨h e List.mem_cons_self, anyChain_fo es (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem codeP_fo (k : Nat) : (codeP k).FirstOrder := by
  induction k with
  | zero => exact ⟨trivial, trivial⟩
  | succ k ih => exact ⟨⟨ih.1, trivial⟩, trivial⟩

theorem brC_fo (M : ATM) {A P K : MExp} (hA : A.FirstOrder) (hP : P.FirstOrder) (hK : K.FirstOrder)
    (tr : Nat × Bool × Dir) : (brC M A P K tr).FirstOrder := by
  obtain ⟨q', b', d⟩ := tr
  have hf : (factE K b').FirstOrder := by cases b' <;> exact ⟨⟨hK, trivial⟩, by simp [MExp.FirstOrder, optY]⟩
  cases d with
  | left => exact ⟨hP, ⟨hf, hA⟩, codeP_fo 0, trivial, trivial⟩
  | right =>
    refine ⟨⟨⟨⟨hK, trivial⟩, trivial, trivial⟩, ⟨⟨hK, trivial⟩, trivial⟩, ⟨hf, hA⟩, codeP_fo 0, trivial, trivial⟩,
      ⟨⟨⟨hK, trivial⟩, trivial, trivial⟩, ⟨hK, trivial⟩, ⟨hf, hA⟩, codeP_fo 0, trivial, trivial⟩⟩

theorem transC_fo (M : ATM) (q : Nat) (b : Bool) {A P K : MExp} (hA : A.FirstOrder) (hP : P.FirstOrder)
    (hK : K.FirstOrder) : (transC M q b A P K).FirstOrder := by
  unfold transC
  split
  · trivial
  · trivial
  · exact allChain_fo _ (fun e he => by
      obtain ⟨tr, _, rfl⟩ := List.mem_map.1 he; exact brC_fo M hA hP hK tr)
  · exact anyChain_fo _ (fun e he => by
      obtain ⟨tr, _, rfl⟩ := List.mem_map.1 he; exact brC_fo M hA hP hK tr)

theorem atmG_firstOrder (M : ATM) : (atmG M).FirstOrder := by
  intro r hr
  simp only [atmG, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
  rcases hr with ⟨q, _, rfl⟩ | rfl
  · have hp : ∀ i, (MExp.param i).FirstOrder := fun _ => trivial
    have hstep := transC_fo M q true (hp 1) (hp 2) (hp 3)
    have hstep' := transC_fo M q false (hp 1) (hp 2) (hp 3)
    exact ⟨⟨⟨trivial, trivial, trivial⟩, ⟨⟨⟨trivial, ⟨trivial, trivial⟩, trivial⟩, hstep⟩,
      ⟨⟨trivial, ⟨trivial, trivial⟩, trivial⟩, hstep'⟩⟩⟩,
      ⟨⟨trivial, trivial, trivial⟩, ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩,
        ⟨trivial, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩⟩⟩⟩
  · exact ⟨⟨⟨trivial, trivial⟩, trivial⟩, ⟨⟨⟨trivial, trivial⟩, by simp [MExp.FirstOrder, optY]⟩, trivial, trivial⟩,
      trivial, trivial, trivial⟩

theorem atmStart_firstOrder (M : ATM) : (atmStart M).FirstOrder :=
  ⟨⟨codeP_fo 0, ⟨⟨trivial, trivial⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩, codeP_fo 0, trivial, trivial⟩, trivial⟩

theorem atmStart_closed (M : ATM) : MExp.subst [] (atmStart M) = atmStart M := by
  simp [atmStart, MExp.subst, MExp.substArgs, subst_codeP, tape0, codeE, one, zero]

/-- **EXPTIME-completeness, assembled.** The simulating grammar is first-order, so the exponential-time decision
procedure of `Decide.lean` applies to it and decides acceptance of the machine. -/
theorem atm_by_decision (M : ATM) (w : List Bool) (hM : M.WF) (hw : w ≠ []) (hh : M.Halts (M.init w)) :
    decideObs (atmG M) (sitesStr w 0) (atmStart M) = some (some []) ↔ M.Accepts w :=
  (decideObs_iff (atmG_firstOrder M) (atmStart_firstOrder M) (atmStart_closed M) _ _).trans
    (atm_reduction M w hM hw hh)

end Shallot.MacroPeg
