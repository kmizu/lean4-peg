import PalPeg.GalilArriveChain
import PalPeg.GalilCheckpoints
import PalPeg.GalilLedgerAssembly
import PalPeg.GalilFrontier

set_option autoImplicit false

namespace PalPeg.GalilThrottledRun

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain

/-! ## 1. Truncation -/

def dropN (d : ℕ) (l : List (Fin 2)) : List (Fin 2) := l.take (l.length - d)

def truncPH (d : ℕ) (p : GalilScaffoldInputHead.PlaceHead) : GalilScaffoldInputHead.PlaceHead :=
  ⟨{ p.head with incoming := dropN d p.head.incoming }, p.gap⟩

def truncW (d : ℕ) (w : GalilScaffoldChainWatch.State) : GalilScaffoldChainWatch.State :=
  ⟨⟨truncPH d w.machine.verifier, w.machine.control⟩, w.lag, w.margin⟩

def truncChain (d : ℕ) : ChainVM → ChainVM
  | .idle => .idle
  | .copy t h p v lag margin ver => .copy t h p v lag margin (truncPH d ver)
  | .back v h lag margin ver => .back v h lag margin (truncPH d ver)
  | .watch w => .watch (truncW d w)
  | .broken w => .broken (truncW d w)

def truncVM (d : ℕ) (s : GalilVM) : GalilVM :=
  { s with
    left := truncPH d s.left
    center := truncPH d s.center
    right := truncPH d s.right
    chain := truncChain d s.chain }

def truncS (d : ℕ) (st : State GalilVM) : State GalilVM := ⟨st.ctl, truncVM d st.vm⟩

theorem dropN_zero (l : List (Fin 2)) : dropN 0 l = l := by simp [dropN]

theorem truncPH_zero (p : GalilScaffoldInputHead.PlaceHead) : truncPH 0 p = p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  simp [truncPH, dropN_zero]

theorem truncW_zero (w : GalilScaffoldChainWatch.State) : truncW 0 w = w := by
  rcases w with ⟨⟨v, c⟩, l, m⟩
  simp [truncW, truncPH_zero]

theorem truncChain_zero (x : ChainVM) : truncChain 0 x = x := by
  cases x <;> simp [truncChain, truncPH_zero, truncW_zero]

theorem truncVM_zero (s : GalilVM) : truncVM 0 s = s := by
  cases s
  simp [truncVM, truncPH_zero, truncChain_zero]

theorem truncS_zero (st : State GalilVM) : truncS 0 st = st := by
  rcases st with ⟨c, s⟩
  simp [truncS, truncVM_zero]

theorem position_trunc (d : ℕ) (p : GalilScaffoldInputHead.PlaceHead) : position (truncPH d p) = position p := rfl

/-- The prefix-report fields that only read positions, counters and the controller
are invariant under truncation. -/
theorem minv_trunc (raw : List (Fin 2)) (d : ℕ) (c : Control) (s : GalilVM) :
    MInv raw c (truncVM d s) ↔ MInv raw c s := Iff.rfl

theorem onLetterVM_trunc (raw : List (Fin 2)) (d : ℕ) (s : GalilVM) :
    onLetterVM raw (truncVM d s) ↔ onLetterVM raw s := Iff.rfl

theorem leftFirstVM_trunc (d : ℕ) (s : GalilVM) :
    leftFirstVM (truncVM d s) ↔ leftFirstVM s := Iff.rfl

/-! ## 2. Consumption and suffix form -/

def usedPH (n : ℕ) (p : GalilScaffoldInputHead.PlaceHead) : ℕ := n - p.head.incoming.length

def verOf : ChainVM → Option GalilScaffoldInputHead.PlaceHead
  | .idle => none
  | .copy _ _ _ _ _ _ ver => some ver
  | .back _ _ _ _ ver => some ver
  | .watch w => some w.machine.verifier
  | .broken w => some w.machine.verifier

def usedChain (n : ℕ) (x : ChainVM) : ℕ :=
  match verOf x with
  | none => 0
  | some p => usedPH n p

/-- Letters consumed by the furthest FIFO of the VM (L, C, R, chain verifier). -/
def usedVM (raw : List (Fin 2)) (s : GalilVM) : ℕ :=
  max (max (usedPH raw.length s.left) (usedPH raw.length s.center))
    (max (usedPH raw.length s.right) (usedChain raw.length s.chain))

def SufPH (raw : List (Fin 2)) (p : GalilScaffoldInputHead.PlaceHead) : Prop := ∃ c, p.head.incoming = raw.drop c

/-- Every FIFO of the VM is a suffix of the pre-loaded word. -/
def SufVM (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  SufPH raw s.left ∧ SufPH raw s.center ∧ SufPH raw s.right ∧
    ∀ p, verOf s.chain = some p → SufPH raw p

theorem dropN_arrive (raw : List (Fin 2)) (c j : ℕ) (hj : j < raw.length)
    (hc : raw.length - (raw.drop c).length ≤ j) :
    dropN (raw.length - j) (raw.drop c) ++ [raw[j]] = dropN (raw.length - (j+1)) (raw.drop c) := by
  simp only [dropN, List.length_drop]
  have hcj : c ≤ j := by
    rw [List.length_drop] at hc
    omega
  have e1 : raw.length - c - (raw.length - (j+1)) = (j - c) + 1 := by omega
  have e2 : raw.length - c - (raw.length - j) = j - c := by omega
  rw [e1, e2, List.take_add_one, List.getElem?_drop]
  have e3 : c + (j - c) = j := by omega
  rw [e3, List.getElem?_eq_getElem hj]
  rfl

theorem arrivePH_trunc (raw : List (Fin 2)) (j : ℕ) (hj : j < raw.length) (p : GalilScaffoldInputHead.PlaceHead)
    (hs : SufPH raw p) (hu : usedPH raw.length p ≤ j) :
    arrivePH raw[j] (truncPH (raw.length - j) p) = truncPH (raw.length - (j+1)) p := by
  obtain ⟨c, hc⟩ := hs
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  simp only at hc
  subst hc
  simp only [usedPH] at hu
  simp only [arrivePH, truncPH]
  rw [dropN_arrive raw c j hj hu]

theorem arriveChain_trunc (raw : List (Fin 2)) (j : ℕ) (hj : j < raw.length) (x : ChainVM)
    (hs : ∀ p, verOf x = some p → SufPH raw p) (hu : usedChain raw.length x ≤ j) :
    arriveChain raw[j] (truncChain (raw.length - j) x) = truncChain (raw.length - (j+1)) x := by
  cases x with
  | idle => rfl
  | copy t h p v lag margin ver =>
    simp only [arriveChain, truncChain]
    rw [arrivePH_trunc raw j hj ver (hs ver rfl) hu]
  | back v h lag margin ver =>
    simp only [arriveChain, truncChain]
    rw [arrivePH_trunc raw j hj ver (hs ver rfl) hu]
  | watch w =>
    simp only [arriveChain, truncChain, arriveW, truncW]
    rw [arrivePH_trunc raw j hj _ (hs _ rfl) hu]
  | broken w =>
    simp only [arriveChain, truncChain, arriveW, truncW]
    rw [arrivePH_trunc raw j hj _ (hs _ rfl) hu]

theorem arriveVM'_eq (a : Fin 2) (s : GalilVM) :
    arriveVM' a s = { s with
      left := arrivePH a s.left
      center := arrivePH a s.center
      right := arrivePH a s.right
      chain := arriveChain a s.chain } := rfl

/-- **Arrival undoes one step of truncation.** -/
theorem arrive_trunc (raw : List (Fin 2)) (j : ℕ) (hj : j < raw.length) (x : State GalilVM)
    (hs : SufVM raw x.vm) (hu : usedVM raw x.vm ≤ j) :
    arriveState' raw[j] (truncS (raw.length - j) x) = truncS (raw.length - (j+1)) x := by
  rcases x with ⟨c, s⟩
  obtain ⟨hl, hc, hr, hch⟩ := hs
  simp only [usedVM] at hu
  have hul : usedPH raw.length s.left ≤ j := by omega
  have huc : usedPH raw.length s.center ≤ j := by omega
  have hur : usedPH raw.length s.right ≤ j := by omega
  have huch : usedChain raw.length s.chain ≤ j := by omega
  have e1 := arrivePH_trunc raw j hj _ hl hul
  have e2 := arrivePH_trunc raw j hj _ hc huc
  have e3 := arrivePH_trunc raw j hj _ hr hur
  have e4 := arriveChain_trunc raw j hj _ hch huch
  simp only [arriveState', truncS]
  congr 1
  rw [arriveVM'_eq]
  simp only [truncVM]
  rw [e1, e2, e3, e4]


/-! ## 3. The need of a pre-loaded tick -/

def needS (raw : List (Fin 2)) (st : ℕ → State GalilVM) (i : ℕ) : ℕ := usedVM raw (st i).vm

def pmax (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | i+1 => max (pmax f i) (f (i+1))

theorem le_pmax (f : ℕ → ℕ) : ∀ k i, i ≤ k → f i ≤ pmax f k := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst this
    exact le_rfl
  | succ k ih =>
    intro i hi
    by_cases h : i ≤ k
    · exact le_trans (ih i h) (le_max_left _ _)
    · have : i = k+1 := by omega
      subst this
      exact le_max_right _ _

theorem pmax_le (f : ℕ → ℕ) (b : ℕ) : ∀ k, (∀ i, i ≤ k → f i ≤ b) → pmax f k ≤ b := by
  intro k
  induction k with
  | zero => intro h; exact h 0 le_rfl
  | succ k ih => intro h; exact max_le (ih fun i hi => h i (by omega)) (h _ le_rfl)

/-- Letters the pre-loaded tick `st k → st (k+1)` needs to have arrived: the prefix
maximum of `needS` up to `k+1`. -/
def need (raw : List (Fin 2)) (st : ℕ → State GalilVM) (k : ℕ) : ℕ := pmax (needS raw st) (k+1)

theorem needS_le_need (raw : List (Fin 2)) (st : ℕ → State GalilVM) {i k : ℕ} (h : i ≤ k+1) :
    needS raw st i ≤ need raw st k := le_pmax _ _ _ h

/-- **`need` is non-decreasing.** -/
theorem need_mono (raw : List (Fin 2)) (st : ℕ → State GalilVM) {k k' : ℕ} (h : k ≤ k') :
    need raw st k ≤ need raw st k' :=
  pmax_le _ _ _ fun i hi => le_pmax _ _ _ (by omega)

/-- If consumption is already monotone along the trace, `need` is the plain consumption
after the tick. -/
theorem need_eq_of_mono (raw : List (Fin 2)) (st : ℕ → State GalilVM)
    (hm : ∀ i, needS raw st i ≤ needS raw st (i+1)) (k : ℕ) :
    need raw st k = needS raw st (k+1) := by
  have hle : ∀ i j, i ≤ j → needS raw st i ≤ needS raw st j := by
    intro i j hij
    induction j with
    | zero => have : i = 0 := by omega
              subst this; exact le_rfl
    | succ j ih =>
      by_cases h : i ≤ j
      · exact le_trans (ih h) (hm j)
      · have : i = j+1 := by omega
        subst this; exact le_rfl
  exact le_antisymm (pmax_le _ _ _ fun i hi => hle i _ hi) (le_pmax _ _ _ le_rfl)

/-! ## 4. The throttled schedule -/

structure Cfg where
  k : ℕ
  j : ℕ

theorem τ_eq : GalilLedgerAssembly.τ = 131072 := by
  unfold GalilLedgerAssembly.τ; norm_num

/-- One throttled index: an arrival when the next letter is due (letter `j` at index
`j·τ`), else the next pre-loaded tick when its need is met, else a stutter. -/
def stepCfg (n e : ℕ) (nd : ℕ → ℕ) (t : ℕ) (c : Cfg) : Cfg :=
  if c.j < n ∧ c.j * GalilLedgerAssembly.τ ≤ t then ⟨c.k, c.j + 1⟩
  else if c.k < e ∧ nd c.k ≤ c.j then ⟨c.k + 1, c.j⟩ else c

def cfg (n e : ℕ) (nd : ℕ → ℕ) : ℕ → Cfg
  | 0 => ⟨0, 0⟩
  | t+1 => stepCfg n e nd t (cfg n e nd t)

theorem cfg_succ_cases (n e : ℕ) (nd : ℕ → ℕ) (t : ℕ) :
    ((cfg n e nd t).j < n ∧ (cfg n e nd t).j * GalilLedgerAssembly.τ ≤ t ∧
        cfg n e nd (t+1) = ⟨(cfg n e nd t).k, (cfg n e nd t).j + 1⟩) ∨
      (¬ ((cfg n e nd t).j < n ∧ (cfg n e nd t).j * GalilLedgerAssembly.τ ≤ t) ∧
        (cfg n e nd t).k < e ∧ nd (cfg n e nd t).k ≤ (cfg n e nd t).j ∧
        cfg n e nd (t+1) = ⟨(cfg n e nd t).k + 1, (cfg n e nd t).j⟩) ∨
      (¬ ((cfg n e nd t).j < n ∧ (cfg n e nd t).j * GalilLedgerAssembly.τ ≤ t) ∧
        ¬ ((cfg n e nd t).k < e ∧ nd (cfg n e nd t).k ≤ (cfg n e nd t).j) ∧
        cfg n e nd (t+1) = cfg n e nd t) := by
  show _ ∨ _ ∨ _
  have hd : cfg n e nd (t+1) = stepCfg n e nd t (cfg n e nd t) := rfl
  rw [hd]
  unfold stepCfg
  by_cases h1 : (cfg n e nd t).j < n ∧ (cfg n e nd t).j * GalilLedgerAssembly.τ ≤ t
  · exact Or.inl ⟨h1.1, h1.2, if_pos h1⟩
  · by_cases h2 : (cfg n e nd t).k < e ∧ nd (cfg n e nd t).k ≤ (cfg n e nd t).j
    · exact Or.inr (Or.inl ⟨h1, h2.1, h2.2, by rw [if_neg h1, if_pos h2]⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, by rw [if_neg h1, if_neg h2]⟩)

/-- Arithmetic invariants of the schedule: arrivals happen exactly on time. -/
theorem cfg_inv (n e : ℕ) (nd : ℕ → ℕ) : ∀ t,
    (cfg n e nd t).j ≤ n ∧ (cfg n e nd t).k ≤ e ∧
    ((cfg n e nd t).j < n → t ≤ (cfg n e nd t).j * GalilLedgerAssembly.τ) ∧
    (0 < (cfg n e nd t).j → ((cfg n e nd t).j - 1) * GalilLedgerAssembly.τ < t) := by
  intro t
  induction t with
  | zero => simp [cfg]
  | succ t ih =>
    rw [τ_eq] at ih ⊢
    obtain ⟨i1, i2, i3, i4⟩ := ih
    rcases cfg_succ_cases n e nd t with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · rw [h3]; rw [τ_eq] at h2; simp only; omega
    · rw [h4]; rw [τ_eq] at h1; simp only
      refine ⟨i1, by omega, fun h => ?_, fun h => by have := i4 h; omega⟩
      have := i3 h
      by_contra hc
      exact h1 ⟨h, by omega⟩
    · rw [h3]; rw [τ_eq] at h1
      refine ⟨i1, i2, fun h => ?_, fun h => by have := i4 h; omega⟩
      by_contra hc
      exact h1 ⟨h, by omega⟩

/-- Consumption invariant: everything the pre-loaded prefix up to `k` consumed has arrived. -/
theorem cfg_used (n e : ℕ) (nd f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hnd : ∀ k i, i ≤ k+1 → f i ≤ nd k) :
    ∀ t i, i ≤ (cfg n e nd t).k → f i ≤ (cfg n e nd t).j := by
  intro t
  induction t with
  | zero =>
    intro i hi
    have : i = 0 := by simpa [cfg] using hi
    subst this
    simp [cfg, hf0]
  | succ t ih =>
    intro i hi
    rcases cfg_succ_cases n e nd t with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · rw [h3] at hi ⊢; exact le_trans (ih i hi) (Nat.le_succ _)
    · rw [h4] at hi ⊢; exact le_trans (hnd _ i hi) h3
    · rw [h3] at hi ⊢; exact ih i hi

theorem cfg_mono (n e : ℕ) (nd : ℕ → ℕ) (t : ℕ) :
    (cfg n e nd t).k ≤ (cfg n e nd (t+1)).k ∧ (cfg n e nd (t+1)).k ≤ (cfg n e nd t).k + 1 ∧
      (cfg n e nd t).j ≤ (cfg n e nd (t+1)).j := by
  rcases cfg_succ_cases n e nd t with ⟨_, _, h3⟩ | ⟨_, _, _, h4⟩ | ⟨_, _, h3⟩
  · rw [h3]; simp
  · rw [h4]; simp
  · rw [h3]; simp

theorem cfg_mono_le (n e : ℕ) (nd : ℕ → ℕ) {t t' : ℕ} (h : t ≤ t') :
    (cfg n e nd t).k ≤ (cfg n e nd t').k ∧ (cfg n e nd t).j ≤ (cfg n e nd t').j := by
  induction t' with
  | zero => have : t = 0 := by omega
            subst this; exact ⟨le_rfl, le_rfl⟩
  | succ t' ih =>
    by_cases ht : t ≤ t'
    · obtain ⟨a, b⟩ := ih ht
      obtain ⟨c, -, d⟩ := cfg_mono n e nd t'
      exact ⟨le_trans a c, le_trans b d⟩
    · have : t = t' + 1 := by omega
      subst this; exact ⟨le_rfl, le_rfl⟩

/-- No stutter inside a window where the pending ticks' needs have arrived. -/
theorem window (n e : ℕ) (nd : ℕ → ℕ) (B J t0 : ℕ) (hB : B ≤ e)
    (hnd : ∀ k, k < B → nd k ≤ J) (hJ : J ≤ (cfg n e nd t0).j) :
    ∀ L, (cfg n e nd (t0+L)).k < B →
      (cfg n e nd (t0+L)).k + (cfg n e nd (t0+L)).j = (cfg n e nd t0).k + (cfg n e nd t0).j + L := by
  intro L
  induction L with
  | zero => intro _; rfl
  | succ L ih =>
    intro hK
    have hm := cfg_mono n e nd (t0+L)
    have hK' : (cfg n e nd (t0+L)).k < B := by
      have : t0 + (L+1) = t0 + L + 1 := by omega
      rw [this] at hK; omega
    have e1 := ih hK'
    have hjj := (cfg_mono_le n e nd (Nat.le_add_right t0 L)).2
    have heq : t0 + (L+1) = t0 + L + 1 := by omega
    rw [heq] at hK ⊢
    rcases cfg_succ_cases n e nd (t0+L) with ⟨_, _, h3⟩ | ⟨_, _, _, h4⟩ | ⟨_, h2, _⟩
    · rw [h3]; simp only; omega
    · rw [h4]; simp only; omega
    · exact absurd ⟨by omega, le_trans (hnd _ hK') (le_trans hJ hjj)⟩ h2

/-- **The per-prefix throttled step.** From any index `t1` at which the pre-loaded
prefix `Tc m` has been played, by `max t1 ((m+1)·τ) + (2·Δ + 1)` the prefix
`Tc (m+1)` has been played (`Δ = Tc (m+1) - Tc m`); arrivals in that window
are at most one per `τ` indices, hence the factor `2`. -/
theorem ostep (n e : ℕ) (nd Tc : ℕ → ℕ) (m : ℕ) (hm : m < n) (hTc : Tc m ≤ Tc (m+1))
    (hTe : Tc (m+1) ≤ e) (hnd : ∀ k, k < Tc (m+1) → nd k ≤ m+1) (t1 : ℕ)
    (hK1 : Tc m ≤ (cfg n e nd t1).k) :
    Tc (m+1) ≤ (cfg n e nd (max t1 ((m+1) * GalilLedgerAssembly.τ) +
      (2 * (Tc (m+1) - Tc m) + 1))).k := by
  generalize ht0 : max t1 ((m+1) * GalilLedgerAssembly.τ) = t0
  have ha : t1 ≤ t0 := ht0 ▸ le_max_left _ _
  have hb : (m+1) * GalilLedgerAssembly.τ ≤ t0 := ht0 ▸ le_max_right _ _
  generalize hL : 2 * (Tc (m+1) - Tc m) + 1 = L
  by_contra hlt
  have hlt' : (cfg n e nd (t0+L)).k < Tc (m+1) := by omega
  obtain ⟨i1, -, i3, -⟩ := cfg_inv n e nd t0
  obtain ⟨j1, -, -, j4⟩ := cfg_inv n e nd (t0+L)
  rw [τ_eq] at hb i3 j4
  have hj0 : m+1 ≤ (cfg n e nd t0).j := by
    by_cases h : (cfg n e nd t0).j < n
    · have := i3 h; omega
    · omega
  have hw := window n e nd (Tc (m+1)) (m+1) t0 hTe hnd hj0 L hlt'
  have hk0 := (cfg_mono_le n e nd ha).1
  have hjm := (cfg_mono_le n e nd (Nat.le_add_right t0 L)).2
  by_cases h : (cfg n e nd t0).j < n
  · have := i3 h
    by_cases hp : 0 < (cfg n e nd (t0+L)).j
    · have := j4 hp; omega
    · omega
  · omega

/-! ## 5. The throttled run -/

variable (raw : List (Fin 2)) (st : ℕ → State GalilVM) (e : ℕ)

/-- The throttled schedule of the pre-loaded trace `st` (ticks `< e`). -/
abbrev cfgT (t : ℕ) : Cfg := cfg raw.length e (need raw st) t

/-- Throttled states: the pre-loaded state with only the arrived letters in its FIFOs. -/
def stT (t : ℕ) : State GalilVM :=
  truncS (raw.length - (cfgT raw st e t).j) (st (cfgT raw st e t).k)

/-- Arrivals so far. -/
def arrT (t : ℕ) : ℕ := (cfgT raw st e t).j

/-- **The one open obligation (truncation commutation).** A pre-loaded tick whose
before- and after-consumption is at most `j` is also a tick with only `j` letters
arrived. This is the reverse direction of `GalilArriveChain.tick_arrive_comm'`;
its discharge needs the analogues of that lemma's side conditions (`hinit`,
`hsh`, `hlive` with `Frontier`) plus the fact that no FIFO read inside the
tick is later discarded (e.g. a chain verifier consumed and then dropped by
`beginFallback`) beyond what `needS` at the endpoints records. -/
def TruncTick (F : Frame GalilVM) (delay : ℕ) : Prop :=
  ∀ k, k < e → ∀ j, j ≤ raw.length → needS raw st k ≤ j → needS raw st (k+1) ≤ j →
    Tick F delay (truncS (raw.length - j) (st k)) (truncS (raw.length - j) (st (k+1)))

/-- **`AbstractRun'` for the throttled run.** -/
theorem abstractRun_throttled (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hctl : (st 0).ctl = GalilScaffoldController.initial delay)
    (h0 : needS raw st 0 = 0)
    (hsuf : ∀ k, k ≤ e → SufVM raw (st k).vm)
    (htt : TruncTick raw st e (galilFrameS P q first) delay) :
    AbstractRun' P q first delay raw (stT raw st e) (arrT raw st e) := by
  refine ⟨hctl, rfl, fun t => ?_⟩
  have hused := cfg_used raw.length e (need raw st) (needS raw st) h0
    (fun k i hi => needS_le_need raw st hi) t
  obtain ⟨-, hke, -, -⟩ := cfg_inv raw.length e (need raw st) t
  rcases cfg_succ_cases raw.length e (need raw st) t with ⟨h1, _, h3⟩ | ⟨_, h2, h3, h4⟩ | ⟨_, _, h3⟩
  · refine Or.inr ⟨by simp only [arrT, cfgT, h3], raw[(cfgT raw st e t).j], ?_, ?_⟩
    · exact List.getElem?_eq_getElem h1
    · simp only [stT, cfgT, h3]
      exact (arrive_trunc raw _ h1 _ (hsuf _ hke) (hused _ le_rfl)).symm
  · refine Or.inl ⟨by simp only [arrT, cfgT, h4], Or.inl ?_⟩
    simp only [stT, cfgT, h4]
    obtain ⟨i1, -, -, -⟩ := cfg_inv raw.length e (need raw st) t
    exact htt _ h2 _ i1 (hused _ le_rfl) (le_trans (needS_le_need raw st le_rfl) h3)
  · refine Or.inl ⟨by simp only [arrT, cfgT, h3], Or.inr ?_⟩
    simp only [stT, cfgT, h3]

/-! ## 6. Checkpoint times of the throttled run and the O-step -/

open Classical in
/-- First throttled index at which the pre-loaded prefix `Tc m` has been played. -/
noncomputable def TcT (Tc : ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : ∃ t, Tc m ≤ (cfgT raw st e t).k then Nat.find h else 0

theorem TcT_spec (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgT raw st e t).k) :
    Tc m ≤ (cfgT raw st e (TcT raw st e Tc m)).k ∧
      ∀ t, Tc m ≤ (cfgT raw st e t).k → TcT raw st e Tc m ≤ t := by
  unfold TcT
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun t ht => Nat.find_min' h ht⟩

theorem TcT_exact (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgT raw st e t).k) :
    (cfgT raw st e (TcT raw st e Tc m)).k = Tc m := by
  obtain ⟨h1, h2⟩ := TcT_spec raw st e Tc m h
  refine le_antisymm ?_ h1
  rcases hT : TcT raw st e Tc m with _ | t'
  · simp [cfgT, cfg]
  · have hlt : ¬ Tc m ≤ (cfgT raw st e t').k := fun hc => by
      have := h2 t' hc; omega
    have := (cfg_mono raw.length e (need raw st) t').2.1
    simp only [cfgT] at hlt this ⊢
    omega

/-- Hypotheses on the pre-loaded trace, with `e = Tc |raw|`. -/
structure Preload (Tc : ℕ → ℕ) : Prop where
  tc0 : Tc 0 = 0
  mono : ∀ m, m < raw.length → Tc m ≤ Tc (m+1)
  need0 : needS raw st 0 = 0
  needLe : ∀ m, m < raw.length → ∀ k, k < Tc (m+1) → need raw st k ≤ m+1

theorem preload_le_end {Tc : ℕ → ℕ} (hp : Preload raw st Tc) {m : ℕ} (hm : m ≤ raw.length) :
    Tc m ≤ Tc raw.length :=
  GalilCheckpoints.mono_of_step Tc raw.length hp.mono m raw.length hm le_rfl

theorem TcT_exists {Tc : ℕ → ℕ} (hp : Preload raw st Tc) :
    ∀ m, m ≤ raw.length → ∃ t, Tc m ≤ (cfg raw.length (Tc raw.length) (need raw st) t).k := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, by rw [hp.tc0]; exact Nat.zero_le _⟩
  | succ m ih =>
    intro hm
    obtain ⟨hK, -⟩ := TcT_spec raw st (Tc raw.length) Tc m (ih (by omega))
    exact ⟨_, ostep raw.length _ (need raw st) Tc m hm (hp.mono m hm)
      (preload_le_end raw st hp hm) (hp.needLe m hm) _ hK⟩

/-- `dw` of the throttled run: `2·(Tc k − Tc (k−1)) + 1`. -/
def dwT (Tc : ℕ → ℕ) (k : ℕ) : ℕ := 2 * (Tc k - Tc (k-1)) + 1

theorem TcT_zero {Tc : ℕ → ℕ} (hp : Preload raw st Tc) : TcT raw st (Tc raw.length) Tc 0 = 0 := by
  have h := TcT_exists raw st hp 0 (Nat.zero_le _)
  have := (TcT_spec raw st _ Tc 0 h).2 0 (by rw [hp.tc0]; exact Nat.zero_le _)
  omega

/-- **O-step for the throttled checkpoint times.** -/
theorem O_step_throttled {Tc : ℕ → ℕ} (hp : Preload raw st Tc) (m : ℕ) (hm : m < raw.length) :
    TcT raw st (Tc raw.length) Tc (m+1) ≤
      max (TcT raw st (Tc raw.length) Tc m) ((m+1) * GalilLedgerAssembly.τ) + dwT Tc (m+1) := by
  obtain ⟨hK, -⟩ := TcT_spec raw st (Tc raw.length) Tc m (TcT_exists raw st hp m hm.le)
  have ho := ostep raw.length _ (need raw st) Tc m hm (hp.mono m hm)
    (preload_le_end raw st hp hm) (hp.needLe m hm) _ hK
  have := (TcT_spec raw st (Tc raw.length) Tc (m+1) (TcT_exists raw st hp (m+1) hm)).2 _ ho
  simpa [dwT] using this

/-! ## 7. Report point transport and the ledger -/

theorem used_right_of_represents (raw : List (Fin 2)) (p : GalilScaffoldInputHead.PlaceHead)
    (hr : GalilScaffoldInputTrace.Represents p.head raw) (hpos : position p = 2 * raw.length - 1)
    (hn : 0 < raw.length) : usedPH raw.length p = raw.length := by
  rcases p with ⟨hd, g⟩
  obtain ⟨xs, rs, q, hh, hw⟩ := hr
  simp only at hh
  subst hh
  have hl : (GalilScaffoldInputHead.layout xs (rs.map some) q).left.length = xs.length := by
    cases xs <;> simp [GalilScaffoldInputHead.layout]
  have hi : (GalilScaffoldInputHead.layout xs (rs.map some) q).incoming = q := by
    cases xs <;> rfl
  have hlen : raw.length = xs.length + rs.length + q.length := by
    rw [hw]; simp only [List.length_append, List.length_reverse]
  cases g <;> simp only [position, hl, if_true, if_false, Bool.false_eq_true] at hpos <;>
    simp only [usedPH, hi] <;> omega

theorem used_of_report {P : Shared} {q : ℕ} {first : Fin 9} {x : State GalilVM}
    (hn : 0 < raw.length) (h : GalilLedgerAssembly.ReportPointAt P q first raw raw.length x) :
    raw.length ≤ usedVM raw x.vm := by
  obtain ⟨r, hi⟩ := h.scanInv
  have := used_right_of_represents raw x.vm.right hi.rightRep h.atPrefix hn
  unfold usedVM
  omega

/-- **Report point transport.** At the throttled checkpoint of the whole word every
letter has arrived, so the throttled state *is* the pre-loaded report state. -/
theorem stT_at_end {Tc : ℕ → ℕ} (hp : Preload raw st Tc) (hn : 0 < raw.length)
    {P : Shared} {q : ℕ} {first : Fin 9}
    (hrep : GalilLedgerAssembly.ReportPointAt P q first raw raw.length (st (Tc raw.length))) :
    stT raw st (Tc raw.length) (TcT raw st (Tc raw.length) Tc raw.length) = st (Tc raw.length) := by
  have hex := TcT_exists raw st hp raw.length le_rfl
  have hk := TcT_exact raw st (Tc raw.length) Tc raw.length hex
  have hused := cfg_used raw.length (Tc raw.length) (need raw st) (needS raw st) hp.need0
    (fun k i hi => needS_le_need raw st hi) (TcT raw st (Tc raw.length) Tc raw.length)
    (Tc raw.length) (by simp only [cfgT] at hk; omega)
  have hu := used_of_report raw hn hrep
  obtain ⟨i1, -, -, -⟩ := cfg_inv raw.length (Tc raw.length) (need raw st)
    (TcT raw st (Tc raw.length) Tc raw.length)
  have hjn : (cfgT raw st (Tc raw.length) (TcT raw st (Tc raw.length) Tc raw.length)).j = raw.length := by
    simp only [cfgT, needS] at hused i1 ⊢
    omega
  unfold stT
  rw [hjn, hk, Nat.sub_self, truncS_zero]

/-- **Ledger obligation for the throttled runs.** (O-check is only needed at `m = |w|`;
O-cost is restated for `dwT`.) -/
theorem ledger_throttled (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → Preload w (stOf w) (TcOf w))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      dwT (TcOf w) (m+1) ≤
        GalilLedgerQ64.alpha' 2048 * (Cw w (m+1) - Cw w m) + GalilLedgerQ64.beta' 2048) :
    LedgerObligation Pof qof firstOf
      (fun w => stT w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * GalilLedgerAssembly.τ) := by
  intro w hw hpal
  have hp := hpre w hw
  have hz := GalilLedgerAssembly.backlog_zero_trunc w hw hpal (dwT (TcOf w)) (O_cost w hw)
  have ht := GalilLedgerAssembly.on_time_trunc w (dwT (TcOf w))
    (TcT w (stOf w) (TcOf w w.length) (TcOf w)) (TcT_zero w (stOf w) hp)
    (O_step_throttled w (stOf w) hp) hz
  obtain ⟨hrp, hfr⟩ := GalilLedgerAssembly.reportPoint_of_at_length hw (hrep w hw)
  refine ⟨TcT w (stOf w) (TcOf w w.length) (TcOf w) w.length, ht, ?_, ?_⟩
  · show ReportPoint w (stT w (stOf w) (TcOf w w.length) _)
    rw [stT_at_end w (stOf w) hp hw (hrep w hw)]; exact hrp
  · show Refreshed _ _ _ (stT w (stOf w) (TcOf w w.length) _)
    rw [stT_at_end w (stOf w) hp hw (hrep w hw)]; exact hfr

#print axioms truncS_zero
#print axioms arrive_trunc
#print axioms need_mono
#print axioms need_eq_of_mono
#print axioms cfg_inv
#print axioms cfg_used
#print axioms window
#print axioms ostep
#print axioms abstractRun_throttled
#print axioms TcT_exact
#print axioms TcT_exists
#print axioms O_step_throttled
#print axioms used_of_report
#print axioms stT_at_end
#print axioms ledger_throttled

end PalPeg.GalilThrottledRun
