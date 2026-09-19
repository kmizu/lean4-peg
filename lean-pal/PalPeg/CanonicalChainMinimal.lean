import PalPeg.CanonicalSearchHistory
import PalPeg.CanonicalFallbackInput
import PalPeg.GalilShiftH
import PalPeg.GalilPeriodNext

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.CanonicalChainMinimal

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open PalPeg.CanonicalSearchProgram PalPeg.GalilShiftH
open GalilScaffoldTop GalilScaffoldController GalilRunSkeleton GalilInvPlus3
open PalPeg.WindowInv PalPeg.WindowRun PalPeg.WindowPack PalPeg.ShiftPalAlongTrace
open PalPeg.CloseoutPackRun26

/-- The least-candidate meaning carried through one chain lifetime while its
logical centre is fixed.  Copy states retain the remaining unary answer;
settled states retain the completed block and its exact semiperiod length. -/
def SemWith (Cert : ℕ → Prop) : ChainVM → Prop
  | .idle => True
  | x@(.copy t h p v lag margin ver) =>
      ∃ H n, CopyInv t h p v n ∧ cells v + n = H + 1 ∧ Cert H
  | x => Settled x ∧ ∃ H, BlockInv x ∧ cellsOf x = H + 1 ∧ Cert H

/-- The least-candidate instance of `SemWith`. -/
def Sem (raw : List (Fin 2)) (C : ℕ) : ChainVM → Prop :=
  SemWith (fun H => FutureMinimal raw C H ∧ MoveMinimal raw C H)

theorem sem_start {raw : List (Fin 2)} {C H : ℕ}
    {answer : GalilScaffoldTape.Tape} {cc : Fin 3} {walker : GalilScaffoldPlace.Place}
    {ver : PlaceHead} {radius : Counter}
    (hcopy : CopyInv answer reset walker (GalilScaffoldChainPeriod.start cc) H)
    (hmin : FutureMinimal raw C H) (hmove : MoveMinimal raw C H) :
    Sem raw C (chainStart answer cc walker ver radius) := by
  refine ⟨H,H,hcopy,?_,hmin,hmove⟩
  rw [cells_start]
  omega

/-- One background chain step preserves the fixed-centre semantic datum. -/
theorem sem_step {Cert : ℕ → Prop} {x y : ChainVM}
    (hx : SemWith Cert x) (ht : ChainStep x y) : SemWith Cert y := by
  cases ht with
  | idle => trivial
  | brokenIdle w => exact hx
  | copyBit t h p v lag margin ver a hone legal present =>
    obtain ⟨H,n,hcopy,hcells,hmin⟩ := hx
    cases n with
    | zero =>
      have hz := answerAhead_zero hcopy.1
      omega
    | succ n =>
      refine ⟨H,n,copyInv_step hcopy a,?_,hmin⟩
      have hv := cells_put v a hcopy.2.2.1.1
      omega
  | copyEnd t h p v lag margin ver b hleft hp hv =>
    obtain ⟨H,n,hcopy,hcells,hmin⟩ := hx
    have hn : n = 0 := by
      rcases n with _ | n
      · rfl
      · have hf := answerAhead_succ_focus hcopy.1
        rw [hleft] at hf
        cases hf
    subst n
    have hblock := onBlock_write_last hcopy.2.2.1 b hv
    refine ⟨trivial,H,hblock,?_,hmin⟩
    change cells (GalilScaffoldChainPeriod.write v (.last b)) = H+1
    rw [cells_write]
    omega
  | backStep v h lag margin ver hf =>
    obtain ⟨hs,H,hblock,hcells,hmin⟩ := hx
    have hh := settled_step (.backStep v h lag margin ver hf) hs hblock
    exact ⟨hh.1,H,blockInv_step (.backStep v h lag margin ver hf) hblock,
      hh.2.trans hcells,hmin⟩
  | backDone v h lag margin ver hf =>
    obtain ⟨hs,H,hblock,hcells,hmin⟩ := hx
    have hh := settled_step (.backDone v h lag margin ver hf) hs hblock
    exact ⟨hh.1,H,blockInv_step (.backDone v h lag margin ver hf) hblock,
      hh.2.trans hcells,hmin⟩
  | watchStep w w' hi =>
    obtain ⟨hs,H,hblock,hcells,hmin⟩ := hx
    have hh := settled_step (.watchStep w w' hi) hs hblock
    exact ⟨hh.1,H,blockInv_step (.watchStep w w' hi) hblock,
      hh.2.trans hcells,hmin⟩
  | watchBreak w hb =>
    obtain ⟨hs,H,hblock,hcells,hmin⟩ := hx
    have hh := settled_step (.watchBreak w hb) hs hblock
    exact ⟨hh.1,H,blockInv_step (.watchBreak w hb) hblock,
      hh.2.trans hcells,hmin⟩

/-- The match-credit half of a chain tick preserves the same datum. -/
theorem sem_matched {Cert : ℕ → Prop} {x y : ChainVM}
    (hx : SemWith Cert x) (ht : ChainMatched x y) : SemWith Cert y := by
  cases ht with
  | idle => exact hx
  | copy => exact hx
  | back v h lag margin ver => exact hx
  | watch w w' ho =>
    obtain ⟨hs,H,hblock,hcells,hmin⟩ := hx
    have hh := settled_matched (.watch w w' ho) hs hblock
    exact ⟨hh.1,H,blockInv_matched (.watch w w' ho) hblock,
      hh.2.trans hcells,hmin⟩
  | breaks w w' hb =>
    obtain ⟨hs,H,hblock,hcells,hmin⟩ := hx
    have hh := settled_matched (.breaks w w' hb) hs hblock
    exact ⟨hh.1,H,blockInv_matched (.breaks w w' hb) hblock,
      hh.2.trans hcells,hmin⟩
  | brokenMatched => exact hx

theorem sem_tick {Cert : ℕ → Prop} {a : Bool} {x y : ChainVM}
    (hx : SemWith Cert x) (ht : ChainTick a x y) : SemWith Cert y := by
  obtain ⟨z,hz,ha⟩ := ht
  have hs := sem_step hx hz
  cases a with
  | false => rw [ha]; exact hs
  | true => exact sem_matched hs ha

/-- At watch, the stored candidate is exactly `periodLength`. -/
theorem watch_minimal {raw : List (Fin 2)} {C : ℕ}
    {w : GalilScaffoldChainWatch.State} (h : Sem raw C (.watch w)) :
    FutureMinimal raw C (periodLength w) := by
  obtain ⟨_,H,_,hcells,hmin⟩ := h
  have hp := periodLength_succ_eq_cells w
  change cellsOf (.watch w) = H+1 at hcells
  change periodLength w + 1 = cellsOf (.watch w) at hp
  have : periodLength w = H := by omega
  rw [this]
  exact hmin.1

/-- The same stored least candidate, in the form used by fallback moves. -/
theorem watch_moveMinimal {raw : List (Fin 2)} {C : ℕ}
    {w : GalilScaffoldChainWatch.State} (h : Sem raw C (.watch w)) :
    MoveMinimal raw C (periodLength w) := by
  obtain ⟨_,H,_,hcells,hmin⟩ := h
  have hp := periodLength_succ_eq_cells w
  change cellsOf (.watch w) = H+1 at hcells
  change periodLength w + 1 = cellsOf (.watch w) at hp
  have he : periodLength w = H := by omega
  rw [he]
  exact hmin.2

/-- Every live chain state retains its birth semiperiod and the direct
fallback minimality certificate. -/
theorem sem_moveData {raw : List (Fin 2)} {C : ℕ} {x : ChainVM}
    (hx : Sem raw C x) (hne : x ≠ .idle) :
    ∃ h, MoveMinimal raw C h := by
  cases x with
  | idle => exact (hne rfl).elim
  | copy t h p v lag margin ver =>
      obtain ⟨H,_,_,_,_,hm⟩ := hx
      exact ⟨H,hm⟩
  | back v h lag margin ver | watch v | broken v =>
      obtain ⟨_,H,_,_,_,hm⟩ := hx
      exact ⟨H,hm⟩

theorem sem_chainAt {raw : List (Fin 2)} {C : ℕ}
    {a found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PlaceHead} {rad : Counter} {x y : ChainVM}
    (hx : Sem raw C x)
    (hbirth : x = .idle → found = true → ∃ H,
      CopyInv ans reset wk (GalilScaffoldChainPeriod.start cc) H ∧ FutureMinimal raw C H ∧
      MoveMinimal raw C H)
    (ht : chainAt a found ans cc wk ver rad x y) : Sem raw C y := by
  rcases ht with ⟨_,ht⟩ | ⟨_,_,hy⟩ | ⟨hi,hf,hy⟩
  · exact sem_tick hx ht
  · rw [hy]; trivial
  · obtain ⟨H,hcopy,hmin,hmove⟩ := hbirth hi hf
    have hb := sem_start (ver := ver) (radius := rad) hcopy hmin hmove
    cases a with
    | false => simp only [Bool.false_eq_true,reduceIte] at hy; rw [hy]; exact hb
    | true => exact sem_matched hb hy

/-- The exact short-period conclusion consumed by `OracleRun.shiftLeaf`, once
the run invariant supplies the semantic datum for its target watch. -/
theorem watch_no_short {raw : List (Fin 2)} {C k : ℕ}
    {w : GalilScaffoldChainWatch.State}
    (hsem : Sem raw C (.watch w))
    (hleft : k < C)
    (hpal : Manacher.PalAt (encoded raw) C k)
    (hfour : 4 * periodLength w ≤ k)
    (hperiod : HasPeriod (Span raw C k) (2 * periodLength w)) :
    ∀ p, 0 < p → p < 2 * periodLength w → ¬ HasPeriod (Span raw C k) p := by
  exact watch_minimal hsem k hleft hpal hfour hperiod

/-- Minimality at the next scan centre, computed already at the shift entry.
This is the mathematical payload carried unchanged while the `h` unit shift
ticks execute. -/
theorem watch_no_short_next {raw : List (Fin 2)} {C k h : ℕ}
    {w : GalilScaffoldChainWatch.State}
    (hsem : Sem raw C (.watch w))
    (hh : h = periodLength w)
    (hh0 : 0 < h)
    (hkC : k < C)
    (hpal0 : Manacher.PalAt (encoded raw) C k)
    (hpal1 : Manacher.PalAt (encoded raw) (C + h) (k + 1 - h))
    (hfour : 4 * h ≤ k)
    (hright : PeriodOn (encoded raw) (2*h) (C+1) (C+k+1)) :
    ∀ p, 0 < p → p < 2*h →
      ¬ HasPeriod (Span raw (C+h) (k+1-h)) p := by
  have hk2 : 2*h ≤ k := by omega
  have hperAll := periodOn_span_of_next hh0 hk2 hpal0 hpal1 hright
  have hper0 : HasPeriod (Span raw C k) (2*h) :=
    hasPeriod_span_of_next hh0 hk2 hpal0 hpal1 hright
  have hmin0 : ∀ p, 0 < p → p < 2*h → ¬ HasPeriod (Span raw C k) p := by
    have hfour' : 4 * periodLength w ≤ k := by rwa [← hh]
    have hper0' : HasPeriod (Span raw C k) (2 * periodLength w) := by rwa [← hh]
    intro p hp hp2
    apply watch_no_short hsem hkC hpal0 hfour' hper0' p hp
    rwa [← hh]
  have hperOld : PeriodOn (encoded raw) (2*h) (C-k) (C+k) :=
    hperAll.mono (le_refl _) (by omega)
  have hminOld : ∀ p, 0 < p → p < 2*h →
      ¬ PeriodOn (encoded raw) p (C-k) (C+k) := by
    intro p hp hp2 hpo
    apply hmin0 p hp hp2
    unfold Span
    have hkCle : k ≤ C := Nat.le_of_lt hkC
    rw [show 2*k+1 = (C+k)+1-(C-k) from by omega]
    exact (hasPeriod_slice_iff (x := encoded raw) (p := p) hpal0.2.1 (by omega)).mpr hpo
  have hperNew : PeriodOn (encoded raw) (2*h)
      (C+h-(k+1-h)) (C+h+(k+1-h)) := hperAll.mono (by omega) (by omega)
  have hnext := noBelow_next hh0 hk2 (by omega) (by omega) hpal0.1 hpal1.1
    hpal1.2.1 hperOld hminOld hperNew
  intro p hp hp2 hcon
  apply hnext p hp hp2
  unfold Span at hcon
  have hkC' : k + 1 - h ≤ C + h := hpal1.1
  rw [show 2*(k+1-h)+1 = (C+h+(k+1-h))+1-(C+h-(k+1-h)) from by omega] at hcon
  exact (hasPeriod_slice_iff (x := encoded raw) (p := p) hpal1.2.1 (by omega)).mp hcon

/-- After a shift, only radii at least the landing radius occur on the same
scan lifetime.  This thresholded form is therefore the invariant needed for
all later guarded shifts. -/
def TailMinimal (raw : List (Fin 2)) (C h base : ℕ) : Prop :=
  ∀ k, base ≤ k → k < C → Manacher.PalAt (encoded raw) C k →
    HasPeriod (Span raw C k) (2*h) →
    ∀ p, 0 < p → p < 2*h → ¬ HasPeriod (Span raw C k) p

theorem tailMinimal_of_future {raw : List (Fin 2)} {C h : ℕ}
    (hm : FutureMinimal raw C h) : TailMinimal raw C h (4*h) := by
  intro k hk hkC hpal hper
  exact hm k hkC hpal hk hper

/-- A minimal seed span remains a minimal-period witness for every enclosing
span: any period of the latter restricts to the seed. -/
theorem tailMinimal_of_seed {raw : List (Fin 2)} {C h base : ℕ}
    (hpal : Manacher.PalAt (encoded raw) C base)
    (hseed : ∀ p, 0 < p → p < 2*h → ¬ HasPeriod (Span raw C base) p) :
    TailMinimal raw C h base := by
  intro k hfk hkC hpalK _ p hp hp2 hkper
  apply hseed p hp hp2
  unfold Span at hkper ⊢
  have hbaseC : base ≤ C := hpal.1
  have hkCle : k ≤ C := Nat.le_of_lt hkC
  have hd := hasPeriod_drop_drop (d := k-base) hkper (by omega)
  have ht := hasPeriod_take_drop (m := 2*base+1) hd (by omega)
  simpa [show C-k+(k-base)=C-base from by omega] using ht

theorem tailMinimal_next {raw : List (Fin 2)} {C k h : ℕ}
    {w : GalilScaffoldChainWatch.State}
    (hsem : Sem raw C (.watch w))
    (hh : h = periodLength w) (hh0 : 0 < h) (hkC : k < C)
    (hpal0 : Manacher.PalAt (encoded raw) C k)
    (hpal1 : Manacher.PalAt (encoded raw) (C+h) (k+1-h))
    (hfour : 4*h ≤ k)
    (hright : PeriodOn (encoded raw) (2*h) (C+1) (C+k+1)) :
    TailMinimal raw (C+h) h (k+1-h) := by
  apply tailMinimal_of_seed hpal1
  exact watch_no_short_next hsem hh hh0 hkC hpal0 hpal1 hfour hright

/-- The two possible histories of a live watch at a scan state: before its
first shift it still carries the DP certificate; afterwards it carries the
thresholded certificate produced at the preceding shift entry. -/
def WatchMinimal (raw : List (Fin 2)) (C k : ℕ)
    (w : GalilScaffoldChainWatch.State) : Prop :=
  Sem raw C (.watch w) ∨
  ∃ base, base ≤ k ∧ TailMinimal raw C (periodLength w) base

theorem watchMinimal_no_short {raw : List (Fin 2)} {C k : ℕ}
    {w : GalilScaffoldChainWatch.State}
    (hm : WatchMinimal raw C k w) (hkC : k < C)
    (hpal : Manacher.PalAt (encoded raw) C k)
    (hfour : 4 * periodLength w ≤ k)
    (hperiod : HasPeriod (Span raw C k) (2 * periodLength w)) :
    ∀ p, 0 < p → p < 2 * periodLength w → ¬ HasPeriod (Span raw C k) p := by
  rcases hm with hsem | ⟨base,hbase,htail⟩
  · exact watch_no_short hsem hkC hpal hfour hperiod
  · exact htail k hbase hkC hpal hperiod

theorem tailMinimal_next_of_tail {raw : List (Fin 2)} {C k h base : ℕ}
    (htail : TailMinimal raw C h base) (hbase : base ≤ k)
    (hh0 : 0 < h) (hkC : k < C)
    (hpal0 : Manacher.PalAt (encoded raw) C k)
    (hpal1 : Manacher.PalAt (encoded raw) (C+h) (k+1-h))
    (hfour : 4*h ≤ k)
    (hright : PeriodOn (encoded raw) (2*h) (C+1) (C+k+1)) :
    TailMinimal raw (C+h) h (k+1-h) := by
  have hk2 : 2*h ≤ k := by omega
  have hperAll := periodOn_span_of_next hh0 hk2 hpal0 hpal1 hright
  have hper0 : HasPeriod (Span raw C k) (2*h) :=
    hasPeriod_span_of_next hh0 hk2 hpal0 hpal1 hright
  have hmin0 := htail k hbase hkC hpal0 hper0
  have hperOld : PeriodOn (encoded raw) (2*h) (C-k) (C+k) :=
    hperAll.mono (le_refl _) (by omega)
  have hminOld : ∀ p, 0 < p → p < 2*h →
      ¬ PeriodOn (encoded raw) p (C-k) (C+k) := by
    intro p hp hp2 hpo
    apply hmin0 p hp hp2
    unfold Span
    have hkCle : k ≤ C := Nat.le_of_lt hkC
    rw [show 2*k+1 = (C+k)+1-(C-k) from by omega]
    exact (hasPeriod_slice_iff (x := encoded raw) (p := p) hpal0.2.1 (by omega)).mpr hpo
  have hperNew : PeriodOn (encoded raw) (2*h)
      (C+h-(k+1-h)) (C+h+(k+1-h)) := hperAll.mono (by omega) (by omega)
  have hnext := noBelow_next hh0 hk2 (by omega) (by omega) hpal0.1 hpal1.1
    hpal1.2.1 hperOld hminOld hperNew
  apply tailMinimal_of_seed hpal1
  intro p hp hp2 hcon
  apply hnext p hp hp2
  unfold Span at hcon
  have hkC' : k+1-h ≤ C+h := hpal1.1
  rw [show 2*(k+1-h)+1 = (C+h+(k+1-h))+1-(C+h-(k+1-h)) from by omega] at hcon
  exact (hasPeriod_slice_iff (x := encoded raw) (p := p) hpal1.2.1 (by omega)).mp hcon

/-- The left-half period and the single caught-up frontier comparison carried
by `FreshShiftLedger` are exactly the right-side period needed at a shift. -/
theorem periodOn_right_succ {α : Type} {x : List α} {C k h : ℕ}
    (hpal : Manacher.PalAt x C k) (hh : 2*h ≤ k)
    (hleft : PeriodOn x (2*h) (C-k) C)
    (hcaught : x[C+k+1-2*h]? = x[C+k+1]?) :
    PeriodOn x (2*h) (C+1) (C+k+1) := by
  have hright : PeriodOn x (2*h) C (C+k) :=
    PalPeg.periodOn_mirror' hpal hh hleft
  intro i hi hib
  rcases Nat.lt_or_eq_of_le hib with hlt | heq
  · exact hright i (by omega) (by omega)
  · have hi' : i = C+k+1-2*h := by omega
    rw [hi']
    have he : C+k+1-2*h+2*h = C+k+1 := by omega
    rw [he]
    exact hcaught

theorem watchMinimal_next {raw : List (Fin 2)} {C k h : ℕ}
    {w : GalilScaffoldChainWatch.State}
    (hm : WatchMinimal raw C k w) (hh : h = periodLength w)
    (hh0 : 0 < h) (hkC : k < C)
    (hpal0 : Manacher.PalAt (encoded raw) C k)
    (hpal1 : Manacher.PalAt (encoded raw) (C+h) (k+1-h))
    (hfour : 4*h ≤ k)
    (hleft : PeriodOn (encoded raw) (2*h) (C-k) C)
    (hcaught : (encoded raw)[C+k+1-2*h]? = (encoded raw)[C+k+1]?) :
    TailMinimal raw (C+h) h (k+1-h) := by
  have hright := periodOn_right_succ hpal0 (by omega) hleft hcaught
  rcases hm with hsem | ⟨base,hbase,htail⟩
  · exact tailMinimal_next hsem hh hh0 hkC hpal0 hpal1 hfour hright
  · have htail' : TailMinimal raw C h base := by rw [hh]; exact htail
    exact tailMinimal_next_of_tail htail' hbase hh0 hkC hpal0 hpal1 hfour hright

/-- Minimality payload at a scan state.  Copy/back phases retain their birth
certificate; a watch records the actual scan radius and either the birth or
post-shift certificate. -/
def ScanMinimal (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  match s.chain with
  | .copy t h p v lag margin ver =>
      Sem raw (position s.center) (.copy t h p v lag margin ver)
  | .back v h lag margin ver =>
      Sem raw (position s.center) (.back v h lag margin ver)
  | .watch w =>
      ∃ k, position s.right = position s.center + k ∧
        WatchMinimal raw (position s.center) k w
  | _ => True

/-- The active phases before the first watch is installed. -/
def PreShift : ChainVM → Prop
  | .copy .. | .back .. => True
  | _ => False

theorem scanMinimal_preShift_sem {raw : List (Fin 2)} {s : GalilVM}
    (hm : ScanMinimal raw s) (hpre : PreShift s.chain) :
    Sem raw (position s.center) s.chain := by
  cases h : s.chain with
  | idle => simp [PreShift,h] at hpre
  | copy => simpa [ScanMinimal,h] using hm
  | back => simpa [ScanMinimal,h] using hm
  | watch => simp [PreShift,h] at hpre
  | broken => simp [PreShift,h] at hpre

/-- During shift mode, the destination centre and landing radius are already
fixed.  Unit shift ticks merely decrease `rem`. -/
def ShiftMinimal (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  ∃ (w : GalilScaffoldChainWatch.State) (rem radius : ℕ),
    s.chain = .watch w ∧ s.remaining = ofNat rem ∧
    position s.right = position s.center + rem + radius ∧
    TailMinimal raw (position s.center + rem) (periodLength w) radius

theorem scanMinimal_watch_no_short {raw : List (Fin 2)} {s : GalilVM}
    {w : GalilScaffoldChainWatch.State} (hm : ScanMinimal raw s)
    (hw : s.chain = .watch w) {k : ℕ}
    (hright : position s.right = position s.center + k)
    (hkC : k < position s.center)
    (hpal : Manacher.PalAt (encoded raw) (position s.center) k)
    (hfour : 4 * periodLength w ≤ k)
    (hperiod : HasPeriod (Span raw (position s.center) k) (2 * periodLength w)) :
    ∀ p, 0 < p → p < 2 * periodLength w →
      ¬ HasPeriod (Span raw (position s.center) k) p := by
  simp only [ScanMinimal, hw] at hm
  obtain ⟨k',hk',hmin⟩ := hm
  have : k' = k := by omega
  subst k'
  exact watchMinimal_no_short hmin hkC hpal hfour hperiod

theorem shiftMinimal_shiftOne {raw : List (Fin 2)} {s s' : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hw : s.chain = .watch w)
    (hchain : s'.chain = .watch (chainShiftOne w))
    (hcenter : position s'.center = position s.center + 1)
    (hright : s'.right = s.right)
    (hrem : s'.remaining = dec s.remaining)
    (hpos : positive s.remaining = true)
    (hm : ShiftMinimal raw s) : ShiftMinimal raw s' := by
  obtain ⟨w0,rem,radius,hc,hrm,hr,htail⟩ := hm
  have hwe : w0 = w := by rw [hw] at hc; cases hc; rfl
  subst w0
  cases rem with
  | zero => rw [hrm] at hpos; exact absurd hpos (by decide)
  | succ rem =>
    refine ⟨chainShiftOne w,rem,radius,hchain,?_,?_,?_⟩
    · rw [hrem,hrm,dec_ofNat_succ]
    · rw [hright,hr,hcenter]
      omega
    · have hdest : position s'.center + rem = position s.center + (rem+1) := by omega
      rw [hdest]
      simpa [periodLength,chainShiftOne] using htail

theorem scanMinimal_shiftDone {raw : List (Fin 2)} {s : GalilVM}
    (hpos : positive s.remaining = false)
    (hm : ShiftMinimal raw s) : ScanMinimal raw s := by
  obtain ⟨w,rem,radius,hchain,hrem,hright,htail⟩ := hm
  have hz : rem = 0 := by
    cases rem with
    | zero => rfl
    | succ n => rw [hrem] at hpos; simp [positive,ofNat] at hpos
  subst rem
  simp only [ScanMinimal,hchain]
  refine ⟨radius,?_,Or.inr ⟨radius,le_rfl,?_⟩⟩
  · simpa using hright
  · simpa using htail

theorem watchMinimal_tick {raw : List (Fin 2)} {C k k' : ℕ}
    {w w' : GalilScaffoldChainWatch.State} {a : Bool}
    (hm : WatchMinimal raw C k w)
    (ht : ChainTick a (.watch w) (.watch w'))
    (hb : BlockInv (.watch w))
    (hkk : k ≤ k') : WatchMinimal raw C k' w' := by
  rcases hm with hsem | ⟨base,hbase,htail⟩
  · exact Or.inl (sem_tick hsem ht)
  · right
    refine ⟨base,le_trans hbase hkk,?_⟩
    have hc := (settled_tick ht (by trivial) hb).2
    have hp := periodLength_succ_eq_cells w
    have hp' := periodLength_succ_eq_cells w'
    change periodLength w + 1 = cellsOf (.watch w) at hp
    change periodLength w' + 1 = cellsOf (.watch w') at hp'
    change cellsOf (.watch w') = cellsOf (.watch w) at hc
    have heq : periodLength w' = periodLength w := by omega
    rwa [heq]

theorem watchMinimal_matched {raw : List (Fin 2)} {C k k' : ℕ}
    {w w' : GalilScaffoldChainWatch.State}
    (hm : WatchMinimal raw C k w)
    (ht : ChainMatched (.watch w) (.watch w'))
    (hb : BlockInv (.watch w)) (hkk : k ≤ k') : WatchMinimal raw C k' w' := by
  rcases hm with hsem | ⟨base,hbase,htail⟩
  · exact Or.inl (sem_matched hsem ht)
  · right
    refine ⟨base,le_trans hbase hkk,?_⟩
    have hc := (settled_matched ht (by trivial) hb).2
    have hp := periodLength_succ_eq_cells w
    have hp' := periodLength_succ_eq_cells w'
    change periodLength w+1 = cellsOf (.watch w) at hp
    change periodLength w'+1 = cellsOf (.watch w') at hp'
    change cellsOf (.watch w') = cellsOf (.watch w) at hc
    have heq : periodLength w' = periodLength w := by omega
    rwa [heq]

theorem scanMinimal_chainTick_watch {raw : List (Fin 2)} {s : GalilVM}
    {w : GalilScaffoldChainWatch.State} {a : Bool} {k : ℕ}
    (hm : ScanMinimal raw s)
    (ht : ChainTick a s.chain (.watch w))
    (hb : BlockInv s.chain)
    (hright : position s.right = position s.center + k) :
    WatchMinimal raw (position s.center) k w := by
  cases hs : s.chain with
  | idle =>
    rw [hs] at ht
    obtain ⟨z,hz,ha⟩ := ht
    cases hz
    cases a with
    | false => simp at ha
    | true => cases ha
  | broken wb =>
    rw [hs] at ht
    obtain ⟨z,hz,ha⟩ := ht
    cases hz
    cases a with
    | false => simp at ha
    | true => cases ha
  | copy t h p v lag margin ver =>
    simp only [ScanMinimal,hs] at hm
    exact Or.inl (sem_tick hm (by simpa [hs] using ht))
  | back v h lag margin ver =>
    simp only [ScanMinimal,hs] at hm
    exact Or.inl (sem_tick hm (by simpa [hs] using ht))
  | watch w0 =>
    simp only [ScanMinimal,hs] at hm
    obtain ⟨k0,hr0,hmin⟩ := hm
    have hk : k0 = k := by omega
    subst k0
    exact watchMinimal_tick hmin (by simpa [hs] using ht) (by simpa [hs] using hb) le_rfl

theorem scanMinimal_step {raw : List (Fin 2)} {s t : GalilVM}
    (hm : ScanMinimal raw s) (hb : BlockInv s.chain)
    (hstep : ChainStep s.chain t.chain)
    (hcenter : t.center = s.center) (hright : t.right = s.right)
    (hpos : position s.center ≤ position s.right) :
    ScanMinimal raw t := by
  generalize hs : s.chain = x at hm hb hstep
  generalize ht : t.chain = y at hstep ⊢
  cases hstep with
  | idle => simp [ScanMinimal,ht]
  | brokenIdle => simp [ScanMinimal,ht]
  | copyBit ta ha pa va laga margina vera a hone legal present =>
    simp only [ScanMinimal,hs,ht] at hm ⊢
    rw [hcenter]
    exact sem_step hm (.copyBit ta ha pa va laga margina vera a hone legal present)
  | copyEnd ta ha pa va laga margina vera b hleft hp hv =>
    simp only [ScanMinimal,hs,ht] at hm ⊢
    rw [hcenter]
    exact sem_step hm (.copyEnd ta ha pa va laga margina vera b hleft hp hv)
  | backStep v h lag margin ver hf =>
    simp only [ScanMinimal,hs,ht] at hm ⊢
    rw [hcenter]
    exact sem_step hm (.backStep v h lag margin ver hf)
  | backDone v h lag margin ver hf =>
    simp only [ScanMinimal,hs,ht] at hm ⊢
    refine ⟨position s.right-position s.center,?_,Or.inl ?_⟩
    · rw [hright,hcenter]
      omega
    · rw [hcenter]
      exact sem_step hm (.backDone v h lag margin ver hf)
  | watchStep w w' hi =>
    simp only [ScanMinimal,hs,ht] at hm ⊢
    obtain ⟨k,hr,hmin⟩ := hm
    refine ⟨k,by rw [hright,hcenter]; exact hr,?_⟩
    rw [hcenter]
    exact watchMinimal_tick (a := false) hmin ⟨_,.watchStep w w' hi,rfl⟩
      (by simpa using hb) le_rfl
  | watchBreak => simp [ScanMinimal,ht]

theorem scanMinimal_matched {raw : List (Fin 2)} {s t : GalilVM}
    (hm : ScanMinimal raw s) (hb : BlockInv s.chain)
    (hmatched : ChainMatched s.chain t.chain)
    (hcenter : t.center = s.center)
    {k k' : ℕ} (hr : position s.right = position s.center+k)
    (hr' : position t.right = position t.center+k') (hkk : k ≤ k') :
    ScanMinimal raw t := by
  generalize hs : s.chain = x at hm hb hmatched
  generalize ht : t.chain = y at hmatched ⊢
  cases hmatched with
  | idle => simp [ScanMinimal,ht]
  | copy ta ha pa va laga margina vera =>
    simp only [ScanMinimal,hs,ht] at hm ⊢
    rw [hcenter]
    exact sem_matched hm (.copy ta ha pa va laga margina vera)
  | back va ha laga margina vera =>
    simp only [ScanMinimal,hs,ht] at hm ⊢
    rw [hcenter]
    exact sem_matched hm (.back va ha laga margina vera)
  | watch w w' ho =>
    simp only [ScanMinimal,hs,ht] at hm ⊢
    obtain ⟨j,hjr,hmin⟩ := hm
    have hj : j = k := by omega
    subst j
    refine ⟨k',hr',?_⟩
    rw [hcenter]
    exact watchMinimal_matched hmin (.watch w w' ho) (by simpa [hs] using hb) hkk
  | breaks => simp [ScanMinimal,ht]
  | brokenMatched => simp [ScanMinimal,ht]

theorem scanMinimal_chainAt_false {raw : List (Fin 2)} {s t : GalilVM}
    {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PlaceHead} {rad : Counter}
    (hm : ScanMinimal raw s) (hb : BlockInv s.chain)
    (hbirth : s.chain = .idle → found = true → ∃ H,
      CopyInv ans reset wk (GalilScaffoldChainPeriod.start cc) H ∧
      FutureMinimal raw (position s.center) H ∧ MoveMinimal raw (position s.center) H)
    (hat : chainAt false found ans cc wk ver rad s.chain t.chain)
    (hcenter : t.center = s.center) (hright : t.right = s.right)
    (hpos : position s.center ≤ position s.right) : ScanMinimal raw t := by
  rcases hat with ⟨_,htick⟩ | ⟨_,_,hy⟩ | ⟨hi,hf,hy⟩
  · obtain ⟨z,hstep,hz⟩ := htick
    simp only [Bool.false_eq_true,reduceIte] at hz
    subst z
    exact scanMinimal_step hm hb hstep hcenter hright hpos
  · simp [ScanMinimal,hy]
  · simp only [Bool.false_eq_true,reduceIte] at hy
    obtain ⟨H,hcopy,hmin,hmove⟩ := hbirth hi hf
    have hs := sem_start (ver := ver) (radius := rad) hcopy hmin hmove
    simp only [ScanMinimal,hy]
    rw [hcenter]
    exact hs

theorem scanMinimal_chainAt_true {raw : List (Fin 2)} {s t : GalilVM}
    {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PlaceHead} {rad : Counter}
    {k k' : ℕ}
    (hm : ScanMinimal raw s) (hb : BlockInv s.chain)
    (hbirth : s.chain = .idle → found = true → ∃ H,
      CopyInv ans reset wk (GalilScaffoldChainPeriod.start cc) H ∧
      FutureMinimal raw (position s.center) H ∧ MoveMinimal raw (position s.center) H)
    (hat : chainAt true found ans cc wk ver rad s.chain t.chain)
    (hcenter : t.center = s.center)
    (hr : position s.right = position s.center+k)
    (hr' : position t.right = position t.center+k') (hkk : k ≤ k') :
    ScanMinimal raw t := by
  rcases hat with ⟨_,htick⟩ | ⟨_,_,hy⟩ | ⟨hi,hf,hy⟩
  · obtain ⟨z,hstep,hmatched⟩ := htick
    let u : GalilVM := {s with chain := z}
    have hmu : ScanMinimal raw u :=
      scanMinimal_step hm hb (by simpa [u] using hstep) (by simp [u]) (by simp [u]) (by omega)
    have hbu : BlockInv u.chain := by
      simpa [u] using blockInv_step hstep hb
    exact scanMinimal_matched hmu hbu (by simpa [u] using hmatched)
      hcenter (by simpa [u] using hr) hr' hkk
  · simp [ScanMinimal,hy]
  · obtain ⟨H,hcopy,hmin,hmove⟩ := hbirth hi hf
    have hs := sem_start (ver := ver) (radius := rad) hcopy hmin hmove
    have hs' : Sem raw (position s.center) t.chain := sem_matched hs hy
    generalize ht : t.chain = y at hy hs' ⊢
    unfold chainStart at hy
    cases hy
    simpa [ScanMinimal,ht,hcenter] using hs'

theorem scanMinimal_resize {raw : List (Fin 2)} {s t : GalilVM} {k k' : ℕ}
    (hm : ScanMinimal raw s) (hchain : t.chain = s.chain)
    (hcenter : t.center = s.center)
    (hr : position s.right = position s.center+k)
    (hr' : position t.right = position t.center+k') (hkk : k ≤ k') :
    ScanMinimal raw t := by
  cases hs : s.chain with
  | idle => simp [ScanMinimal,hchain,hs]
  | broken w => simp [ScanMinimal,hchain,hs]
  | copy a h p v lag margin ver =>
    simp only [ScanMinimal,hs] at hm
    simp only [ScanMinimal,hchain,hs]
    rw [hcenter]
    exact hm
  | back v h lag margin ver =>
    simp only [ScanMinimal,hs] at hm
    simp only [ScanMinimal,hchain,hs]
    rw [hcenter]
    exact hm
  | watch w =>
    simp only [ScanMinimal,hs] at hm
    simp only [ScanMinimal,hchain,hs]
    obtain ⟨j,hjr,hmin⟩ := hm
    have hj : j = k := by omega
    subst j
    refine ⟨k',hr',?_⟩
    rw [hcenter]
    rcases hmin with hsem | ⟨base,hbase,htail⟩
    · exact Or.inl hsem
    · exact Or.inr ⟨base,le_trans hbase hkk,htail⟩

def ModeMinimal (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  match c.mode with
  | .scan => ScanMinimal raw s
  | .shift => ShiftMinimal raw s
  | _ => True

/-- Core of the controller's `scan_shift` branch.  All arguments are fields
already exposed by `WindowRunPack`, `FreshShiftLedger`, and `beginShiftVM`. -/
theorem shiftMinimal_start {raw : List (Fin 2)} {s t : GalilVM}
    {w : GalilScaffoldChainWatch.State} {k h : ℕ}
    (hm : ScanMinimal raw s)
    (htick : ChainTick false s.chain (.watch w))
    (hb : BlockInv s.chain)
    (hradius : position s.right = position s.center + k)
    (hkC : k < position s.center)
    (hpal0 : Manacher.PalAt (encoded raw) (position s.center) k)
    (hh : h = periodLength w) (hh0 : 0 < h) (hfour : 4*h ≤ k)
    (hpal1 : Manacher.PalAt (encoded raw) (position s.center+h) (k+1-h))
    (hleft : PeriodOn (encoded raw) (2*h) (position s.center-k) (position s.center))
    (hcaught : (encoded raw)[position s.center+k+1-2*h]? =
      (encoded raw)[position s.center+k+1]?)
    (hcenter : t.center = s.center)
    (hright : position t.right = position s.right + 1)
    (hrem : t.remaining = ofNat h)
    (hchain : t.chain = .watch (GalilScaffoldChainWatch.immediate w))
    (hperiodI : periodLength (GalilScaffoldChainWatch.immediate w) = periodLength w) :
    ShiftMinimal raw t := by
  have hw := scanMinimal_chainTick_watch hm htick hb hradius
  have htail := watchMinimal_next hw hh hh0 hkC hpal0 hpal1 hfour hleft hcaught
  refine ⟨GalilScaffoldChainWatch.immediate w,h,k+1-h,hchain,hrem,?_,?_⟩
  · rw [hright,hradius,hcenter]
    omega
  · rw [hcenter,hperiodI]
    simpa [← hh] using htail

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

def BirthMinimal (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  ∀ a vq, s.chain = .idle → searchEffect (PofC centre place entry raw) a s vq →
    vq.search.mode = .found → ∃ H,
      CopyInv (vq.dp.config.tapes 11) reset ((PofC centre place entry raw).place s)
        (GalilScaffoldChainPeriod.start ((PofC centre place entry raw).centre s)) H ∧
      FutureMinimal raw (position s.center) H ∧ MoveMinimal raw (position s.center) H

/-- The ledger hidden inside `WindowPack.shiftPal_of_windowRunPack`, exposed
for the minimal-period payload of the same `scan_shift` branch. -/
theorem freshLedger_of_windowRunPack {raw : List (Fin 2)} {c : Control} {s s' : GalilVM}
    (hpack : PalPeg.CloseoutPackRun10.LPackM raw c s)
    (hwin : WindowRunPack raw c s) (hcan : canRight s.right)
    (hs : ScanNR ⟨c,s⟩)
    (hcmp : compareFound (PofC centre place entry raw) q first s s')
    (hmis : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s')
    (hguard : shiftGuardVM s') :
    ∀ wch : GalilScaffoldChainWatch.State, s'.chain = .watch wch →
      ∀ r₀, ScanInvariant raw (position s.center) r₀ s.left s.right →
        Manacher.PalAt (encoded raw) (position s.center-periodLength wch) (periodLength wch) ∧
        PeriodOn (encoded raw) (2*periodLength wch) (position s.center-r₀) (position s.center) ∧
        0 < periodLength wch ∧ 2*periodLength wch ≤ r₀ ∧
        (encoded raw)[position s.center+r₀+1-2*periodLength wch]? =
          (encoded raw)[position s.center+r₀+1]? := by
  obtain ⟨w₀,hw₀,hint⟩ := source_watch_of_guard hcmp hmis hguard
  obtain ⟨cen₀,cc,hcc,hinv,hk,-,-⟩ := hwin.window
  rw [hw₀] at hinv
  obtain ⟨b,xs,hW⟩ := hinv
  obtain ⟨n,hn⟩ := (hk w₀ hw₀).2 (by rw [hs.1]; decide)
  have hh : periodLength w₀ = xs.length+1 := periodLength_of_coreP hW.2.2
  obtain ⟨rad,hscan⟩ := hpack.scanGeom hs.1 hs.2
  have hpos : position s.right = position s.center+rad := hscan.rightPos
  have hgFour := hguard
  have hgFinal := hguard
  obtain ⟨wch,hwch,-,-,-,-,-⟩ := hguard
  have hW' : WatchWindow raw cen₀ (position s.right) cc b xs (.watch wch) :=
    watchWindow_step hW (hint wch hwch)
  have hh' : periodLength wch = xs.length+1 := periodLength_of_coreP hW'.2.2
  have hfour := four_of_guard centre place entry q first hwin.coupled hs hcmp hmis hgFour hwch
  obtain ⟨R',hRR,hR'⟩ := hwin.radiusScan hs.1
  have hfour' : 4*((xs.length+1 : ℕ) : ℤ) ≤ (R' : ℤ) := by
    have hv : value s.radius = (R' : ℤ) := hRR.2
    rw [← hh',← hv]
    exact hfour
  have hsize : 2*(xs.length+1) ≤ rad := by omega
  have hW2 : WatchWindow raw cen₀ (position s.center+rad) cc b xs s.chain := by
    rw [hw₀,← hpos]
    exact hW
  exact PalPeg.ShiftEntryFromLanding.freshShiftLedger_of_chainW_scan centre place entry q first
    hW2 (by rw [hn,hh]) hscan hcan hcc hsize hcmp hmis hgFinal

theorem scanMinimal_background {raw : List (Fin 2)} {s t : GalilVM}
    (hbg : (galilFrameS (PofC centre place entry raw) q first).background s t)
    (hm : ScanMinimal raw s) (hb : BlockInv s.chain)
    (hbirth : BirthMinimal centre place entry raw s)
    (hpos : position s.center ≤ position s.right) : ScanMinimal raw t := by
  obtain ⟨_,hr,hs,hch,heq⟩ := hbg
  have hc : t.center = s.center := by rw [heq,afterBirth_center]; rfl
  exact scanMinimal_chainAt_false hm hb
    (fun hi hf => hbirth false (searchLens.get t) hi hs (of_decide_eq_true hf))
    hch hc hr hpos

theorem scanMinimal_compare {raw : List (Fin 2)} {s t : GalilVM} {k k' : ℕ}
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s t)
    (hm : ScanMinimal raw s) (hb : BlockInv s.chain)
    (hbirth : BirthMinimal centre place entry raw s)
    (hr : position s.right = position s.center+k)
    (hr' : position t.right = position t.center+k') (hkk : k ≤ k') :
    ScanMinimal raw t := by
  obtain ⟨vs,vq,a,_,_,_,hs,hch,heq⟩ := hcmp
  have hc : t.center = s.center := by
    rw [heq,afterBirth_center]
    cases a <;> rfl
  have htc : t.chain = vs.chain := by
    rw [heq,afterBirth_chain]
    cases a <;> rfl
  cases a with
  | false =>
    let u : GalilVM := {s with chain := vs.chain}
    have hmu : ScanMinimal raw u := scanMinimal_chainAt_false hm hb
      (fun hi hf => hbirth false vq hi hs (of_decide_eq_true hf))
      (by simpa [u] using hch) (by simp [u]) (by simp [u]) (by omega)
    exact scanMinimal_resize hmu (by simpa [u] using htc) hc
      (by simpa [u] using hr) hr' hkk
  | true =>
    exact scanMinimal_chainAt_true hm hb
      (fun hi hf => hbirth true vq hi hs (of_decide_eq_true hf))
      (by simpa [htc] using hch) hc hr hr' hkk

theorem modeMinimal_shiftOne {raw : List (Fin 2)} {c : Control} {s t : GalilVM}
    (hm : c.mode = .shift) (hmin : ModeMinimal raw c s)
    (hwin : WindowRunPack raw c s)
    (hpos : positive s.remaining = true)
    (hso : (galilFrameS (PofC centre place entry raw) q first).shiftOne s t) :
    ModeMinimal raw c t := by
  have hshift : ShiftMinimal raw s := by simpa [ModeMinimal,hm] using hmin
  obtain ⟨⟨hcanC,_,_,w,hw,hget⟩,hset⟩ := hso
  change s.chain = .watch w at hw
  have hchain : t.chain = .watch (chainShiftOne w) := by rw [hset,hget]; rfl
  have hrem : t.remaining = dec s.remaining := by rw [hset,hget]; rfl
  have hright : t.right = s.right := by rw [hset]; rfl
  have htc : t.center = right s.center := by rw [hset,hget]; rfl
  have hcen := hwin.centreRep (Or.inr hm)
  have hl0 : 0 < s.center.head.left.length :=
    (represented_position _ raw hcen.1 hcen.2).1
  have hcenter : position t.center = position s.center+1 := by
    rw [htc,right_position s.center hcanC hl0]
  have hout := shiftMinimal_shiftOne hw hchain hcenter hright hrem hpos hshift
  simpa [ModeMinimal,hm] using hout

theorem modeMinimal_shiftDone {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hm : c.mode = .shift) (hmin : ModeMinimal raw c s)
    (hp : ¬ (galilFrameS (PofC centre place entry raw) q first).remainingPos s) :
    ModeMinimal raw {c with mode := .scan} s := by
  have hs : ShiftMinimal raw s := by simpa [ModeMinimal,hm] using hmin
  have hz : positive s.remaining = false := Bool.eq_false_iff.mpr (fun h => hp (Or.inl h))
  have hout := scanMinimal_shiftDone hz hs
  simpa [ModeMinimal] using hout

/-- The mathematical payload of the controller's `scan_shift` branch. -/
theorem shiftMinimal_scanShift {raw : List (Fin 2)} {c : Control} {s s' t : GalilVM}
    (hm : c.mode = .scan) (hr : c.replaying = false)
    (hmin : ModeMinimal raw c s)
    (hpack : PalPeg.CloseoutPackRun10.LPackM raw c s)
    (hwin : WindowRunPack raw c s)
    (hav : (galilFrameS (PofC centre place entry raw) q first).available s)
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s')
    (hmt : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s')
    (hg : shiftGuardVM s') (hb : beginShiftVM' s' t) : ShiftMinimal raw t := by
  have hscanMin : ScanMinimal raw s := by simpa [ModeMinimal,hm] using hmin
  have hcan : canRight s.right := hav
  obtain ⟨k,hscan⟩ := hpack.scanGeom hm hr
  have hpos : position s.right = position s.center+k := hscan.rightPos
  have hsNR : ScanNR ⟨c,s⟩ := ⟨hm,hr⟩
  obtain ⟨w,hw,_,_,_,_,_⟩ := id hg
  obtain ⟨w₀,hw₀,hint⟩ := source_watch_of_guard hcmp hmt hg
  have htick : ChainTick false s.chain (.watch w) := by
    refine ⟨.watch w, ?_, rfl⟩
    rw [hw₀]
    exact .watchStep w₀ w (hint w hw)
  have hledger := freshLedger_of_windowRunPack centre place entry q first hpack hwin hcan
    hsNR hcmp hmt hg w hw k hscan
  obtain ⟨_,hleft,hh0,_,hcaught⟩ := hledger
  have hsp := shiftPal_of_windowRunPack centre place entry q first hpack hwin hcan hsNR
  obtain ⟨_,_,hpal1⟩ := hsp s' hcmp hmt w hw hg k hscan
  have hfourZ := four_of_guard centre place entry q first hwin.coupled hsNR hcmp hmt hg hw
  obtain ⟨R,hRR,hposR⟩ := hwin.radiusScan hm
  have hkR : k = R := by omega
  have hfour : 4 * periodLength w ≤ k := by
    have hv : value s.radius = (R : ℤ) := hRR.2
    rw [hv] at hfourZ
    omega
  obtain ⟨wb,hwb,hbegin⟩ := hb
  have he : wb = w := by rw [hwb] at hw; exact ChainVM.watch.inj hw
  subst wb
  have hscenter : s'.center = s.center := by
    obtain ⟨vs,vq,a,_,_,_,_,_,heq⟩ : compareFound (PofC centre place entry raw) q first s s' := hcmp
    exact (PalPeg.WindowTick.compare_target_heads heq).2.2.2.1
  have hsright : position s'.right = position s.right+1 := by
    obtain ⟨vs,vq,a,_,hvr,_,_,_,heq⟩ : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨_,hsr,_,_,_⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hl0 : 0 < s.right.head.left.length :=
      (represented_position _ raw hscan.rightRep hscan.rightPresent).1
    rw [hsr,hvr,right_position _ hcan hl0]
  have htcenter : t.center = s.center := by rw [hbegin,hscenter]
  have htright : position t.right = position s.right+1 := by rw [hbegin,hsright]
  have htrem : t.remaining = ofNat (periodLength w) := by rw [hbegin]
  have htchain : t.chain = .watch (GalilScaffoldChainWatch.immediate w) := by rw [hbegin]
  have hblockW : OnBlock w.machine.control.period := by
    obtain ⟨mid,hstep,hmid⟩ := htick
    simp only [Bool.false_eq_true, ↓reduceIte] at hmid
    subst mid
    have hbW := blockInv_step hstep hwin.coupled.block
    exact hbW
  have hperiodI : periodLength (GalilScaffoldChainWatch.immediate w) = periodLength w :=
    PalPeg.GalilChainCoupling.periodLength_consume
      w.machine w.lag w.margin w.lag (inc w.margin) hblockW
  exact shiftMinimal_start hscanMin htick hwin.coupled.block hpos (scan_radius_lt hscan)
    hscan.palindrome rfl hh0 hfour hpal1 hleft hcaught htcenter htright htrem htchain hperiodI

/-- Controller transport, with the genuinely mathematical shift-entry case
factored out.  Every other branch is structural transport of the payload. -/
theorem modeMinimal_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hmin : ModeMinimal raw x.ctl x.vm)
    (hwinX : WindowRunPack raw x.ctl x.vm)
    (hwinY : WindowRunPack raw y.ctl y.vm)
    (hfront : PalPeg.GalilFrontMono.FrontPack x.ctl x.vm)
    (hrrep : x.ctl.mode = .scan → GalilScaffoldInputTrace.Represents x.vm.right.head raw)
    (hrpres : x.ctl.mode = .scan → x.vm.right.head.focus ≠ none)
    (hbirth : x.ctl.mode = .scan → BirthMinimal centre place entry raw x.vm)
    (hcopy : x.ctl.mode = .shift → CopyIdle x.vm)
    (hstart : ∀ c s s' t,
      x = ⟨c,s⟩ → y = ⟨{c with clock := 2048, mode := .shift},t⟩ →
      c.mode = .scan → (galilFrameS (PofC centre place entry raw) q first).available s →
      (galilFrameS (PofC centre place entry raw) q first).compare s s' →
      ¬ (galilFrameS (PofC centre place entry raw) q first).matched s' →
      c.replaying = false → shiftGuardVM s' → beginShiftVM' s' t →
      ShiftMinimal raw t) :
    ModeMinimal raw y.ctl y.vm := by
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    simp [ModeMinimal,ScanMinimal,hch]
  | scan_wait c s t hm hav hb =>
    have hs : ScanMinimal raw s := by simpa [ModeMinimal,hm] using hmin
    obtain ⟨R,_,hR⟩ := hwinX.radiusScan hm
    change position s.right = position s.center + R at hR
    simpa [ModeMinimal,hm] using
      scanMinimal_background centre place entry q first hb hs hwinX.coupled.block
        (hbirth hm) (by rw [hR]; omega)
  | scan_count c s t hm hav hc hb =>
    have hs : ScanMinimal raw s := by simpa [ModeMinimal,hm] using hmin
    obtain ⟨R,_,hR⟩ := hwinX.radiusScan hm
    change position s.right = position s.center + R at hR
    simpa [ModeMinimal,hm] using
      scanMinimal_background centre place entry q first hb hs hwinX.coupled.block
        (hbirth hm) (by rw [hR]; omega)
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hs : ScanMinimal raw s := by simpa [ModeMinimal,hm] using hmin
    obtain ⟨R,_,hR⟩ := hwinX.radiusScan hm
    obtain ⟨R',_,hR'⟩ := hwinY.radiusScan (by simpa using hm)
    change position s.right = position s.center + R at hR
    change position t.right = position t.center + R' at hR'
    have hp : position s'.right = position s.right + 1 := by
      have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
      obtain ⟨vs,vq,a,_,hvr,_,_,_,heq⟩ := hcmp'
      obtain ⟨_,hr,_,_,_⟩ := PalPeg.WindowTick.compare_target_heads heq
      have hcan : canRight s.right := by
        rcases hav with hrp | ha
        · exact PalPeg.CloseoutReplayCanRight.canRight_of_frontPack hfront hrp
        · exact ha
      have hl0 : 0 < s.right.head.left.length :=
        (represented_position _ raw (hrrep hm) (hrpres hm)).1
      rw [hr,hvr,right_position _ hcan hl0]
    have htc : t.center = s'.center := by rw [hpl]; split <;> rfl
    have htr : t.right = s'.right := by rw [hpl]; split <;> rfl
    have hsc : s'.center = s.center := by
      have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
      obtain ⟨vs,vq,a,_,_,_,_,_,heq⟩ := hcmp'
      exact (PalPeg.WindowTick.compare_target_heads heq).2.2.2.1
    have hRcmp : position s'.right = position s'.center + R' := by
      rw [← htr,← htc]
      exact hR'
    have hRR : R ≤ R' := by rw [hp,hR,hsc] at hRcmp; omega
    have hs' := scanMinimal_compare centre place entry q first hcmp hs hwinX.coupled.block
      (hbirth hm) hR hRcmp hRR
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have hcenter : t.center = s'.center := by rw [hpl]; split <;> rfl
    simpa [ModeMinimal,hm] using
      scanMinimal_resize hs' hchain hcenter hRcmp hR' (by omega)
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    have ha : (galilFrameS (PofC centre place entry raw) q first).available s := by
      rcases hav with hrep | ha
      · rw [hr] at hrep; cases hrep
      · exact ha
    simpa [ModeMinimal] using
      hstart c s s' t rfl rfl hm ha hcmp hmt hr hg hb
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    simp [ModeMinimal]
  | shift_one c s t hm hp hso =>
    have hpos : positive s.remaining = true := by
      rcases hp with hp | hp
      · exact hp
      · exact absurd hp (hcopy hm)
    exact modeMinimal_shiftOne centre place entry q first hm hmin hwinX hpos hso
  | shift_done c s o hm hp ho =>
    exact modeMinimal_shiftDone centre place entry q first hm hmin hp
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    simp [ModeMinimal,ScanMinimal,hch]
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    simp [ModeMinimal,ScanMinimal,hm]
  | copy_one _ _ _ hm _ _ | copy_done _ _ _ hm _ _
  | home_start _ _ _ hm _ _ | home_step _ _ _ hm _ _
  | fpp_slice _ _ _ hm _ | fpp_done _ _ _ hm _
  | markEnd_found _ _ _ hm _ _ | markEnd_step _ _ _ hm _ _
  | choose_select _ _ _ hm _ _ _ | choose_step _ _ _ hm _ _
  | rewind_done _ _ _ hm _ _ | rewind_one _ _ _ hm _ _ _
  | rewind_pair _ _ _ hm _ _ _ => simp [ModeMinimal,hm]

/-- Only the zero-lower stage needs the absolute least-period certificate. -/
def BudgetMinimal (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  s.lower = reset → ModeMinimal raw c s

private theorem searchStep_lower_eq {center : GalilScaffoldPlace.Place} {a : Bool}
    {v v' : SearchVM} (h : searchStep center a v v') : v'.lower = v.lower := by
  unfold searchStep at h
  cases hm : v.search.mode <;> simp only [hm] at h
  all_goals first
    | exact h.2.1
    | (rcases h with ⟨y,_,rfl⟩; rfl)
    | (rw [h])
    | (split at h <;> (rw [h] <;> rfl))

private theorem searchEffect_lower_eq {P : Shared} {a : Bool} {s : GalilVM}
    {v : SearchVM} (h : searchEffect P a s v) : v.lower = s.lower := by
  rcases h with ⟨_,hs⟩ | ⟨_,rfl⟩
  · exact searchStep_lower_eq hs
  · rfl

/-- Away from the three controller entries which reset the search state, a
canonical tick preserves `lower` exactly. -/
theorem lower_eq_of_regular_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hinit : x.ctl.mode ≠ .init) (hreplay : x.ctl.mode ≠ .replayStart)
    (hnr : x.ctl.mode = .scan → ¬ restartVM entry x.vm y.vm) :
    y.vm.lower = x.vm.lower := by
  cases ht <;> simp only
  case init c s t hm hi => exact absurd hm hinit
  case replayStart c s t o hm hi ho ho' => exact absurd hm hreplay
  case restart c s t hm hb => exact False.elim (hnr hm hb)
  case scan_wait c s t hm ha hb =>
    exact searchEffect_lower_eq hb.2.2.1
  case scan_count c s t hm ha hc hb =>
    exact searchEffect_lower_eq hb.2.2.1
  case scan_match c s u t o hm ha hc hcmp hmt hpl ho =>
    change t = (if c.replaying then {u with replay := dec u.replay} else u) at hpl
    rw [hpl]
    split
    all_goals obtain ⟨vs,vq,a,_,_,_,hse,_,rfl⟩ := hcmp
    all_goals rw [afterBirth_lower]
    all_goals cases a <;> change vq.lower = s.lower <;> exact searchEffect_lower_eq hse
  case scan_shift c s u t hm ha hc hcmp hmt hr hg hb =>
    obtain ⟨w,_,rfl⟩ := hb
    obtain ⟨vs,vq,a,_,_,_,hse,_,rfl⟩ := hcmp
    rw [afterBirth_lower]
    cases a <;> exact searchEffect_lower_eq hse
  case scan_fallback c s u t hm ha hc hcmp hmt hg hr hb =>
    obtain ⟨p,ht,_⟩ := hb
    rw [ht]
    obtain ⟨vs,vq,a,_,_,_,hse,_,rfl⟩ := hcmp
    rw [afterBirth_lower]
    cases a <;> exact searchEffect_lower_eq hse
  all_goals try rfl
  all_goals
    rename_i he
    rw [he.2]
    rfl

theorem budgetMinimal_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hcanon : PalPeg.GalilTickFair.Canonical entry 2048 x y)
    (hmin : BudgetMinimal raw x.ctl x.vm)
    (hpackX : PalPeg.CloseoutPackW.IPackMW centre place entry q first raw x)
    (hpackY : PalPeg.CloseoutPackW.IPackMW centre place entry q first raw y)
    (haux : PalPeg.CloseoutPackRun2.AuxPack x.ctl x.vm)
    (hbirth : x.vm.lower = reset → x.ctl.mode = .scan →
      BirthMinimal centre place entry raw x.vm) :
    BudgetMinimal raw y.ctl y.vm := by
  intro hy
  -- a restart installs a positive lower bound, so a tick into `lower = reset` is not one
  have hnr : x.ctl.mode = .scan → ¬ restartVM entry x.vm y.vm := by
    rintro - ⟨w0, -, -, hlast, -, ht0⟩
    have hl : y.vm.lower = w0.machine.control.last := by rw [ht0]
    rw [hl] at hy
    rw [hy] at hlast
    simp [positive, reset] at hlast
  have hxmin : ModeMinimal raw x.ctl x.vm := by
    by_cases hi : x.ctl.mode = .init
    · simp [ModeMinimal,hi]
    by_cases hp : x.ctl.mode = .replayStart
    · simp [ModeMinimal,hp]
    apply hmin
    rw [← lower_eq_of_regular_tick centre place entry q first ht hi hp hnr]
    exact hy
  have hscanInv : x.ctl.mode = .scan →
      ∃ k, ScanInvariant raw (position x.vm.center) k x.vm.left x.vm.right := by
    intro hm
    cases hr : x.ctl.replaying with
    | false => exact hpackX.pack.scanGeom hm hr
    | true => exact hpackX.m2.scanGeomR hm hr
  apply modeMinimal_tick centre place entry q first ht hxmin (hpackX.win hP) (hpackY.win hP)
    haux.front
  · intro hm; exact (hscanInv hm).choose_spec.rightRep
  · intro hm; exact (hscanInv hm).choose_spec.rightPresent
  · intro hm
    exact hbirth (by
      rw [← lower_eq_of_regular_tick centre place entry q first ht
        (by rw [hm]; decide) (by rw [hm]; decide) hnr]
      exact hy) hm
  · intro hm
    exact haux.copyP (by rw [hm]; decide)
  · intro c s s' t hx hy' hm hav hcmp hmt hr hg hb
    subst x
    cases hy'
    exact shiftMinimal_scanShift centre place entry q first hm hr hxmin hpackX.pack
      (hpackX.win hP) hav hcmp hmt hg hb

/-- The zero-lower minimal-period budget along an arbitrary canonical packed
prefix out of an `InvLPS` origin. -/
theorem budgetMinimal_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k
      ⟨c₀,r₀⟩ y) : BudgetMinimal raw y.ctl y.vm := by
  obtain ⟨g,hg0,hgk,htr,hcan,hpk⟩ := hrun
  have hprefix : ∀ i, i ≤ k →
      PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw i
        ⟨c₀,r₀⟩ (g i) := by
    intro i hi
    exact ⟨g,hg0,rfl,
      ⟨fun j hj => htr.tick j (by omega),fun j hj => htr.good j (by omega)⟩,
      fun j hj => hcan j (by omega),fun j hj => hpk j (by omega)⟩
  have hiMode : c₀.mode = .scan :=
    (PalPeg.GalilOracleLocal.invS_mode hI.1.1.1.1.1).1
  have hiChain : r₀.chain = .idle := by
    rcases hI.1.1.1.1.1 with h | ⟨_,h⟩
    · obtain ⟨_,_,h⟩ := h.rest; exact h.1
    · exact h.chainIdle
  have hlv0 := PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hI.1
  have haux0 : PalPeg.CloseoutPackRun2.AuxPack c₀ r₀ :=
    ⟨PalPeg.CloseoutPackRun.coupled_of_invLPC hI.1,
      PalPeg.CloseoutPackRun.front_of_invLPC hI.1,
      PalPeg.CloseoutPackRun.copyPack_of_invLPC hI.1⟩
  have haux : ∀ i, i ≤ k → PalPeg.CloseoutPackRun2.AuxPack (g i).ctl (g i).vm := by
    intro i hi
    have hs := PalPeg.CloseoutPackRun2.steps_of_trace htr i hi
    rw [hg0] at hs
    exact PalPeg.CloseoutPackRun2.auxPack_steps centre place entry q first hlv0 haux0 hs
  have hbud : ∀ i, i ≤ k → BudgetMinimal raw (g i).ctl (g i).vm := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hg0]
      intro _
      simp [ModeMinimal,hiMode,ScanMinimal,hiChain]
    | succ i ih =>
      intro hik
      apply budgetMinimal_tick centre place entry q first hP (htr.tick i (by omega))
        (hcan i (by omega)).canonical (ih (by omega)) (hpk i (by omega)) (hpk (i+1) (by omega))
        (haux i (by omega))
      intro hz hm a vq hidle he hf
      apply PalPeg.CanonicalSearchHistory.birthMinimals_packed centre place entry q first
        hP hI (hprefix i (by omega)) hm hidle he hf
      rw [searchEffect_lower_eq he,hz]
  rw [← hgk]
  exact hbud k le_rfl

/-- If the zero-lower search has parked in `missed`, its retained DP result
is already the complete Galil contract for the concrete fallback window. -/
theorem move_of_idle_missed_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {z : ChainVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k
      ⟨c₀,r₀⟩ ⟨c,s⟩)
    (hlower : s.lower = reset) (hm : c.mode = .scan) (hr : c.replaying = false)
    (hcan : canRight s.right) (hidle : s.chain = .idle)
    (hsearch : searchEffect (PofC centre place entry raw) false s vq)
    (hmiss : vq.search.mode = .missed) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨_,_,rad,hscan,hlen⟩ :=
    PalPeg.CanonicalFallbackInput.counters centre place entry q first hI hrun hm hr
  have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun
  have hcen := (hp.win hP).centreRep (Or.inl hm)
  have hvq : vq.lower = reset := (searchEffect_lower_eq hsearch).trans hlower
  have hdp := PalPeg.CanonicalSearchHistory.dpPack_of_idle_missed_packed
    centre place entry q first hP hI hrun hm hscan hcen hidle hsearch hmiss
    (fun δ hd hδ => by
      have hz : δ ≤ 0 := by simpa [hvq,reset,value] using hδ
      omega)
  exact PalPeg.CanonicalFallbackInput.move_of_dpPack
    (centre := centre) (place := place) (entry := entry) (c := c)
    hP hscan hcan hlen (scan_radius_lt hscan) hdp rfl

/-- A live chain discharges the fallback move leaf as soon as its retained
least candidate is still above the current quarter-radius threshold.  This is
the direct consumer for the pre-shift copy/back part of the active route. -/
theorem move_of_live_sem_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {z : ChainVM}
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k
      ⟨c₀,r₀⟩ ⟨c,s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hcan : canRight s.right)
    (hsem : Sem raw (position s.center) z) (hz : z ≠ .idle)
    (hquarter : ∀ h, MoveMinimal raw (position s.center) h →
      position s.right - position s.center ≤ 4*h) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨_,_,rad,hscan,hlen⟩ :=
    PalPeg.CanonicalFallbackInput.counters centre place entry q first hI hrun hm hr
  obtain ⟨h,hminimal⟩ := sem_moveData hsem hz
  have hrad : rad = position s.right - position s.center := by
    rw [hscan.rightPos]
    omega
  apply PalPeg.CanonicalFallbackInput.move_of_activeBound
    (c := c) hscan hcan hlen (scan_radius_lt hscan) hminimal
  · rw [hrad]
    exact hquarter h hminimal
  · rfl

theorem move_of_preShift_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {z : ChainVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k
      ⟨c₀,r₀⟩ ⟨c,s⟩)
    (hlower : s.lower = reset) (hm : c.mode = .scan) (hr : c.replaying = false)
    (hcan : canRight s.right)
    (hsearch : searchEffect (PofC centre place entry raw) false s vq)
    (hchain : chainAt false (decide (vq.search.mode = .found))
      (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre s)
      ((PofC centre place entry raw).place s) s.center s.radius s.chain z)
    (hpre : PreShift z)
    (hquarter : ∀ h, MoveMinimal raw (position s.center) h →
      position s.right - position s.center ≤ 4*h) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun
  obtain ⟨rad,hscan⟩ := hp.pack.scanGeom hm hr
  have hright : position s.right = position s.center + rad := by
    simpa using hscan.rightPos
  have hminMode := budgetMinimal_packed centre place entry q first hP hI hrun hlower
  have hscanMin : ScanMinimal raw s := by simpa [ModeMinimal,hm] using hminMode
  let t : GalilVM := {s with chain := z}
  have htmin : ScanMinimal raw t := scanMinimal_chainAt_false hscanMin
    (hp.win hP).coupled.block
    (fun hi hf => PalPeg.CanonicalSearchHistory.birthMinimals_packed centre place entry q first
      hP hI hrun hm hi hsearch (of_decide_eq_true hf)
        (by rw [searchEffect_lower_eq hsearch,hlower]))
    (by simpa [t] using hchain) (by simp [t]) (by simp [t])
      (by show position s.center ≤ position s.right; rw [hright]; omega)
  have hsem : Sem raw (position s.center) z := by
    have hs := scanMinimal_preShift_sem htmin (by simpa [t] using hpre)
    simpa [t] using hs
  exact move_of_live_sem_packed centre place entry q first hI hrun hm hr hcan
    hsem (by intro hz; rw [hz] at hpre; cases hpre) hquarter

theorem shiftPeriodMinimal_at {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    {k : ℕ} {c : Control} {s s' : GalilVM} {vq : SearchVM} {z : ChainVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k
      ⟨c₀,r₀⟩ ⟨c,s⟩)
    (hlower : s.lower = reset) (hm : c.mode = .scan) (hr : c.replaying = false)
    (hcan : canRight s.right)
    (hsearch : searchEffect (PofC centre place entry raw) false s vq)
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s')
    (hmt : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s')
    (hchain : chainAt false (decide (vq.search.mode = .found))
      (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre s)
      ((PofC centre place entry raw).place s) s.center s.radius s.chain z)
    (hg : shiftGuardVM s') {wg : GalilScaffoldChainWatch.State} (hwg : z = .watch wg) :
    ∀ p, 0 < p → p < 2 * periodLength wg →
      ¬ HasPeriod (Span raw (position s.center) (position s.right-position s.center)) p := by
  have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun
  obtain ⟨rad,hscan⟩ := hp.pack.scanGeom hm hr
  have hpos : position s.right = position s.center + rad := hscan.rightPos
  have hminMode := budgetMinimal_packed centre place entry q first hP hI hrun hlower
  have hscanMin : ScanMinimal raw s := by simpa [ModeMinimal,hm] using hminMode
  let t : GalilVM := {s with chain := z}
  have htmin : ScanMinimal raw t := scanMinimal_chainAt_false hscanMin
    (hp.win hP).coupled.block
    (fun hi hf => PalPeg.CanonicalSearchHistory.birthMinimals_packed centre place entry q first
      hP hI hrun hm hi hsearch (of_decide_eq_true hf)
        (by rw [searchEffect_lower_eq hsearch,hlower]))
    (by simpa [t] using hchain) (by simp [t]) (by simp [t])
      (by rw [hpos]; omega)
  have htwatch : WatchMinimal raw (position s.center) rad wg := by
    simp only [t,hwg,ScanMinimal] at htmin
    obtain ⟨j,hj,hjmin⟩ := htmin
    have hj' : position s.right = position s.center + j := by simpa [t] using hj
    have : j = rad := by omega
    simpa [this] using hjmin
  have hsChain : s'.chain = .watch wg := by
    obtain ⟨vs,vq',a,hvl,hvr,hiff,hse,hca,heq⟩ := hcmp
    have ha : a = false := by
      cases a with
      | false => rfl
      | true =>
        exfalso
        apply hmt
        have heqRead := hiff.mp rfl
        show read s'.left = read s'.right
        rw [heq,afterBirth_left,afterBirth_right]
        simp only [Bool.true_eq,if_pos]
        change read vs.left = read vs.right at heqRead
        simpa [afterCompare,searchLens,scanLens] using heqRead
    subst a
    have hvq : vq' = vq := by
      have h1 := PalPeg.GalilTickFair.searchEffect_unique hsearch hse
      exact h1.symm
    subst vq'
    have hz : vs.chain = z := PalPeg.GalilTickDet.chainAt_unique hca hchain
    rw [heq,afterBirth_chain]
    simpa [afterMismatch,searchLens,scanLens,hz,hwg]
  have hledger := freshLedger_of_windowRunPack centre place entry q first hp.pack (hp.win hP)
    hcan ⟨hm,hr⟩ hcmp hmt hg wg hsChain rad hscan
  obtain ⟨_,hleft,hh0,_,hcaught⟩ := hledger
  have hfourZ := four_of_guard centre place entry q first (hp.win hP).coupled
    ⟨hm,hr⟩ hcmp hmt hg hsChain
  have hfour : 4 * periodLength wg ≤ rad := by
    obtain ⟨R,hRR,hR⟩ := (hp.win hP).radiusScan hm
    change position s.right = position s.center + R at hR
    have hradR : rad = R := by omega
    have hv : value s.radius = (R : ℤ) := hRR.2
    rw [hv] at hfourZ
    omega
  have hperiodOn := periodOn_right_succ hscan.palindrome (by omega) hleft hcaught
  have hsp := shiftPal_of_windowRunPack centre place entry q first hp.pack (hp.win hP)
    hcan ⟨hm,hr⟩
  obtain ⟨_,_,hpal1⟩ := hsp s' hcmp hmt wg hsChain hg rad hscan
  have hperiod : HasPeriod (Span raw (position s.center) rad) (2*periodLength wg) :=
    hasPeriod_span_of_next hh0 (by omega) hscan.palindrome hpal1 hperiodOn
  simpa [hscan.rightPos] using
    watchMinimal_no_short htwatch (scan_radius_lt hscan) hscan.palindrome hfour hperiod

/-- The exact leaf consumed by `OracleReady`. -/
theorem shiftPeriodMinimal_packed {raw : List (Fin 2)}
    (hP : Decodes (PofC centre place entry raw)) :
    ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (c : Control) (s : GalilVM)
      (vq : SearchVM) (z : ChainVM) (u : GalilVM) (m : ℕ), 1 ≤ m → m ≤ raw.length →
      InvLPS (PofC centre place entry raw) q first raw c₀ r₀ →
      PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c,s⟩ →
      s.lower = reset → c.mode = .scan → c.replaying = false → c.clock = 1 →
      position s.right + 1 ≤ 2*m-1 → MInv raw c s →
      read (left s.left) ≠ read (right s.right) →
      searchEffect (PofC centre place entry raw) false s vq →
      chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
        ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
        s.center s.radius s.chain z →
      (PofC centre place entry raw).shiftGuard
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)) →
      (PofC centre place entry raw).beginShift
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)) u →
      Tick (galilFrameS (PofC centre place entry raw) q first) 2048 ⟨c,s⟩
        ⟨{c with clock := 2048, mode := .shift},u⟩ →
      ∀ wg : GalilScaffoldChainWatch.State, z = .watch wg →
        ∀ p, 0 < p → p < 2*periodLength wg →
          ¬ HasPeriod (Span raw (position s.center) (position s.right-position s.center)) p := by
  intro c₀ r₀ k c s vq z u m hm1 hmle hI hrun hlower hm hr hc hbound hM
    hmis hsearch hchain hg hb htick wg hwg
  let vs : ScanVM := ⟨left s.left,right s.right,z⟩
  let s' := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
    (afterMismatch s vs vq)
  have hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s' := by
    refine ⟨vs,vq,false,rfl,rfl,?_,hsearch,?_,rfl⟩
    · constructor
      · intro h; cases h
      · intro hmatch
        exfalso
        apply hmis
        exact hmatch
    · simpa [vs] using hchain
  have hmt : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s' := by
    change read s'.left ≠ read s'.right
    intro he
    apply hmis
    simpa [s',vs,afterBirth_left,afterBirth_right,afterMismatch,searchLens,scanLens] using he
  have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun
  obtain ⟨rad,hscan⟩ := hp.pack.scanGeom hm hr
  have hcan : canRight s.right := canRight_of_bound _ raw hscan.rightRep hscan.rightPresent (by
    simp only [encoded,pairs_length,List.length_append,List.length_singleton]
    omega)
  exact shiftPeriodMinimal_at centre place entry q first hP hI hrun hlower hm hr hcan
    hsearch hcmp hmt (by simpa [vs] using hchain)
      (by simpa [s',vs,PofC,sharedC,galilShared] using hg) hwg

end PalPeg.CanonicalChainMinimal
