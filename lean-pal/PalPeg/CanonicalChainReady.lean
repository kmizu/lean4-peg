import PalPeg.WindowPack
import PalPeg.CloseoutCheckW
import PalPeg.GalilTickFun

/-! # Chain enabling from the window already carried by the packed run

The only additional datum is the unary answer still being copied.  The
window supplies verifier representation and lag, and the coupled block
supplies every period symbol.  No completed trace is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PalPeg.CanonicalChainReady
open PalPeg GalilScaffoldTop GalilScaffoldController GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open GalilBranchInvariants GalilReplayGeneral2 WindowRun WindowInv ShiftPalAlongTrace

/-- The only enabling datum not already in `WindowRunPack`. -/
def CopyReady : ChainVM → Prop
  | .copy t h p v _ _ _ => ∃ n, CopyInv t h p v n
  | _ => True

/-- The answer and source prefix advance in lockstep. -/
theorem copyReady_step {x y : ChainVM} (hx : CopyReady x) (ht : ChainStep x y) :
    CopyReady y := by
  cases ht with
  | copyBit t hh p v lag margin ver a hone _ _ =>
    obtain ⟨n,hn⟩ := hx
    cases n with
    | zero => have := answerAhead_zero hn.1; omega
    | succ n => exact ⟨n,copyInv_step hn a⟩
  | _ => trivial

theorem copyReady_matched {x y : ChainVM} (hx : CopyReady x) (ht : ChainMatched x y) :
    CopyReady y := by
  cases ht with
  | copy => exact hx
  | _ => trivial

theorem copyReady_chainTick {a : Bool} {x y : ChainVM}
    (hx : CopyReady x) (ht : ChainTick a x y) : CopyReady y := by
  obtain ⟨z,hz,ha⟩ := ht
  have hh := copyReady_step hx hz
  cases a with
  | false => simp only [Bool.false_eq_true,reduceIte] at ha; rw [ha]; exact hh
  | true => exact copyReady_matched hh ha

/-- At a birth the only new requirement is the DP answer's copy invariant. -/
theorem copyReady_chainAt {a found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PlaceHead} {rad : Counter} {x y : ChainVM}
    (hx : CopyReady x)
    (hbirth : x = .idle → found = true → ∃ n, CopyInv ans reset wk (GalilScaffoldChainPeriod.start cc) n)
    (ht : chainAt a found ans cc wk ver rad x y) : CopyReady y := by
  rcases ht with ⟨_,ht⟩ | ⟨_,_,hy⟩ | ⟨hi,hf,hy⟩
  · exact copyReady_chainTick hx ht
  · rw [hy]; trivial
  · have hb : CopyReady (chainStart ans cc wk ver rad) := hbirth hi hf
    cases a with
    | false => simp only [Bool.false_eq_true,reduceIte] at hy; rw [hy]; exact hb
    | true => exact copyReady_matched hb hy

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The DP datum needed only when an idle search actually reports found. -/
def BirthCopy (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  ∀ a vq, s.chain = .idle → searchEffect (PofC centre place entry raw) a s vq →
    vq.search.mode = .found → ∃ n,
      CopyInv (vq.dp.config.tapes 11) reset ((PofC centre place entry raw).place s)
        (GalilScaffoldChainPeriod.start ((PofC centre place entry raw).centre s)) n

private theorem copyReady_background {raw : List (Fin 2)} {s t : GalilVM}
    (hb : (galilFrameS (PofC centre place entry raw) q first).background s t)
    (hx : CopyReady s.chain) (hbirth : BirthCopy centre place entry raw s) : CopyReady t.chain := by
  obtain ⟨_,_,hs,hch,_⟩ := hb
  exact copyReady_chainAt hx
    (fun hi hf => hbirth false (searchLens.get t) hi hs (of_decide_eq_true hf)) hch

private theorem copyReady_compare {raw : List (Fin 2)} {s t : GalilVM}
    (hc : (galilFrameS (PofC centre place entry raw) q first).compare s t)
    (hx : CopyReady s.chain) (hbirth : BirthCopy centre place entry raw s) : CopyReady t.chain := by
  obtain ⟨vs,vq,a,_,_,_,hs,hch,heq⟩ := hc
  have hz : CopyReady vs.chain := copyReady_chainAt hx
    (fun hi hf => hbirth a vq hi hs (of_decide_eq_true hf)) hch
  rw [heq,afterBirth_chain]
  cases a <;> exact hz

/-- Copy validity is transported through every controller phase. -/
theorem copyReady_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hx : CopyReady x.vm.chain)
    (hbirth : x.ctl.mode = .scan → BirthCopy centre place entry raw x.vm) :
    CopyReady y.vm.chain := by
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    rw [hch]; trivial
  | scan_wait c s t hm _ hb => exact copyReady_background centre place entry q first hb hx (hbirth hm)
  | scan_count c s t hm _ _ hb => exact copyReady_background centre place entry q first hb hx (hbirth hm)
  | scan_match c s t u o hm _ _ hc _ hp _ =>
    have he : u.chain = t.chain := by rw [hp]; split <;> rfl
    rw [he]
    exact copyReady_compare centre place entry q first hc hx (hbirth hm)
  | scan_shift c s t u hm _ _ _ _ _ _ hb =>
    obtain ⟨v,_,rfl⟩ := hb; trivial
  | scan_fallback c s t u hm _ _ _ _ _ _ hb =>
    obtain ⟨p,rfl,_⟩ := hb; trivial
  | shift_one c s t hm _ ho =>
    obtain ⟨_,_,_,wv,hw,hget⟩ := ho.1
    have hset := ho.2
    rw [hget] at hset
    rw [hset]; trivial
  | shift_done => exact hx
  | replayStart c s t o hm hr _ _ =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    rw [hch]; trivial
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr; trivial
  | copy_one _ _ _ _ _ h | copy_done _ _ _ _ _ h
  | home_start _ _ _ _ _ h | home_step _ _ _ _ _ h
  | fpp_slice _ _ _ _ h | fpp_done _ _ _ _ h
  | markEnd_step _ _ _ _ _ h | markEnd_found _ _ _ _ _ h
  | choose_select _ _ _ _ _ _ h | choose_step _ _ _ _ _ h
  | rewind_done _ _ _ _ _ h | rewind_one _ _ _ _ _ _ h
  | rewind_pair _ _ _ _ _ _ h => rw [h.2]; exact hx

/-- The finite prefix transports the birth datum; no full trace is assumed. -/
theorem copyReady_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hI : PalPeg.GalilInvPlus3.InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hbirth : ∀ k y,
      PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y →
      y.ctl.mode = .scan → BirthCopy centre place entry raw y.vm)
    {k : ℕ} {y : State GalilVM}
    (hr : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y) :
    CopyReady y.vm.chain := by
  obtain ⟨g,h0,hk,ht,hcan,hpk⟩ := hr
  have hi : r₀.chain = .idle := by
    rcases hI.1.1.1.1.1 with h | ⟨_,h⟩
    · obtain ⟨_,_,h⟩ := h.rest; exact h.1
    · exact h.chainIdle
  have hprefix : ∀ i, i ≤ k →
      PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw i ⟨c₀,r₀⟩ (g i) := by
    intro i hi
    exact ⟨g,h0,rfl,⟨fun j hj => ht.tick j (by omega),fun j hj => ht.good j (by omega)⟩,
      fun j hj => hcan j (by omega),fun j hj => hpk j (by omega)⟩
  have hcopy : ∀ i, i ≤ k → CopyReady (g i).vm.chain := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; change CopyReady r₀.chain; rw [hi]; trivial
    | succ i ih =>
      intro hh
      exact copyReady_tick centre place entry q first (ht.tick i (by omega))
        (ih (by omega)) (hbirth i (g i) (hprefix i (by omega)))
  simpa only [hk] using hcopy k le_rfl

/-- A represented verifier no further right than the scan head can advance. -/
private theorem verifier_canRight {raw : List (Fin 2)} {ver : PlaceHead} {R : ℕ}
    (hrep : GalilScaffoldInputTrace.Represents ver.head raw) (hpres : ver.head.focus ≠ none)
    (hle : position ver ≤ R) (hbound : R + 1 < (encoded raw).length) : canRight ver :=
  GalilScaffoldChainInputSupply.canRight_of_bound ver raw hrep hpres (by omega)

/-- All back/watch branches are enabled by the existing packed window. -/
theorem of_window {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hwin : PalPeg.WindowPack.WindowRunPack raw c s)
    (hcopy : CopyReady s.chain)
    (hbound : position s.right + 1 < (encoded raw).length) :
    PalPeg.GalilTickFun.ChainReady s.chain := by
  obtain ⟨cen,cc,_,hinv,_,_,_⟩ := hwin.window
  have hblock := hwin.coupled.block
  cases he : s.chain with
  | idle => trivial
  | broken w => trivial
  | copy t h p v lag margin ver =>
    rw [he] at hcopy
    change ∃ n, CopyInv t h p v n
    exact hcopy
  | back v h lag margin ver =>
    rw [he] at hinv hblock
    obtain ⟨hver,hlag,_,_,_⟩ := hinv
    have hlag' := hlag.2
    change position ver + lag.pos.length = position s.right at hlag'
    intro hf _
    exact ⟨verifier_canRight hver.1 hver.2.1 (by
      change position ver ≤ position s.right
      omega) hbound,
      onBlock_moveRight hblock (isFirst_isLast hf)⟩
  | watch w =>
    rw [he] at hinv hblock
    obtain ⟨b,xs,hlag,hletters,hcore⟩ := hinv
    have hcan : canRight w.machine.verifier :=
      verifier_canRight hcore.2.1 hcore.2.2.1 (by have := hlag.2; omega) hbound
    refine ⟨fun _ => ⟨hcan,onBlock_symbol hcore.1⟩,hblock,?_⟩
    intro m hi
    cases hi with
    | idle => exact hcan
    | take hp hg =>
      have hpos : 0 < w.lag.pos.length := by
        cases h : w.lag.pos with
        | nil => simp [h, GalilScaffoldCounter.positive] at hp
        | cons a as => simp [h]
      have hpv := represented_position _ raw hcore.2.1 hcore.2.2.1
      have hstep := right_position w.machine.verifier hg.1 hpv.1
      exact verifier_canRight
        (right_word _ raw hcore.2.1 hg.1)
        (right_present _ raw hcore.2.1 hcore.2.2.1 hg.1)
        (by change position (right w.machine.verifier) ≤ position s.right
            rw [hstep]; have := hlag.2; omega) hbound

#print axioms of_window
end PalPeg.CanonicalChainReady
