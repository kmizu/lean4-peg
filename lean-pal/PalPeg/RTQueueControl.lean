import PalPeg.RTQueueDispatch
import PalPeg.ProgLangSum

/-! A private stationary cell stores the finite phase and physical role map.
The alphabet is parameterized by an injective encoding of this finite set.
No unbounded queue value is inspected by the program. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RTQueueControl

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg PalPeg.RTQueueDispatch

structure Mode where
  phase : Phase
  roles : Role → Role
  deriving DecidableEq, Fintype

variable {k : ℕ} {Terminal : Type}

def IM (Terminal : Type) (code : Mode → Fin k) : Interp Terminal Mode Mode (Fin k) 1 where
  actOf m _ _ := fun _ => (code m, .stay)
  condOf m σ := decide (σ 0 = code m)

noncomputable def IC (Terminal : Type) (code : Mode → Fin k) :=
  Interp.sum (IQ (k := k) Terminal) (IM Terminal code)

abbrev CP (k : ℕ) := Prog (ActQ k ⊕ Mode) (CondQ k ⊕ Mode)

def cell (code : Mode → Fin k) (m : Mode) : Fin 1 → STape (Fin k) :=
  fun _ => ⟨[], code m, []⟩

def tapes (code : Mode → Fin k) (qt : QT k) (m : Mode) :=
  Fin.append (TSQ qt) (cell code m)

def liftQ (p : Prog (ActQ k) (CondQ k)) : CP k := Prog.map Sum.inl Sum.inl p

def storeMode (m : Mode) : CP k := .act (.inr m)

def Runs (Terminal : Type) (code : Mode → Fin k) (blank : Fin k) (p : CP k)
    (qt : QT k) (m : Mode) (n : ℕ) (qt' : QT k) (m' : Mode) : Prop :=
  ∃ tr, Exec (IC Terminal code) blank p (tapes code qt m) tr ∧
    tr.length = n ∧ applyTrace blank (tapes code qt m) tr = tapes code qt' m'

theorem runs_lift {code : Mode → Fin k} {blank : Fin k}
    {p : Prog (ActQ k) (CondQ k)} {qt : QT k} {m : Mode} {tr : List (Act k)}
    (h : ExecQ Terminal blank p qt tr) :
    Runs Terminal code blank (liftQ p) qt m tr.length (run blank qt tr) m := by
  have he := exec_sum_inl (I2 := IM Terminal code) h (tapes code qt m)
  rw [tapes, extend_castAdd_append] at he
  refine ⟨_, he, ?_, ?_⟩
  · simp [avecsQ_length]
  · have hh := applyTrace_extend (Fin.castAddEmb 1) blank
      (tapes code qt m) (avecsQ blank tr qt) (TSQ qt)
    simp only [tapes, extend_castAdd_append, applyTrace_avecsQ] at hh
    exact hh

theorem runs_store {code : Mode → Fin k} {blank : Fin k} (qt : QT k) (m m' : Mode) :
    Runs Terminal code blank (storeMode m') qt m 1 qt m' := by
  have he := exec_act (I := IM Terminal code) (blank := blank)
    (fun _ _ _ => rfl) m' (cell code m)
  have ht := exec_sum_inr (I1 := IQ (k := k) Terminal) he (tapes code qt m)
  rw [tapes, extend_natAdd_append] at ht
  refine ⟨_, ht, rfl, ?_⟩
  have hc : applyTrace blank (cell code m) [actVec (IM Terminal code) m' (cell code m)]
      = cell code m' := by rfl
  have hh := applyTrace_extend (Fin.natAddEmb 10) blank (tapes code qt m)
    [actVec (IM Terminal code) m' (cell code m)] (cell code m)
  simp only [tapes, extend_natAdd_append, hc] at hh
  exact hh

theorem runs_seq {code : Mode → Fin k} {blank : Fin k} {p q : CP k}
    {qt qt' qt'' : QT k} {m m' m'' : Mode} {n n' : ℕ}
    (hp : Runs Terminal code blank p qt m n qt' m')
    (hq : Runs Terminal code blank q qt' m' n' qt'' m'') :
    Runs Terminal code blank (.seq p q) qt m (n + n') qt'' m'' := by
  obtain ⟨a, ha, hna, hta⟩ := hp
  obtain ⟨b, hb, hnb, htb⟩ := hq
  refine ⟨a ++ b, exec_seq ha (hta ▸ hb), by simp [hna, hnb], ?_⟩
  rw [applyTrace_append, hta, htb]

def selectAux (body : Mode → CP k) : List Mode → CP k
  | [] => .skip
  | m :: ms => .ite (.inr m) (body m) (selectAux body ms)

noncomputable def select (body : Mode → CP k) : CP k :=
  selectAux body Finset.univ.toList

theorem runs_selectAux {code : Mode → Fin k} (hc : Function.Injective code)
    {blank : Fin k} {body : Mode → CP k} {qt qt' : QT k} {m m' : Mode} {n : ℕ}
    (ms : List Mode) (hm : m ∈ ms)
    (h : Runs Terminal code blank (body m) qt m n qt' m') :
    Runs Terminal code blank (selectAux body ms) qt m n qt' m' := by
  induction ms with
  | nil => simp at hm
  | cons a ms ih =>
      by_cases ha : m = a
      · subst a
        obtain ⟨tr, ht, hn, hr⟩ := h
        refine ⟨tr, exec_ite_pos ?_ ht, hn, hr⟩
        change decide (code m = code m) = true
        simp
      · have hmem : m ∈ ms := (List.mem_cons.mp hm).resolve_left ha
        obtain ⟨tr, ht, hn, hr⟩ := ih hmem
        refine ⟨tr, exec_ite_neg ?_ ht, hn, hr⟩
        change decide (code m = code a) = false
        exact decide_eq_false (fun e => ha (hc e))

theorem runs_select {code : Mode → Fin k} (hc : Function.Injective code)
    {blank : Fin k} {body : Mode → CP k} {qt qt' : QT k} {m m' : Mode} {n : ℕ}
    (h : Runs Terminal code blank (body m) qt m n qt' m') :
    Runs Terminal code blank (select body) qt m n qt' m' :=
  runs_selectAux hc _ (by simp) h

def caseAux (ρ : Role) (body : Fin k → CP k) : List (Fin k) → CP k
  | [] => .skip
  | a :: as => .ite (.inl (ρ, a)) (body a) (caseAux ρ body as)

def caseRead (ρ : Role) (body : Fin k → CP k) : CP k :=
  caseAux ρ body (List.finRange k)

theorem runs_caseAux {code : Mode → Fin k} {blank : Fin k} {ρ : Role}
    {body : Fin k → CP k} {qt qt' : QT k} {m m' : Mode} {n : ℕ}
    (as : List (Fin k)) (hm : (qt ρ).focus ∈ as)
    (h : Runs Terminal code blank (body (qt ρ).focus) qt m n qt' m') :
    Runs Terminal code blank (caseAux ρ body as) qt m n qt' m' := by
  induction as with
  | nil => simp at hm
  | cons a as ih =>
      by_cases ha : (qt ρ).focus = a
      · obtain ⟨tr, ht, hn, hr⟩ := h
        refine ⟨tr, exec_ite_pos ?_ (ha ▸ ht), hn, hr⟩
        simp only [IC, Interp.sum, Interp.transport, IQ, tapes, Fin.castAddEmb_apply,
          Fin.append_left, TSQ_focus, role_ridx, ha, decide_true]
      · obtain ⟨tr, ht, hn, hr⟩ := ih ((List.mem_cons.mp hm).resolve_left ha)
        refine ⟨tr, exec_ite_neg ?_ ht, hn, hr⟩
        simp only [IC, Interp.sum, Interp.transport, IQ, tapes, Fin.castAddEmb_apply,
          Fin.append_left, TSQ_focus, role_ridx, ha, decide_false]

theorem runs_caseRead {code : Mode → Fin k} {blank : Fin k} {ρ : Role}
    {body : Fin k → CP k} {qt qt' : QT k} {m m' : Mode} {n : ℕ}
    (h : Runs Terminal code blank (body (qt ρ).focus) qt m n qt' m') :
    Runs Terminal code blank (caseRead ρ body) qt m n qt' m' :=
  runs_caseAux _ (List.mem_finRange _) h

def probeC (blank : Fin k) (ρ : Role) (body : Fin k → CP k) : CP k :=
  .seq (liftQ (.act (ρ, blank, .left)))
    (caseRead ρ fun a => .seq (liftQ (.act (ρ, a, .right))) (body a))

theorem runs_probeC {code : Mode → Fin k} {blank mark : Fin k} {ρ : Role}
    {body : Fin k → CP k} {qt qt' : QT k} {m m' : Mode} {n : ℕ} {l : List (Fin k)}
    (hs : SStack blank mark (qt ρ) l)
    (hb : Runs Terminal code blank (body (l.head?.getD mark)) qt m n qt' m') :
    Runs Terminal code blank (probeC blank ρ body) qt m (2 + n) qt' m' := by
  let qt1 := run blank qt [⟨ρ, blank, .left⟩]
  have hr : (qt1 ρ).focus = l.head?.getD mark := by
    simp only [qt1, run_cons, run_nil, act_apply]
    exact sstack_probe hs
  have hrestore : run blank qt1 [⟨ρ, l.head?.getD mark, .right⟩] = qt := by
    exact probePrefix_restore hs
  have h1 := runs_lift (code := code) (m := m)
    (execQ_act (Terminal := Terminal) (blank := blank) ρ blank .left qt)
  have h2 := runs_lift (code := code) (m := m)
    (execQ_act (Terminal := Terminal) (blank := blank) ρ (l.head?.getD mark) .right qt1)
  rw [hrestore] at h2
  have htail := runs_seq h2 hb
  have hcase : Runs Terminal code blank
      (caseRead ρ fun a => .seq (liftQ (.act (ρ, a, .right))) (body a))
      qt1 m (1 + n) qt' m' := by
    apply runs_caseRead
    rw [hr]
    exact htail
  have hh := runs_seq h1 hcase
  simpa only [probeC, List.length_singleton, ← Nat.add_assoc] using hh

/-- One queue rotation branch followed by its new finite phase. -/
def finishBranch (blank : Fin k) (m : Mode) (sh : EShape) : CP k :=
  .seq (liftQ (execStepProg blank m.roles sh))
    (storeMode { m with phase := phaseAfter m.phase sh })

def rotationBody (blank mark : Fin k) (m : Mode) : CP k :=
  match m.phase with
  | .idle => finishBranch blank m .nil
  | .done => finishBranch blank m .nil
  | .reversing => probeC blank (m.roles .f) fun a =>
      finishBranch blank m (if a = mark then .revNil else .revCons)
  | .appending => probeC blank (m.roles .ok) fun a =>
      finishBranch blank m (if a = mark then .appZ else .appS)

/-- The public program has no phase or role-map argument: it reads the cell. -/
noncomputable def rotation (blank mark : Fin k) : CP k := select (rotationBody blank mark)

theorem runs_finishBranch {code : Mode → Fin k} {blank mark : Fin k}
    {qt : QT k} {m : Mode} {s : RotationState (Fin k)}
    (hπ : Function.Injective m.roles) (hs : SEnc blank mark (qt ∘ m.roles) s)
    (hp : m.phase = phaseOf s) :
    Runs Terminal code blank (finishBranch blank m (eshapeOf s)) qt m
      ((execProg blank s).length + 1) (run blank qt (renameL m.roles (execProg blank s)))
      { m with phase := phaseOf (exec s) } := by
  have h1 := runs_lift (code := code) (m := m) (execQ_execStep (Terminal := Terminal) hπ hs)
  have h2 := runs_store (Terminal := Terminal) (code := code) (blank := blank)
    (run blank qt (renameL m.roles (execProg blank s))) m
    { m with phase := phaseAfter m.phase (eshapeOf s) }
  have hh := runs_seq h1 h2
  simpa only [finishBranch, renameL_length, hp, phaseAfter_eq] using hh

theorem rotationBody_runs {code : Mode → Fin k} {blank mark : Fin k}
    {qt : QT k} {m : Mode} {s : RotationState (Fin k)} {front : List (Fin k)}
    (hπ : Function.Injective m.roles) (hmb : mark ≠ blank)
    (hi : SInv front s) (hs : SEnc blank mark (qt ∘ m.roles) s)
    (hm : mark ∉ stF s) (hp : m.phase = phaseOf s) :
    ∃ n, n ≤ 12 ∧ Runs Terminal code blank (rotationBody blank mark m) qt m n
      (run blank qt (renameL m.roles (execProg blank s)))
      { m with phase := phaseOf (exec s) } := by
  have he := runs_finishBranch (Terminal := Terminal) (code := code) hπ hs hp
  have hshape := selectShape_eq hi
  have hlen := execProg_length blank s
  cases s with
  | idle =>
      refine ⟨1, by omega, ?_⟩
      simpa only [rotationBody, hp, phaseOf, eshapeOf, execProg, List.length_nil,
        Nat.zero_add] using he
  | done f =>
      refine ⟨1, by omega, ?_⟩
      simpa only [rotationBody, hp, phaseOf, eshapeOf, execProg, List.length_nil,
        Nat.zero_add] using he
  | reversing ok f fp r rp =>
      have hf : SStack blank mark (qt (m.roles .f)) f := hs.1
      have hr : f.head?.getD mark = mark ↔ f = [] := by
        rw [← sstack_probe hf]
        exact stack_probe_empty_iff hf hm
      simp only [phaseOf, selectShape, stF, decide_eq_true_eq] at hshape
      have hb : Runs Terminal code blank
          (finishBranch blank m (if f.head?.getD mark = mark then .revNil else .revCons))
          qt m ((execProg blank (.reversing ok f fp r rp)).length + 1)
          (run blank qt (renameL m.roles (execProg blank (.reversing ok f fp r rp))))
          { m with phase := phaseOf (exec (.reversing ok f fp r rp)) } := by
        simp only [hr, hshape]
        exact he
      refine ⟨2 + ((execProg blank (.reversing ok f fp r rp)).length + 1), by omega, ?_⟩
      simp only [rotationBody, hp, phaseOf]
      exact runs_probeC (body := fun a =>
        finishBranch blank m (if a = mark then .revNil else .revCons)) hf hb
  | appending ok fp rp =>
      have hg : GCount blank mark (qt (m.roles .ok)) ok := hs.2.2.2.2.2
      have hr : (List.replicate ok blank).head?.getD mark = mark ↔ ok = 0 := by
        rw [← sstack_probe hg]
        exact gcount_isZero_iff hmb hg
      simp only [phaseOf, selectShape, stOk, decide_eq_true_eq] at hshape
      have hb : Runs Terminal code blank
          (finishBranch blank m (if (List.replicate ok blank).head?.getD mark = mark
            then .appZ else .appS)) qt m ((execProg blank (.appending ok fp rp)).length + 1)
          (run blank qt (renameL m.roles (execProg blank (.appending ok fp rp))))
          { m with phase := phaseOf (exec (.appending ok fp rp)) } := by
        simp only [hr, hshape]
        exact he
      refine ⟨2 + ((execProg blank (.appending ok fp rp)).length + 1), by omega, ?_⟩
      simp only [rotationBody, hp, phaseOf]
      exact runs_probeC (body := fun a =>
        finishBranch blank m (if a = mark then .appZ else .appS)) hg hb

/-- A single finite program reads its own mode, executes the appropriate queue
rotation, and persists the resulting phase. The physical role map is preserved. -/
theorem rotation_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {s : RotationState (Fin k)}
    {front : List (Fin k)} (hπ : Function.Injective m.roles) (hmb : mark ≠ blank)
    (hi : SInv front s) (hs : SEnc blank mark (qt ∘ m.roles) s)
    (hm : mark ∉ stF s) (hp : m.phase = phaseOf s) :
    ∃ n, n ≤ 12 ∧ Runs Terminal code blank (rotation blank mark) qt m n
      (run blank qt (renameL m.roles (execProg blank s)))
      { m with phase := phaseOf (exec s) } := by
  obtain ⟨n, hn, he⟩ := rotationBody_runs (Terminal := Terminal) (code := code)
    hπ hmb hi hs hm hp
  exact ⟨n, hn, runs_select hc he⟩

theorem stF_exec_subset (s : RotationState (Fin k)) : stF (exec s) ⊆ stF s := by
  cases s with
  | idle => exact List.Subset.refl _
  | done f => exact List.Subset.refl _
  | reversing ok f fp r rp =>
      cases f with
      | nil => cases r with
        | nil => simp [exec, stF]
        | cons a r => cases r <;> simp [exec, stF]
      | cons a f => cases r <;> simp [exec, stF]
  | appending ok fp rp => cases ok <;> cases fp <;> simp [exec, stF]

def afterInstall (m : Mode) : Mode :=
  if m.phase = .done then ⟨.idle, m.roles ∘ ipRole⟩ else m

def installBody (blank mark : Fin k) (m : Mode) : CP k :=
  if m.phase = .done then
    .seq (liftQ (straight m.roles (installProg blank mark))) (storeMode (afterInstall m))
  else .skip

noncomputable def install (blank mark : Fin k) : CP k := select (installBody blank mark)

theorem runs_skip {code : Mode → Fin k} {blank : Fin k} (qt : QT k) (m : Mode) :
    Runs Terminal code blank .skip qt m 0 qt m :=
  ⟨[], exec_skip _, rfl, rfl⟩

theorem afterInstall_injective (m : Mode) (h : Function.Injective m.roles) :
    Function.Injective (afterInstall m).roles := by
  unfold afterInstall
  split
  · exact h.comp ipRole_injective
  · exact h

theorem install_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {s : RotationState (Fin k)}
    (hπ : Function.Injective m.roles) (hp : m.phase = phaseOf s) :
    ∃ n qt', n ≤ 4 ∧ Runs Terminal code blank (install blank mark)
      qt m n qt' (afterInstall m) ∧
      qt' ∘ (afterInstall m).roles = (installIf blank mark s ⟨qt ∘ m.roles, 0⟩).qt := by
  by_cases hd : m.phase = .done
  · have hs : ∃ f, s = .done f := by
      rw [hp] at hd
      cases s <;> simp only [phaseOf] at hd
      · contradiction
      · contradiction
      · contradiction
      · exact ⟨_, rfl⟩
    obtain ⟨f, rfl⟩ := hs
    let qt' := run blank qt (renameL m.roles (installProg blank mark))
    have h1 := runs_lift (code := code) (m := m)
      (execQ_straight (Terminal := Terminal) (blank := blank)
        m.roles (installProg blank mark) qt)
    have h2 := runs_store (Terminal := Terminal) (code := code) (blank := blank)
      qt' m (afterInstall m)
    refine ⟨4, qt', by omega, runs_select hc ?_, ?_⟩
    · simp only [installBody, hd, ↓reduceIte]
      simpa only [renameL_length, installProg_length] using runs_seq h1 h2
    · simp only [afterInstall, hd, ↓reduceIte, installIf, Run.perm_qt,
        Run.acts_qt, installPerm_eq]
      have hh := run_rename hπ blank (installProg blank mark) qt
      change (qt' ∘ m.roles) ∘ ipRole = _
      rw [hh]
  · have hnd : NotDone s := by
      rw [hp] at hd
      cases s <;> simp_all [phaseOf, NotDone]
    refine ⟨0, qt, by omega, runs_select hc ?_, ?_⟩
    · simp only [installBody, afterInstall, hd, ↓reduceIte]
      exact runs_skip qt m
    · rw [installIf_not_done blank mark s _ hnd]
      simp only [afterInstall, hd, ↓reduceIte]

noncomputable def twiceAndInstall (blank mark : Fin k) : CP k :=
  .seq (rotation blank mark) (.seq (rotation blank mark) (install blank mark))

/-- Two rotations and installation, with no externally supplied branch tags.
The full queue tape invariant is restored and the new role assignment is stored. -/
theorem twiceAndInstall_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hπ : Function.Injective m.roles) (hmb : mark ≠ blank)
    (hi : SInv q.front q.state) (hs : EncodesB blank mark (qt ∘ m.roles) q 0)
    (hm : mark ∉ stF q.state) (hp : m.phase = phaseOf q.state) :
    ∃ n qt' m', n ≤ 28 ∧ Runs Terminal code blank (twiceAndInstall blank mark)
      qt m n qt' m' ∧ Function.Injective m'.roles ∧
      m'.phase = phaseOf (exec2 q).state ∧ Encodes blank mark (qt' ∘ m'.roles) (exec2 q) := by
  let qt1 := run blank qt (renameL m.roles (execProg blank q.state))
  let m1 : Mode := { m with phase := phaseOf (exec q.state) }
  have hq1 : qt1 ∘ m.roles = run blank (qt ∘ m.roles) (execProg blank q.state) :=
    run_rename hπ blank _ qt
  have hs1 : SEnc blank mark (qt1 ∘ m1.roles) (exec q.state) := by
    change SEnc blank mark (qt1 ∘ m.roles) _
    rw [hq1]
    exact exec_enc hs.state
  obtain ⟨n1, hn1, he1⟩ := rotation_runs (Terminal := Terminal) hc hπ hmb hi hs.state hm hp
  have hm1 : mark ∉ stF (exec q.state) := fun h => hm (stF_exec_subset q.state h)
  obtain ⟨n2, hn2, he2⟩ := rotation_runs (Terminal := Terminal) hc
    (m := m1) (qt := qt1) hπ hmb (exec_sinv hi) hs1 hm1 rfl
  let qt2 := run blank qt1 (renameL m.roles (execProg blank (exec q.state)))
  let m2 : Mode := { m with phase := phaseOf (exec (exec q.state)) }
  have hq2 : qt2 ∘ m.roles =
      run blank (run blank (qt ∘ m.roles) (execProg blank q.state))
        (execProg blank (exec q.state)) := by
    change run blank qt1 (renameL m.roles (execProg blank (exec q.state))) ∘ m.roles = _
    rw [run_rename hπ, hq1]
  obtain ⟨n3, qt3, hn3, he3, hq3⟩ := install_runs (Terminal := Terminal) hc
    (m := m2) (qt := qt2) (s := exec (exec q.state)) hπ rfl
  have hfull := runs_seq he1 (runs_seq he2 he3)
  refine ⟨n1 + (n2 + n3), qt3, afterInstall m2, by omega, hfull,
    afterInstall_injective m2 hπ, ?_, ?_⟩
  · cases he : exec (exec q.state) <;> simp [afterInstall, m2, exec2, he, phaseOf]
  · have hh : qt3 ∘ (afterInstall m2).roles =
        (exec2T blank mark q ⟨qt ∘ m.roles, 0⟩).qt := by
      rw [hq3]
      change (installIf blank mark (exec (exec q.state)) ⟨qt2 ∘ m.roles, 0⟩).qt = _
      rw [hq2]
      unfold exec2T
      cases exec (exec q.state) <;> rfl
    rw [hh]
    exact exec2T_encodes hs hi

/-- A sufficiently large finite alphabet always admits the mode encoding. -/
noncomputable def canonicalCode : Mode ↪ Fin (Fintype.card Mode + 2) :=
  (Fintype.equivFin Mode).toEmbedding.trans (Fin.castAddEmb 2)

def startMode (m : Mode) : Mode := ⟨.reversing, m.roles ∘ rsRole⟩

noncomputable def checkBody (blank mark : Fin k) (m : Mode) : CP k :=
  probeC blank (m.roles .dd) fun a =>
    if a = mark then .seq (storeMode (startMode m)) (twiceAndInstall blank mark)
    else twiceAndInstall blank mark

noncomputable def checkQueue (blank mark : Fin k) : CP k := select (checkBody blank mark)

/-- The difference counter itself decides whether to start a rotation. The
new permutation is written before either rotation step reads its mode. -/
theorem checkQueue_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hπ : Function.Injective m.roles) (hmb : mark ≠ blank)
    (hi : SInv q.front q.state) (hs : CEncodes blank mark (qt ∘ m.roles) q)
    (hm : mark ∉ stF q.state) (hmf : mark ∉ q.front) (hp : m.phase = phaseOf q.state)
    (hlf : q.lenf = (frontList q.state q.front).length) (hlr : q.lenr = q.rear.length) :
    ∃ n qt' m', n ≤ 31 ∧ Runs Terminal code blank (checkQueue blank mark)
      qt m n qt' m' ∧ Function.Injective m'.roles ∧
      m'.phase = phaseOf (check q).state ∧ Encodes blank mark (qt' ∘ m'.roles) (check q) := by
  obtain ⟨d, hg, heq, hb⟩ := hs.dd
  have hr : (List.replicate d blank).head?.getD mark = mark ↔ d = 0 := by
    rw [← sstack_probe hg]
    exact gcount_isZero_iff hmb hg
  by_cases hz : d = 0
  · have hidle : q.state = .idle := by
      by_contra hni
      have := hb hni
      omega
    have hrem : rem q.state = 0 := by rw [hidle]; rfl
    have hfl : q.lenf = q.front.length := by rw [hlf, hidle]; rfl
    have hrr : q.lenr = q.lenf + 1 := by omega
    have hsi : SInv (rotQ q).front (rotQ q).state := by
      change SInv q.front (.reversing 0 q.front [] q.rear [])
      exact ⟨Nat.zero_le _, rfl, by simpa using (show q.rear.length = q.front.length + 1 by omega), rfl⟩
    have hrot : EncodesB blank mark (qt ∘ (startMode m).roles) (rotQ q) 0 := by
      have ht : qt ∘ (startMode m).roles = rotStart (qt ∘ m.roles) := by
        rw [rotStart_eq]; rfl
      rw [ht]
      exact rot_enc (hs.weaken (by omega)) hidle (hz ▸ hg) hfl hrr
    obtain ⟨n, qt', m', hn, ht, hj, hp', henc⟩ := twiceAndInstall_runs
      (Terminal := Terminal) hc (m := startMode m) (hπ.comp rsRole_injective)
      hmb hsi hrot hmf rfl
    have hstore := runs_store (Terminal := Terminal) (code := code) (blank := blank)
      qt m (startMode m)
    have hbody := runs_seq hstore ht
    have hresult : Runs Terminal code blank (checkBody blank mark m)
        qt m (2 + (1 + n)) qt' m' := by
      unfold checkBody
      apply runs_probeC (qt := qt) (ρ := m.roles .dd) (l := List.replicate d blank) hg
      rw [if_pos (hr.mpr hz)]
      exact hbody
    have hcheck : check q = exec2 (rotQ q) := by
      unfold check rotQ
      rw [if_neg (by omega)]
    refine ⟨2 + (1 + n), qt', m', by omega, runs_select hc hresult, hj, ?_, ?_⟩
    · rw [hcheck]; exact hp'
    · rw [hcheck]; exact henc
  · obtain ⟨n, qt', m', hn, ht, hj, hp', henc⟩ := twiceAndInstall_runs
      (Terminal := Terminal) hc hπ hmb hi (hs.weaken (by omega)) hm hp
    have hresult : Runs Terminal code blank (checkBody blank mark m)
        qt m (2 + n) qt' m' := by
      unfold checkBody
      apply runs_probeC (qt := qt) (ρ := m.roles .dd) (l := List.replicate d blank) hg
      rw [if_neg (fun h => hz (hr.mp h))]
      exact ht
    have hcheck : check q = exec2 q := by
      unfold check
      rw [if_pos (by omega)]
    refine ⟨2 + n, qt', m', by omega, runs_select hc hresult, hj, ?_, ?_⟩
    · rw [hcheck]; exact hp'
    · rw [hcheck]; exact henc

def snocPrefix (blank a : Fin k) : List (Act k) :=
  [⟨.rear, a, .right⟩, ⟨.dd, blank, .left⟩, ⟨.dd, blank, .stay⟩]

noncomputable def snocBody (blank mark a : Fin k) (m : Mode) : CP k :=
  .seq (liftQ (straight m.roles (snocPrefix blank a))) (checkQueue blank mark)

noncomputable def enqueue (blank mark a : Fin k) : CP k := select (snocBody blank mark a)

/-- Enqueue uses a symbol from a finite alphabet, not the abstract queue or its
branch tags. It preserves the queue encoding in at most 34 tape actions. -/
theorem enqueue_runs {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark a : Fin k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hπ : Function.Injective m.roles) (hmb : mark ≠ blank)
    (hq : Inv q) (hs : Encodes blank mark (qt ∘ m.roles) q)
    (hm : mark ∉ stF q.state) (hmf : mark ∉ q.front) (hp : m.phase = phaseOf q.state) :
    ∃ n qt' m', n ≤ 34 ∧ Runs Terminal code blank (enqueue blank mark a)
      qt m n qt' m' ∧ Function.Injective m'.roles ∧
      m'.phase = phaseOf (snoc q a).state ∧ Encodes blank mark (qt' ∘ m'.roles) (snoc q a) := by
  let q1 : Queue (Fin k) := { q with lenr := q.lenr + 1, rear := a :: q.rear }
  let qt1 := run blank qt (renameL m.roles (snocPrefix blank a))
  have hqt : qt1 ∘ m.roles = run blank (qt ∘ m.roles) (snocPrefix blank a) :=
    run_rename hπ blank _ qt
  obtain ⟨d, hg, heq, hb⟩ := hs.dd
  have hd := dd_pos hq heq hb
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hs1 : CEncodes blank mark (qt1 ∘ m.roles) q1 := by
    rw [hqt]
    refine ⟨hs.front, hs.fdup, sstack_push hs.rear a, hs.state,
      ⟨d, gcount_dec hg, ?_, ?_⟩⟩
    · change d + rem q.state + (q.lenr + 1) = q.lenf + 1
      omega
    · intro hni
      have := hb hni
      omega
  have hlr : q1.lenr = q1.rear.length := by
    change q.lenr + 1 = (a :: q.rear).length
    simp [hq.lenr_eq]
  obtain ⟨n, qt', m', hn, ht, hj, hp', he⟩ := checkQueue_runs
    (Terminal := Terminal) hc (qt := qt1) (q := q1) hπ hmb hq.sinv hs1 hm hmf hp
    hq.lenf_eq hlr
  have hprefix := runs_lift (code := code) (m := m)
    (execQ_straight (Terminal := Terminal) (blank := blank) m.roles (snocPrefix blank a) qt)
  have hfull : Runs Terminal code blank (snocBody blank mark a m) qt m (3 + n) qt' m' := by
    simpa only [snocBody, renameL_length, snocPrefix, List.length_cons, List.length_nil] using
      runs_seq hprefix ht
  exact ⟨3 + n, qt', m', by omega, runs_select hc hfull, hj, hp', he⟩

/-- info: 'PalPeg.RTQueueControl.enqueue_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms enqueue_runs

/-- info: 'PalPeg.RTQueueControl.checkQueue_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkQueue_runs

/-- info: 'PalPeg.RTQueueControl.twiceAndInstall_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twiceAndInstall_runs

/-- info: 'PalPeg.RTQueueControl.rotation_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rotation_runs

end PalPeg.RTQueueControl
