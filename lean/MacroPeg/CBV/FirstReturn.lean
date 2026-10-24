import MacroPeg.CBV.WordStarFilter

/-! Inline first-return paths eliminate finite control without parameter
passing. Repetition steps may have different captured words each time. -/
namespace Shallot.MacroPeg.CBV.FirstReturn
open RegularCaptureProduct (choice)
open ClockFreezing (Table)
abbrev Path := List (Nat × Nat)

def scan (allowed : List Nat) (target : Nat) : Path → Option Path
  | [] => none
  | (q,p)::tail => if q=target then some ((q,p)::tail) else if q∈allowed then scan allowed target tail else none

def observe : Option Path → Res
  | some ((_,p)::_) => some (some p)
  | _ => some none

inductive Run (F : Nat → Nat → Nat → Res) (W : Nat) : Path → Prop
  | last (q p : Nat) (hq : q<W) (hf : ∀ r, r<W → F q r p=some none) : Run F W [(q,p)]
  | cons (q p t z : Nat) (tail : Path) (hq : q<W) (hz : z<p)
      (hf : ∀ r, r<W → F q r p=if r=t then some (some z) else some none)
      (rest : Run F W ((t,z)::tail)) : Run F W ((q,p)::(t,z)::tail)

theorem run_head {F : Nat → Nat → Nat → Res} {W q p : Nat} {tail : Path} (h : Run F W ((q,p)::tail)) : q<W := by
  cases h <;> assumption

theorem run_length {F : Nat → Nat → Nat → Res} {W : Nat} {path : Path} (h : Run F W path) : 0<path.length := by
  cases h <;> simp

/-- The first-hit result retains a real suffix run and its head state. -/
theorem scan_sound {F : Nat → Nat → Nat → Res} {W : Nat} {path : Path} (h : Run F W path)
    (A : List Nat) (r : Nat) {out : Path} (hs : scan A r path=some out) :
    Run F W out ∧ out.length≤path.length ∧ ∃ p tail, out=(r,p)::tail := by
  induction h with
  | last q p hq hf =>
    simp only [scan] at hs
    split at hs
    · rename_i he; cases hs; exact ⟨.last q p hq hf,Nat.le_refl _,p,[],by simp [he]⟩
    · split at hs <;> cases hs
  | cons q p t z tail hq hz hf rest ih =>
    simp only [scan] at hs
    split at hs
    · rename_i he; cases hs; exact ⟨.cons q p t z tail hq hz hf rest,Nat.le_refl _,p,(t,z)::tail,by simp [he]⟩
    · split at hs
      · obtain ⟨ho,hl,hr⟩ := ih hs
        exact ⟨ho,by simp only [List.length_cons] at *; omega,hr⟩
      · cases hs

theorem scan_mem (A : List Nat) (r : Nat) : ∀ path out, scan A r path=some out → ∀ a∈out, a∈path
  | [], _, hs, _, _ => by cases hs
  | (q,p)::tail, out, hs, a, ha => by
    simp only [scan] at hs
    split at hs
    · cases hs; exact ha
    · split at hs
      · exact List.mem_cons_of_mem _ (scan_mem A r tail out hs a ha)
      · cases hs

theorem run_positions {F : Nat → Nat → Nat → Res} {W : Nat} {path : Path} (h : Run F W path) :
    ∀ q p tail, path=(q,p)::tail → ∀ s v, (s,v)∈path → v≤p := by
  induction h with
  | last q p hq hf =>
    intro a b tail he s v hm
    cases he
    simp only [List.mem_singleton,Prod.mk.injEq] at hm
    omega
  | cons q p t z tail hq hz hf rest ih =>
    intro a b rest' he s v hm
    cases he
    rcases List.mem_cons.mp hm with he | ht
    · cases he; omega
    · have := ih t z tail rfl s v ht; omega

theorem scan_position_le {F : Nat → Nat → Nat → Res} {W q p : Nat} {tail : Path}
    (h : Run F W ((q,p)::tail)) (A : List Nat) (r v : Nat) (out : Path)
    (hs : scan A r ((q,p)::tail)=some ((r,v)::out)) : v≤p :=
  run_positions h q p tail rfl r v (scan_mem A r _ _ hs _ (by simp))

/-- If removing q finds a first return to q, a larger allowed-state scan
can continue from that return. Otherwise it is the scan avoiding q. -/
theorem scan_eliminate (A : List Nat) (q r : Nat) (hq : q∈A) (hr : r∉A) (hqr : q≠r) :
    ∀ path, scan A r path=
      match scan (A.erase q) q path with
      | some out => scan A r out
      | none => scan (A.erase q) r path
  | [] => rfl
  | (t,p)::tail => by
    by_cases htq : t=q
    · subst t
      simp [scan]
    · by_cases htr : t=r
      · subst t
        have hne : r≠q := Ne.symm hqr
        have hn : r∉A.erase q := fun h => hr (List.mem_of_mem_erase h)
        simp [scan,hne,hn]
      · have hm : t∈A.erase q ↔ t∈A := List.mem_erase_of_ne htq
        simp only [scan,if_neg htq,if_neg htr]
        by_cases ht : t∈A
        · simp only [if_pos ht,if_pos (hm.mpr ht)]
          exact scan_eliminate A q r hq hr hqr tail
        · simp only [if_neg ht,if_neg (fun h => ht (hm.mp h))]

def step (W : Nat) (F : Nat → Nat → MExp) (q : Nat) (K : Nat → MExp) : MExp :=
  choice ((List.range W).map (fun t => .seq (F q t) (K t)))

/-- A first-return loop avoids the final target and all eliminated states.
Removing the current state strictly decreases the construction size. -/
def hit (W : Nat) (F : Nat → Nat → MExp) (A : List Nat) (q r : Nat) : MExp :=
  if q=r then .eps else if _hq : q∈A then
    .seq (.star (step W F q (fun t => hit W F (A.erase q) t q)))
      (step W F q (fun t => hit W F (A.erase q) t r))
  else MExp.failAlways
termination_by A.length
decreasing_by
  all_goals
    have hlen := List.length_erase_of_mem _hq
    have hpos := List.length_pos_of_mem _hq
    omega

theorem hit_firstOrder (W : Nat) (F : Nat → Nat → MExp) (hF : ∀ q r, (F q r).FirstOrder) :
    ∀ A q r, (hit W F A q r).FirstOrder := by
  intro A
  induction A using (measure List.length).wf.induction with
  | h A ih =>
    intro q r
    rw [hit]
    split
    · trivial
    · split
      · rename_i hq
        have hl : (A.erase q).length<A.length := by
          have := List.length_erase_of_mem hq
          have := List.length_pos_of_mem hq
          omega
        constructor <;> apply RegularCaptureProduct.choice_firstOrder <;> intro e he <;>
          obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
        · exact ⟨hF q t,ih _ hl t q⟩
        · exact ⟨hF q t,ih _ hl t r⟩
      · trivial

theorem step_last (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (W : Nat) (F : Nat → Nat → MExp) (q p : Nat) (K : Nat → MExp)
    (hf : ∀ r, r<W → evV g x s T E (F q r) p=some none) :
    evV g x s T E (step W F q K) p=some none := by
  apply CaptureTransitionProfile.choice_failed
  intro r hr
  exact evV_seq_fail (hf r (List.mem_range.mp hr))

theorem step_cons (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (W : Nat) (F : Nat → Nat → MExp) (q p t z : Nat) (K : Nat → MExp) (ht : t<W)
    (hf : ∀ r, r<W → evV g x s T E (F q r) p=if r=t then some (some z) else some none) :
    evV g x s T E (step W F q K) p=evV g x s T E (K t) z := by
  rw [step,CaptureTransitionProfile.choice_unique (chosen := t) (v := evV g x s T E (K t) z)]
  · rw [if_pos (List.mem_range.mpr ht)]
  · intro r hr
    have hh := hf r (List.mem_range.mp hr)
    by_cases he : r=t
    · subst r; rw [if_pos rfl] at hh; rw [evV_seq_ok hh,if_pos rfl]
    · rw [if_neg he] at hh; rw [evV_seq_fail hh,if_neg he]

/-- A finite inline expression recognizes the first target hit on every
actual finite iteration path, preserving the retained environment. -/
theorem hit_correct (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (W : Nat) (F : Nat → Nat → MExp) :
    ∀ A, A.Nodup → ∀ q r p tail, Run (fun q r p => evV g x s T E (F q r) p) W ((q,p)::tail) → r∉A →
      evV g x s T E (hit W F A q r) p=observe (scan A r ((q,p)::tail)) := by
  intro A
  induction A using (measure List.length).wf.induction with
  | h A ih =>
    intro hA q r p tail hRun hr
    by_cases hqr : q=r
    · subst q
      rw [hit,if_pos rfl]
      simp only [scan,ite_true,observe]
      rfl
    · by_cases hq : q∈A
      · have hlen : (A.erase q).length<A.length := by
          have := List.length_erase_of_mem hq
          have := List.length_pos_of_mem hq
          omega
        have hq' : q∉A.erase q := hA.not_mem_erase
        have hr' : r∉A.erase q := fun h => hr (List.mem_of_mem_erase h)
        have hStep (v : Nat) (path : Path)
            (hR : Run (fun q r p => evV g x s T E (F q r) p) W ((q,v)::path))
            (target : Nat) (hTarget : target∉A.erase q) :
            evV g x s T E (step W F q (fun t => hit W F (A.erase q) t target)) v=
              observe (scan (A.erase q) target path) := by
          cases hR with
          | last _ _ _ hf => exact step_last g x s T E W F q v _ hf
          | cons _ _ t z path _ _ hf rest =>
            rw [step_cons g x s T E W F q v t z _ (run_head rest) hf]
            exact ih _ hlen (hA.erase q) t target z path rest hTarget
        have main : ∀ v path, Run (fun q r p => evV g x s T E (F q r) p) W ((q,v)::path) →
            evV g x s T E (.seq (.star (step W F q (fun t => hit W F (A.erase q) t q)))
              (step W F q (fun t => hit W F (A.erase q) t r))) v=observe (scan A r ((q,v)::path)) := by
          intro v
          induction v using Nat.strongRecOn with
          | ind v iv =>
            intro path hR
            have hLoop := hStep v path hR q hq'
            have hExit := hStep v path hR r hr'
            have hScan := scan_eliminate A q r hq hr hqr path
            cases hs : scan (A.erase q) q path with
            | none =>
              rw [hs] at hLoop hScan
              have hL : evV g x s T E (step W F q (fun t => hit W F (A.erase q) t q)) v=some none := hLoop
              rw [evV_seq_ok (show evV g x s T E (.star (step W F q (fun t => hit W F (A.erase q) t q))) v=some (some v) from evStar_fail hL),hExit]
              simp only [scan,if_neg hqr,if_pos hq,hScan]
            | some out =>
              have hPath : Run (fun q r p => evV g x s T E (F q r) p) W path := by
                cases hR with
                | last => cases hs
                | cons _ _ _ _ _ _ _ _ rest => exact rest
              obtain ⟨ho,_,z,rest,rfl⟩ := scan_sound hPath (A.erase q) q hs
              have hz : z<v := by
                cases hR with
                | last => cases hs
                | cons _ _ t z' tail _ hz _ rest =>
                  have := scan_position_le rest (A.erase q) q z _ hs
                  omega
              rw [hs] at hLoop hScan
              have hL : evV g x s T E (step W F q (fun t => hit W F (A.erase q) t q)) v=some (some z) := hLoop
              change (match evStar (fun a => evV g x s T E (step W F q (fun t => hit W F (A.erase q) t q)) a) v with
                | some (some a) => evV g x s T E (step W F q (fun t => hit W F (A.erase q) t r)) a
                | other => other)=_
              rw [evStar_ok hL hz]
              change evV g x s T E (.seq (.star (step W F q (fun t => hit W F (A.erase q) t q)))
                (step W F q (fun t => hit W F (A.erase q) t r))) z=_
              rw [iv z hz rest ho]
              simp only [scan,if_neg hqr,if_pos hq,hScan]
        rw [hit,if_neg hqr,dif_pos hq]
        exact main p tail hRun
      · rw [hit,if_neg hqr,dif_neg hq]
        simp only [scan,if_neg hqr,if_neg hq,observe]
        rfl

def Source (f : Nat → Res) : Path → Prop
  | [] => False
  | [(_,p)] => f p=some none
  | (_,p)::(t,z)::tail => f p=some (some z) ∧ Source f ((t,z)::tail)

def Ends : Path → Nat → Nat → Prop
  | [], _, _ => False
  | [a], q, p => a=(q,p)
  | _::b::tail, q, p => Ends (b::tail) q p

theorem scan_source (f : Nat → Res) (A : List Nat) (r : Nat) :
    ∀ path out, Source f path → scan A r path=some out → Source f out
  | [], _, h, _ => False.elim h
  | (q,p)::tail, out, h, hs => by
    simp only [scan] at hs
    split at hs
    · cases hs; exact h
    · split at hs
      · cases tail with
        | nil => cases hs
        | cons a tail => exact scan_source f A r (a::tail) out h.2 hs
      · cases hs

theorem scan_ends (A : List Nat) (r t j : Nat) :
    ∀ path out, Ends path t j → scan A r path=some out → Ends out t j
  | [], _, h, _ => False.elim h
  | (q,p)::tail, out, h, hs => by
    simp only [scan] at hs
    split at hs
    · cases hs; exact h
    · split at hs
      · cases tail with
        | nil => cases hs
        | cons a tail => exact scan_ends A r t j (a::tail) out h hs
      · cases hs

theorem scan_reaches_end {F : Nat → Nat → Nat → Res} {W : Nat} {path : Path} (h : Run F W path)
    (A : List Nat) (r j : Nat) (hA : ∀ q, q<W → q≠r → q∈A) (he : Ends path r j) :
    ∃ out, scan A r path=some out := by
  induction h with
  | last q p hq hf =>
    have hq' : q=r := (show q=r ∧ p=j from by simpa [Ends] using he).1
    subst q
    exact ⟨[(r,p)],by simp [scan]⟩
  | cons q p t z tail hq hz hf rest ih =>
    by_cases hqr : q=r
    · subst q; exact ⟨(r,p)::(t,z)::tail,by simp [scan]⟩
    · simpa only [scan,if_neg hqr,if_pos (hA q hq hqr)] using ih he

/-- After the first target hit, consume every complete first-return loop.
The final original stopping test prevents accepting a shorter prefix. -/
theorem returns_correct (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (W : Nat) (F : Nat → Nat → MExp) (e : MExp) (A : List Nat) (hA : A.Nodup)
    (r : Nat) (hr : r∉A) (hAll : ∀ q, q<W → q≠r → q∈A) (t j : Nat) :
    ∀ p tail, Run (fun q r p => evV g x s T E (F q r) p) W ((r,p)::tail) →
      Source (fun p => evV g x s T E e p) ((r,p)::tail) → Ends ((r,p)::tail) t j →
      evV g x s T E (.seq (.star (step W F r (fun q => hit W F A q r))) (.notP e)) p=
        if t=r then some (some j) else some none := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro tail hR hS hE
    have hStep : evV g x s T E (step W F r (fun q => hit W F A q r)) p=observe (scan A r tail) := by
      cases hR with
      | last _ _ _ hf => exact step_last g x s T E W F r p _ hf
      | cons _ _ q z tail _ _ hf rest =>
        rw [step_cons g x s T E W F r p q z _ (run_head rest) hf]
        exact hit_correct g x s T E W F A hA q r z tail rest hr
    cases hs : scan A r tail with
    | none =>
      rw [hs] at hStep
      have hL : evV g x s T E (step W F r (fun q => hit W F A q r)) p=some none := hStep
      rw [evV_seq_ok (show evV g x s T E (.star (step W F r (fun q => hit W F A q r))) p=some (some p) from evStar_fail hL)]
      cases hR with
      | last _ _ _ _ =>
        have he : t=r ∧ j=p := by simpa [Ends,eq_comm] using hE
        rw [if_pos he.1]
        change (match evV g x s T E e p with | some (some _) => some none | some none => some (some p) | none => none)=_
        rw [show evV g x s T E e p=some none from hS,he.2]
      | cons _ _ q z tail _ _ _ rest =>
        have ht : t≠r := by
          intro he
          obtain ⟨out,ho⟩ := scan_reaches_end rest A r j hAll (by change Ends ((q,z)::tail) t j at hE; simpa only [he] using hE)
          rw [hs] at ho; cases ho
        rw [if_neg ht]
        change (match evV g x s T E e p with | some (some _) => some none | some none => some (some p) | none => none)=_
        have hSrc : evV g x s T E e p=some (some z) := hS.1
        rw [hSrc]
    | some out =>
      have hTail : Run (fun q r p => evV g x s T E (F q r) p) W tail := by
        cases hR with
        | last => cases hs
        | cons _ _ _ _ _ _ _ _ rest => exact rest
      obtain ⟨ho,_,v,rest,rfl⟩ := scan_sound hTail A r hs
      have hv : v<p := by
        cases hR with
        | last => cases hs
        | cons _ _ q z tail _ hz _ rest => have := scan_position_le rest A r v _ hs; omega
      have hSourceTail : Source (fun p => evV g x s T E e p) tail := by
        cases tail with
        | nil => cases hs
        | cons a tail => exact hS.2
      have hEndTail : Ends tail t j := by
        cases tail with
        | nil => cases hs
        | cons a tail => exact hE
      rw [hs] at hStep
      have hL : evV g x s T E (step W F r (fun q => hit W F A q r)) p=some (some v) := hStep
      change (match evStar (fun p => evV g x s T E (step W F r (fun q => hit W F A q r)) p) p with
        | some (some p) => evV g x s T E (.notP e) p | other => other)=_
      rw [evStar_ok hL hv]
      exact ih v hv rest ho (scan_source _ A r _ _ hSourceTail hs) (scan_ends A r t j _ _ hEndTail hs)

def finished (W : Nat) (F : Nat → Nat → MExp) (e : MExp) (q r : Nat) : MExp :=
  let A := (List.range W).erase r
  .seq (hit W F A q r) (.seq (.star (step W F r (fun t => hit W F A t r))) (.notP e))

theorem finished_correct (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (W : Nat) (F : Nat → Nat → MExp) (e : MExp) (q r p : Nat) (tail : Path)
    (hR : Run (fun q r p => evV g x s T E (F q r) p) W ((q,p)::tail))
    (hS : Source (fun p => evV g x s T E e p) ((q,p)::tail))
    (t j : Nat) (hE : Ends ((q,p)::tail) t j) :
    evV g x s T E (finished W F e q r) p=if t=r then some (some j) else some none := by
  let A := (List.range W).erase r
  have hA : A.Nodup := List.nodup_range.erase r
  have hr : r∉A := List.nodup_range.not_mem_erase
  have hAll (q : Nat) (hq : q<W) (hne : q≠r) : q∈A := (List.mem_erase_of_ne hne).mpr (List.mem_range.mpr hq)
  have hh := hit_correct g x s T E W F A hA q r p tail hR hr
  change evV g x s T E (.seq (hit W F A q r) _) p=_
  cases hs : scan A r ((q,p)::tail) with
  | none =>
    rw [hs] at hh
    rw [evV_seq_fail hh]
    have hn : t≠r := by
      intro he
      obtain ⟨out,ho⟩ := scan_reaches_end hR A r j hAll (by simpa only [he] using hE)
      rw [hs] at ho; cases ho
    rw [if_neg hn]
  | some out =>
    obtain ⟨ho,_,v,rest,rfl⟩ := scan_sound hR A r hs
    rw [hs] at hh
    rw [evV_seq_ok hh]
    exact returns_correct g x s T E W F e A hA r hr hAll t j v rest ho
      (scan_source _ A r _ _ hS hs) (scan_ends A r t j _ _ hE hs)

theorem step_firstOrder (W : Nat) (F : Nat → Nat → MExp) (hF : ∀ q r, (F q r).FirstOrder)
    (q : Nat) (K : Nat → MExp) (hK : ∀ t, (K t).FirstOrder) : (step W F q K).FirstOrder := by
  apply RegularCaptureProduct.choice_firstOrder
  intro e he
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
  exact ⟨hF q t,hK t⟩

theorem finished_firstOrder (W : Nat) (F : Nat → Nat → MExp) (hF : ∀ q r, (F q r).FirstOrder)
    (e : MExp) (he : e.FirstOrder) (q r : Nat) : (finished W F e q r).FirstOrder :=
  ⟨hit_firstOrder W F hF _ q r,step_firstOrder W F hF r _ (fun t => hit_firstOrder W F hF _ t r),he⟩

theorem step_safe (n W : Nat) (F : Nat → Nat → MExp) (q : Nat) (K : Nat → MExp)
    (hF : ∀ r, r<W → FilteredOverlapCaller.Tail n (F q r))
    (hK : ∀ t, t<W → FilteredOverlapCaller.Tail n (K t)) : FilteredOverlapCaller.Tail n (step W F q K) := by
  apply WordStarFilter.choice_safe
  intro e he
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
  exact ⟨hF t (List.mem_range.mp ht),hK t (List.mem_range.mp ht)⟩

theorem hit_safe (n W : Nat) (F : Nat → Nat → MExp)
    (hF : ∀ q r, q<W → r<W → FilteredOverlapCaller.Tail n (F q r)) :
    ∀ A q r, q<W → r<W → FilteredOverlapCaller.Tail n (hit W F A q r) := by
  intro A
  induction A using (measure List.length).wf.induction with
  | h A ih =>
    intro q r hq hr
    rw [hit]
    split
    · trivial
    · split
      · rename_i hm
        have hl : (A.erase q).length<A.length := by
          have := List.length_erase_of_mem hm
          have := List.length_pos_of_mem hm
          omega
        exact ⟨step_safe n W F q _ (fun t ht => hF q t hq ht) (fun t ht => ih _ hl t q ht hq),
          step_safe n W F q _ (fun t ht => hF q t hq ht) (fun t ht => ih _ hl t r ht hr)⟩
      · trivial

theorem finished_safe (n W : Nat) (F : Nat → Nat → MExp)
    (hF : ∀ q r, q<W → r<W → FilteredOverlapCaller.Tail n (F q r))
    (e : MExp) (he : FilteredOverlapCaller.Tail n e) (q r : Nat) (hq : q<W) (hr : r<W) :
    FilteredOverlapCaller.Tail n (finished W F e q r) :=
  ⟨hit_safe n W F hF _ q r hq hr,
    step_safe n W F r _ (fun t ht => hF r t hr ht) (fun t ht => hit_safe n W F hF _ t r ht hr),he⟩

end Shallot.MacroPeg.CBV.FirstReturn
