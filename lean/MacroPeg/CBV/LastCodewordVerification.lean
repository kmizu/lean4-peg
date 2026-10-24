import MacroPeg.CBV.LastCodewordCandidate

/-! Verify the actual header run, including nonuniform runs. Counts below
are trace witnesses, never parameters of the generated expression. -/
namespace Shallot.MacroPeg.CBV.LastCodewordVerification
open ClockFreezing (Table)
open PrefixCodeCapture (PrefixFree)

/-- Every label is the actual consumed input, not a supplied recognizer. -/
inductive Run (x : List Char) (A : Nat → Res) (C : List Char → Prop) :
    Nat → List (List Char) → Nat → Prop
  | nil (p : Nat) : Run x A C p [] p
  | cons {p q r : Nat} {w : List Char} {ws : List (List Char)}
      (eval : A p=some (some q)) (strict : q<p)
      (word : C w) (suffix : sfx x p=w++sfx x q)
      (tail : Run x A C q ws r) : Run x A C p (w::ws) r

theorem run_trace {x A C p ws r} (h : Run x A C p ws r) :
    InlineRepeat.Trace A p ws.length r := by
  induction h with
  | nil => exact .zero _
  | cons hv hq hw hs ht ih => exact .succ hv hq ih

theorem run_words {x A C p ws r} (h : Run x A C p ws r) : ∀ w∈ws, C w := by
  induction h with
  | nil => simp
  | cons hv hq hw hs ht ih => intro v hmem; rcases List.mem_cons.mp hmem with rfl | hmem; exact hw; exact ih v hmem

theorem run_suffix {x A C p ws r} (h : Run x A C p ws r) :
    sfx x p=ws.flatten++sfx x r := by
  induction h with
  | nil => simp
  | cons hv hq hw hs ht ih => simpa [List.flatten_cons,List.append_assoc,ih] using hs

/-- A successful ordinary header iteration supplies its own labelled run. -/
theorem run_of_trace (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (A : MExp) (hA : A.FirstOrder)
    (C : List Char → Prop)
    (hcode : ∀ p q, p≤x.length → evV g x s T E A p=some (some q) → C (pre x p q))
    {p n r : Nat} (ht : InlineRepeat.Trace (fun q => evV g x s T E A q) p n r)
    (hp : p≤x.length) :
    ∃ ws, ws.length=n ∧ Run x (fun q => evV g x s T E A q) C p ws r := by
  induction ht with
  | zero p => exact ⟨[],rfl,.nil p⟩
  | @succ p q n r hv hq ht ih =>
    obtain ⟨ws,hn,hr⟩ := ih (by omega)
    exact ⟨pre x p q::ws,by simp [hn],.cons hv hq (hcode p q hp hv)
      (WordStarFilter.success_prefix hs hT E A hA p q hp hv).2 hr⟩

theorem run_snoc {x A C p ws q r w} (h : Run x A C p ws q)
    (hv : A q=some (some r)) (hr : r<q) (hw : C w)
    (hs : sfx x q=w++sfx x r) : Run x A C p (ws++[w]) r := by
  induction h with
  | nil => exact .cons hv hr hw hs (.nil r)
  | cons hv' hq hw' hs' ht ih => exact .cons hv' hq hw' hs' (ih hv hr hs)

/-- The actual argument itself yields the full maximal run and the exact
original capture. The exceptional empty run means the initial header fails. -/
theorem capture_run (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (A : MExp) (hA : A.FirstOrder)
    (C : List Char → Prop)
    (hcode : ∀ p q, p≤x.length → evV g x s T E A p=some (some q) → C (pre x p q))
    (p q : Nat) (hp : p≤x.length)
    (hb : evV g x s T E (LastCodewordRotation.argument A) p=some (some q)) :
    (q=p ∧ evV g x s T E A p=some none) ∨
    ∃ (u : List Char) (vs : List (List Char)) (j r : Nat),
      Run x (fun z => evV g x s T E A z) C p (u::vs) r ∧
      evV g x s T E A p=some (some j) ∧
      Run x (fun z => evV g x s T E A z) C j vs r ∧
      evV g x s T E A q=some (some r) ∧
      evV g x s T E A r=some none ∧
      pre x p q=((u::vs).take vs.length).flatten := by
  rw [LastCodewordRotation.argument_eval] at hb
  obtain ⟨n,ht,hstop⟩ := InlineRepeat.star_trace _ p q hb
  have hprefix := LastCodewordRotation.step_trace ht
  have hq : q≤x.length := by have := InlineRepeat.trace_le hprefix; omega
  rcases LastCodewordRotation.capture_endpoint _ p q hb with ⟨he,hfail⟩ | ⟨r,hfinal,hend⟩
  · exact Or.inl ⟨he,he ▸ hfail⟩
  · have hr : r<q := by
      have hle := GreedyRotation.evaluator_decreasing g x s hs T hT E A hA q hq r hfinal
      have hne : r≠q := by intro he; subst r; rw [hend] at hfinal; cases hfinal
      omega
    obtain ⟨ws,hn,hws⟩ := run_of_trace g x s hs T hT E A hA C hcode hprefix hp
    have hfull := run_snoc hws hfinal hr (hcode q r hq hfinal)
      (WordStarFilter.success_prefix hs hT E A hA q r hq hfinal).2
    have hwpre : pre x p q=ws.flatten := by
      have he := pre_eq (sfx_is_suffix x p) (run_suffix hws)
      simpa only [length_sfx x hp,length_sfx x hq] using he
    generalize he : ws++[pre x q r]=all at hfull
    cases all with
    | nil => have := congrArg List.length he; simp at this
    | cons u vs =>
      have hlen : vs.length=ws.length := by have := congrArg List.length he; simp at this; omega
      have htake : (u::vs).take vs.length=ws := by
        rw [←he,hlen,List.take_append]
        simp
      cases hfull with
      | cons hv hstrict hu hsf htail =>
        exact Or.inr ⟨u,vs,_,r,.cons hv hstrict hu hsf htail,hv,htail,hfinal,hend,by rw [htake]; exact hwpre⟩

theorem run_congr {x C p ws r} {f h : Nat → Res}
    (he : ∀ q, f q=h q) (hr : Run x f C p ws r) : Run x h C p ws r := by
  induction hr with
  | nil => exact .nil _
  | cons hv hq hw hs ht ih => exact .cons ((he _).symm.trans hv) hq hw hs ih

def verifier (A : MExp) : MExp :=
  .seq (.star (.seq (.andP A) (.param 0))) (.notP A)

/-- The fixed verifier succeeds exactly for a uniform actual codeword run.
A mismatch is finite failure, even if later input contains another copy. -/
theorem verifier_run (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (A : MExp) {C : List Char → Prop} (hc : PrefixFree C)
    (u : List Char) (hu : C u) {p ws r : _}
    (h : Run x (fun q => evV g x s T [u] A q) C p ws r)
    (hend : evV g x s T [u] A r=some none) (hp : p≤x.length) :
    evV g x s T [u] (verifier A) p=
      if ws=List.replicate ws.length u then some (some r) else some none := by
  let f := fun q => evV g x s T [u] (.seq (.andP A) (.param 0)) q
  have hfinish : ∀ q, evV g x s T [u] (verifier A) q=
      ContinuationPlan.sequence (evStar f) (GreedyRotation.negative (fun j => evV g x s T [u] A j)) q := by
    intro q; rfl
  induction h with
  | nil p =>
    have hf : f p=some none := by
      change (match evV g x s T [u] (.andP A) p with
        | some (some j) => evV g x s T [u] (.param 0) j | other => other)=_
      rw [CallLookahead.evV_peek,hend]; rfl
    simp [hfinish,ContinuationPlan.sequence,evStar_fail hf,GreedyRotation.negative,hend]
  | @cons p q r w ws hv hq hw hs ht ih =>
    have hpeek : evV g x s T [u] (.andP A) p=some (some p) := by
      rw [CallLookahead.evV_peek,hv]; rfl
    by_cases he : w=u
    · subst w
      have hlen : (sfx x q).length=q := length_sfx x (by omega)
      have hf : f p=some (some q) := by
        change evV g x s T [u] (.seq (.andP A) (.param 0)) p=_
        rw [evV_seq_ok hpeek]
        change evV g x s T [] (.lit u) p=_
        simpa only [hlen] using LastCodewordCandidate.literal_at g x s T [] u (sfx x q) p hs
      have hnext : evV g x s T [u] (verifier A) p=evV g x s T [u] (verifier A) q := by
        simp only [hfinish,ContinuationPlan.sequence,evStar_ok hf hq]
      rw [hnext,ih hend (by omega)]
      simp only [List.length_cons,List.replicate_succ,List.cons.injEq,true_and]
    · have hstrip : Shallot.stripPrefix? u (w++sfx x q)=none := by
        cases hh : Shallot.stripPrefix? u (w++sfx x q) with
        | none => rfl
        | some rest => exact False.elim (he (PrefixCodeCapture.prefix_identifies hc hu hw
            ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm⟩).symm)
      have hf : f p=some none := by
        change evV g x s T [u] (.seq (.andP A) (.param 0)) p=_
        rw [evV_seq_ok hpeek]
        simp [evV,hs,hstrip]
      have hne : w::ws≠List.replicate (w::ws).length u := by
        simp only [List.length_cons,List.replicate_succ,ne_eq,List.cons.injEq]
        exact fun hh => he hh.1
      rw [if_neg hne]
      simp [hfinish,ContinuationPlan.sequence,evStar_fail hf,GreedyRotation.negative,hv]

/-- Dropping the final header from the original capture, then replaying
that capture after the first header, succeeds exactly on uniform runs. -/
theorem shifted_prefix_iff {C : List Char → Prop} (hc : PrefixFree C)
    (u : List Char) (vs : List (List Char)) (rest : List Char)
    (hu : C u) (hv : ∀ v∈vs, C v) :
    ((u::vs).take vs.length).flatten.IsPrefix (vs.flatten++rest) ↔
      vs=List.replicate vs.length u := by
  constructor
  · intro hp
    have hall : ∀ w∈u::vs, C w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw
      · exact hu
      · exact hv w hw
    have hn : ((u::vs).take vs.length).length=vs.length := by simp
    have hd := CodewordReplay.decode_prefix hc ((u::vs).take vs.length) vs rest
      (fun w hw => hall w (List.mem_of_mem_take hw)) hv (by omega) hp
    rw [List.take_of_length_le (by omega)] at hd
    exact CodewordReplay.shift_forces_replicate u vs hd
  · intro he
    have hh : (u::vs).take vs.length=vs := by
      rw [he]
      rw [←List.replicate_succ]
      simp
    rw [hh]
    exact ⟨rest,rfl⟩

/-- This is the source's actual literal replay, with the entire capture
retained. The count is inferred from the trace, not built into syntax. -/
theorem shifted_replay (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    {C : List Char → Prop} (hc : PrefixFree C)
    (u : List Char) (vs : List (List Char)) (rest : List Char)
    (hu : C u) (hv : ∀ v∈vs, C v) (p : Nat) (hs : sfx x p=vs.flatten++rest) :
    evV g x s T [((u::vs).take vs.length).flatten] (.param 0) p=
      if vs=List.replicate vs.length u then some (some rest.length) else some none := by
  by_cases he : vs=List.replicate vs.length u
  · have hh : (u::vs).take vs.length=vs := by
      rw [he,←List.replicate_succ]
      simp
    rw [if_pos he,hh]
    change evV g x s T [] (.lit vs.flatten) p=_
    exact LastCodewordCandidate.literal_at g x s T [] vs.flatten rest p hs
  · rw [if_neg he]
    have hstrip : Shallot.stripPrefix? ((u::vs).take vs.length).flatten (vs.flatten++rest)=none := by
      cases hh : Shallot.stripPrefix? ((u::vs).take vs.length).flatten (vs.flatten++rest) with
      | none => rfl
      | some r => exact False.elim (he ((shifted_prefix_iff hc u vs rest hu hv).mp
          ⟨r,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm⟩))
    simp [evV,hs,hstrip]

/-- On every actual maximal run, the original long-capture replay and
the fixed Seq verifier have the same full result, including unequal words.
No bound on the run length or header lengths occurs in the expression. -/
theorem replay_verifier_agree (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (A : MExp) {C : List Char → Prop} (hc : PrefixFree C)
    (u : List Char) (hu : C u) {p ws r : _}
    (h : Run x (fun q => evV g x s T [u] A q) C p ws r)
    (hend : evV g x s T [u] A r=some none) (hp : p≤x.length) :
    evV g x s T [((u::ws).take ws.length).flatten] (.param 0) p=
      evV g x s T [u] (verifier A) p := by
  rw [shifted_replay g x s T hc u ws (sfx x r) hu (run_words h) p (run_suffix h),
    verifier_run g x s T A hc u hu h hend hp,
    length_sfx x (by have hh := InlineRepeat.trace_le (run_trace h); omega)]

/-- Evaluation of the unary Seq helper with argument A: retain its actual
first codeword, then run the fixed verifier. -/
def probe (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (A : MExp) (p : Nat) : Res :=
  match evV g x s T [] A p with
  | some (some j) => evV g x s T [pre x p j] (verifier A) j
  | other => other

/-- Every successful original argument gives a local entry equivalence on
the same input and the same entire captured string. The continuation is
arbitrary, so its failure or undefinedness is preserved. -/
theorem actual_entry (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (A : MExp) (hA : A.FirstOrder)
    (hind : ∀ E z, evV g x s T E A z=evV g x s T [] A z)
    {C : List Char → Prop} (hc : PrefixFree C)
    (hcode : ∀ p q, p≤x.length → evV g x s T [] A p=some (some q) → C (pre x p q))
    (p q : Nat) (hp : p≤x.length)
    (hb : evV g x s T [] (LastCodewordRotation.argument A) p=some (some q))
    (b : MExp) :
    evV g x s T [pre x p q] (.seq A (.seq (.param 0) b)) p=
      match probe g x s T A p with
      | some (some _) => evV g x s T [pre x p q] (.seq A b) q
      | other => other := by
  rcases capture_run g x s hs T hT [] A hA C hcode p q hp hb with
    ⟨he,hfail⟩ | ⟨u,vs,j,r,hfull,hfirst,htail,hfinal,hend,hcap⟩
  · rw [evV_seq_fail ((hind _ p).trans hfail)]
    simp [probe,hfail]
  · have hj : j≤x.length := (WordStarFilter.success_prefix hs hT [] A hA p j hp hfirst).1
    have hword : pre x p j=u := by
      cases hfull with
      | @cons _ z _ _ _ hv hstrict hu hsf ht =>
        have hz : z=j := by simpa using hv.symm.trans hfirst
        subst z
        have he := pre_eq (sfx_is_suffix x p) hsf
        simpa only [length_sfx x hp,length_sfx x hj] using he
    have hu : C u := run_words hfull u (by simp)
    have ht' : Run x (fun z => evV g x s T [u] A z) C j vs r :=
      run_congr (fun z => (hind [u] z).symm) htail
    have hv := verifier_run g x s T A hc u hu ht' ((hind [u] r).trans hend) hj
    have hprobe : probe g x s T A p=
        if vs=List.replicate vs.length u then some (some r) else some none := by
      simp only [probe,hfirst,hword]
      exact hv
    rw [evV_seq_ok ((hind _ p).trans hfirst)]
    have hreplay : evV g x s T [pre x p q] (.param 0) j=
        if vs=List.replicate vs.length u then some (some r) else some none := by
      rw [hcap,shifted_replay g x s T hc u vs (sfx x r) hu (run_words htail) j (run_suffix htail),
        length_sfx x (by have := InlineRepeat.trace_le (run_trace htail); omega)]
    change (match evV g x s T [pre x p q] (.param 0) j with
      | some (some z) => evV g x s T [pre x p q] b z | other => other)=_
    rw [hreplay,hprobe]
    by_cases he : vs=List.replicate vs.length u
    · rw [if_pos he]
      exact (evV_seq_ok ((hind _ q).trans hfinal)).symm
    · rw [if_neg he]

end Shallot.MacroPeg.CBV.LastCodewordVerification
