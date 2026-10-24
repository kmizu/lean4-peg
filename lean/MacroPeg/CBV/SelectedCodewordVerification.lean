import MacroPeg.CBV.LastCodewordVerification

/-! Keep the original repetition's selected endpoint, even when its guard
stops before later codewords. The count never occurs in generated syntax. -/
namespace Shallot.MacroPeg.CBV.SelectedCodewordVerification
open ClockFreezing (Table)
open LastCodewordVerification (Run run_trace run_words run_suffix run_snoc)

/-- Each successful iteration retains its first header endpoint and checks
another header followed by the original condition. -/
def step (A G : MExp) : MExp := .seq A (.andP (.seq A G))
def argument (A G : MExp) : MExp := .star (step A G)
/-- Stop on the original step, then compare the one final header. -/
def verifier (S : MExp) : MExp := .seq (LastCodewordVerification.verifier S) (.param 0)

theorem step_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (A G : MExp) (p q : Nat)
    (h : evV g x s T E (step A G) p=some (some q)) :
    evV g x s T E A p=some (some q) ∧
      ∃ r, evV g x s T E A q=some (some r) := by
  change (match evV g x s T E A p with
    | some (some j) => evV g x s T E (.andP (.seq A G)) j | other => other)=_ at h
  cases ha : evV g x s T E A p with
  | none => simp [ha] at h
  | some result => cases result with
    | none => simp [ha] at h
    | some j =>
      rw [ha] at h
      change evV g x s T E (.andP (.seq A G)) j=some (some q) at h
      rw [CallLookahead.evV_peek] at h
      change (match (match evV g x s T E A j with
        | some (some r) => evV g x s T E G r | other => other) with
        | some (some _) => some (some j) | other => other)=_ at h
      cases hb : evV g x s T E A j with
      | none => simp [hb] at h
      | some result => cases result with
        | none => simp [hb] at h
        | some r =>
          cases hc : evV g x s T E G r with
          | none => simp [hb,hc] at h
          | some result => cases result with
            | none => simp [hb,hc] at h
            | some z =>
              have he : j=q := by simpa [hb,hc] using h
              subst j
              exact ⟨rfl,r,hb⟩

theorem trace_final {f a : Nat → Res}
    (he : ∀ p q, f p=some (some q) → ∃ r, a q=some (some r))
    {p n q : Nat} (ht : InlineRepeat.Trace f p (n+1) q) :
    ∃ r, a q=some (some r) := by
  induction n generalizing p with
  | zero => cases ht with | succ hv hz tail => cases tail; exact he _ _ hv
  | succ n ih => cases ht with | succ hv hz tail => exact ih tail

/-- Later codewords are outside the verification region. -/
theorem verifier_run (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (S : MExp) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (u v : List Char) (hu : C u) (hv : C v) {p ws q r : _}
    (h : Run x (fun z => evV g x s T [u] S z) C p ws q)
    (hend : evV g x s T [u] S q=some none)
    (hs : sfx x q=v++sfx x r) (hp : p≤x.length) (hr : r≤x.length) :
    evV g x s T [u] (verifier S) p=
      if ws++[v]=List.replicate (ws.length+1) u then some (some r) else some none := by
  have hq : q≤x.length := by have := InlineRepeat.trace_le (run_trace h); omega
  have hf := LastCodewordVerification.verifier_run g x s T S hc u hu h hend hp
  change (match evV g x s T [u] (LastCodewordVerification.verifier S) p with
    | some (some z) => evV g x s T [u] (.param 0) z | other => other)=_
  rw [hf]
  by_cases he : ws=List.replicate ws.length u
  · rw [if_pos he]
    by_cases hvu : v=u
    · subst v
      have hlist : ws++[u]=List.replicate (ws.length+1) u := by simpa only [List.replicate_succ'] using congrArg (fun z => z++[u]) he
      rw [if_pos hlist]
      change evV g x s T [] (.lit u) q=_
      simpa only [length_sfx x hr] using
        LastCodewordCandidate.literal_at g x s T [] u (sfx x r) q hs
    · have hlist : ws++[v]≠List.replicate (ws.length+1) u := by
        rw [List.replicate_succ',←he]
        simpa using hvu
      have hstrip : Shallot.stripPrefix? u (v++sfx x r)=none := by
        cases hh : Shallot.stripPrefix? u (v++sfx x r) with
        | none => rfl
        | some rest => exact False.elim (hvu (PrefixCodeCapture.prefix_identifies hc hu hv
            ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm⟩).symm)
      rw [if_neg hlist]
      simp [evV,hs,hstrip]
  · rw [if_neg he]
    have hlist : ws++[v]≠List.replicate (ws.length+1) u := by
      intro hh
      have hh' := congrArg (List.take ws.length) hh
      exact he (by simpa [List.take_append] using hh')
    rw [if_neg hlist]

/-- The original whole capture remains in the continuation environment. -/
theorem nonempty_entry (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (A G : MExp) (hA : A.FirstOrder) (hG : G.FirstOrder)
    (hind : ∀ E z, evV g x s T E A z=evV g x s T [] A z)
    (hinds : ∀ E z, evV g x s T E (step A G) z=evV g x s T [] (step A G) z)
    {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ p q, p≤x.length → evV g x s T [] A p=some (some q) → C (pre x p q))
    (p q j : Nat) (hp : p≤x.length)
    (hfirst : evV g x s T [] (step A G) p=some (some j))
    (hb : evV g x s T [] (argument A G) p=some (some q)) (b : MExp) :
    evV g x s T [pre x p q] (.seq A (.seq (.param 0) b)) p=
      match evV g x s T [pre x p j] (verifier (step A G)) j with
      | some (some _) => evV g x s T [pre x p q] (.seq A b) q
      | other => other := by
  change evStar (fun z => evV g x s T [] (step A G) z) p=some (some q) at hb
  obtain ⟨n,ht,hstop⟩ := InlineRepeat.star_trace _ p q hb
  have hS : (step A G).FirstOrder := ⟨hA,hA,hG⟩
  obtain ⟨ws,hlen,hrun⟩ := LastCodewordVerification.run_of_trace g x s hs T hT []
    (step A G) hS C
    (fun z r hz h => hcode z r hz (step_success g x s T [] A G z r h).1) ht hp
  cases hrun with
  | nil => rw [hstop] at hfirst; cases hfirst
  | @cons _ z _ u ws hv hstrict hu hsf htail =>
    have hz : z=j := by simpa using hv.symm.trans hfirst
    subst z
    have hj : j≤x.length := by omega
    have hq : q≤x.length := by have := InlineRepeat.trace_le (run_trace htail); omega
    have hword : pre x p j=u := by
      have he := pre_eq (sfx_is_suffix x p) hsf
      simpa only [length_sfx x hp,length_sfx x hj] using he
    have hfinal : ∃ r, evV g x s T [] A q=some (some r) := by
      have ht' := run_trace (Run.cons hv hstrict hu hsf htail)
      exact trace_final (fun a b h => (step_success g x s T [] A G a b h).2) ht'
    obtain ⟨r,har⟩ := hfinal
    have hr : r≤x.length := (WordStarFilter.success_prefix hs hT [] A hA q r hq har).1
    let v := pre x q r
    have hvcode : C v := hcode q r hq har
    have hvsfx : sfx x q=v++sfx x r := (WordStarFilter.success_prefix hs hT [] A hA q r hq har).2
    have hcap : pre x p q=(u::ws).flatten := by
      have he := pre_eq (sfx_is_suffix x p) (run_suffix (Run.cons hv hstrict hu hsf htail))
      simpa only [length_sfx x hp,length_sfx x hq] using he
    have hvs : ∀ w∈ws++[v], C w := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact run_words htail w hw
      · simpa using (List.mem_singleton.mp hw ▸ hvcode)
    have htake : ((u::(ws++[v])).take (ws++[v]).length).flatten=(u::ws).flatten := by
      simp [List.take_succ_cons]
    have hreplay := LastCodewordVerification.shifted_replay g x s T hc u (ws++[v]) (sfx x r)
      hu hvs j (by simpa [List.flatten_append,List.append_assoc,hvsfx] using run_suffix htail)
    rw [htake,←hcap,length_sfx x hr] at hreplay
    have hverify := verifier_run g x s T (step A G) hc u v hu hvcode
      (LastCodewordVerification.run_congr (fun z => (hinds [u] z).symm) htail)
      ((hinds [u] q).trans hstop) hvsfx hj hr
    simp only [List.length_append,List.length_singleton] at hreplay
    rw [evV_seq_ok ((hind _ p).trans (step_success g x s T [] A G p j hv).1)]
    change (match evV g x s T [pre x p q] (.param 0) j with
      | some (some z) => evV g x s T [pre x p q] b z | other => other)=_
    rw [hreplay,hword,hverify]
    by_cases he : ws++[v]=List.replicate (ws.length+1) u
    · rw [if_pos he]
      exact (evV_seq_ok ((hind _ q).trans har)).symm
    · rw [if_neg he]

def probe (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (A G : MExp) (p : Nat) : Res :=
  match evV g x s T [] (step A G) p with
  | some none => some (some p)
  | some (some _) => match evV g x s T [] A p with
    | some (some j) => evV g x s T [pre x p j] (verifier (step A G)) j
    | other => other
  | none => none

/-- Successful arguments preserve the selected endpoint and whole capture.
The initial test separates zero iterations without examining later words. -/
theorem actual_entry (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (A G : MExp) (hA : A.FirstOrder) (hG : G.FirstOrder)
    (hind : ∀ E z, evV g x s T E A z=evV g x s T [] A z)
    (hinds : ∀ E z, evV g x s T E (step A G) z=evV g x s T [] (step A G) z)
    {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (hcode : ∀ p q, p≤x.length → evV g x s T [] A p=some (some q) → C (pre x p q))
    (p q : Nat) (hp : p≤x.length)
    (hb : evV g x s T [] (argument A G) p=some (some q)) (b : MExp) :
    evV g x s T [pre x p q] (.seq A (.seq (.param 0) b)) p=
      match probe g x s T A G p with
      | some (some _) => evV g x s T [pre x p q] (.seq A b) q
      | other => other := by
  cases hf : evV g x s T [] (step A G) p with
  | none =>
    change evStar (fun z => evV g x s T [] (step A G) z) p=some (some q) at hb
    rw [evStar_none hf] at hb
    cases hb
  | some result => cases result with
    | none =>
      have he : p=q := by
        change evStar (fun z => evV g x s T [] (step A G) z) p=some (some q) at hb
        rw [evStar_fail hf] at hb
        simpa using hb
      subst q
      simp only [probe,hf,pre,Nat.sub_self,List.take_zero]
      cases ha : evV g x s T [[]] A p with
      | none => rw [evV_seq_none ha,evV_seq_none ha]
      | some result => cases result with
        | none => rw [evV_seq_fail ha,evV_seq_fail ha]
        | some j =>
          have hj : j≤x.length := (WordStarFilter.success_prefix hs hT [[]] A hA p j hp ha).1
          rw [evV_seq_ok ha,evV_seq_ok ha]
          have hempty : evV g x s T [[]] (.param 0) j=some (some j) := by
            simp [evV,Shallot.stripPrefix?,length_sfx x hj]
          rw [evV_seq_ok hempty]
    | some j =>
      have ha := (step_success g x s T [] A G p j hf).1
      simpa only [probe,hf,ha] using nonempty_entry g x s hs T hT A G hA hG hind hinds hc hcode p q j hp hf hb b

end Shallot.MacroPeg.CBV.SelectedCodewordVerification
