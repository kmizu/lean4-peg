import MacroPeg.CBV.PrefixCodeCapture

/-! Finite codeword sequences retain a runtime word representation after a
one-codeword shift. The count is a grammar parameter, not an input bound. -/
namespace Shallot.MacroPeg.CBV.CodewordReplay
open PrefixCodeCapture (PrefixFree)
open ClockFreezing (Table)

def power (u : List Char) (n : Nat) : List Char := (List.replicate n u).flatten

def replay : Nat → MExp
  | 0 => .lit []
  | n+1 => .seq (.param 0) (replay n)

def view (n : Nat) (b : MExp) : MExp := MExp.subst [replay n] b

theorem replay_word : ∀ n, WordArguments.Word (replay n)
  | 0 => trivial
  | n+1 => ⟨True.intro,replay_word n⟩

theorem replay_value (u : List Char) : ∀ n,
    WordArguments.value [u] (replay n)=some (power u n)
  | 0 => rfl
  | n+1 => by simp [replay,WordArguments.value,replay_value u n,power,List.replicate_succ]

theorem replay_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u : List Char) (n p : Nat) :
    evV g x s T [u] (replay n) p=evV g x s T [] (.lit (power u n)) p := by
  rw [WordArguments.word_eval _ x _ T [u] _ (replay_word n) p,replay_value]
  rfl

theorem view_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u : List Char) (n : Nat) (b : MExp) (hb : b.FirstOrder) (p : Nat) :
    evV g x s T [u] (view n b) p=evV g x s T [power u n] b p := by
  apply CaptureViews.evV_rebind [replay n] [power u n] _ b hb p
  intro k q
  cases k with
  | zero => rw [show MExp.subst [replay n] (.param 0)=replay n from rfl,replay_eval]; rfl
  | succ k => simp [MExp.subst,argAt,evV,MExp.failAlways]

/-- Unique prefix decoding works even when the compared encoding has more
codewords than the prefix being decoded, and when codewords are unbounded. -/
theorem decode_prefix {C : List Char → Prop} (hc : PrefixFree C) :
    ∀ (xs ys : List (List Char)) (rest : List Char),
      (∀ w∈xs, C w) → (∀ w∈ys, C w) → ys.length≤xs.length →
      xs.flatten.IsPrefix (ys.flatten++rest) → xs.take ys.length=ys
  | xs, [], rest, hx, hy, hn, hp => rfl
  | [], y::ys, rest, hx, hy, hn, hp => by simp at hn
  | x::xs, y::ys, rest, hx, hy, hn, hp => by
    have hxy : x=y := PrefixCodeCapture.prefix_identifies hc
      (hx x (by simp)) (hy y (by simp)) (by
        have hh := (show x.IsPrefix ((x::xs).flatten) from ⟨xs.flatten,rfl⟩).trans hp
        simpa only [List.flatten_cons,List.append_assoc] using hh)
    subst y
    have ht : xs.flatten.IsPrefix (ys.flatten++rest) := by
      apply (List.prefix_append_right_inj x).mp
      simpa only [List.flatten_cons,List.append_assoc] using hp
    have hi := decode_prefix hc xs ys rest (fun w hw => hx w (by simp [hw]))
      (fun w hw => hy w (by simp [hw])) (by simpa using hn) ht
    simpa only [List.length_cons,List.take_succ_cons] using congrArg (List.cons x) hi

/-- A one-position shift of a finite codeword list forces every word to
be the initial word. This is a list-level fact, independent of parsers. -/
theorem shift_forces_replicate (u : List Char) : ∀ vs : List (List Char),
    (u::vs).take vs.length=vs → vs=List.replicate vs.length u
  | [], h => rfl
  | v::vs, h => by
    simp only [List.length_cons,List.take_succ_cons,List.cons.injEq] at h
    obtain ⟨rfl,ht⟩ := h
    simpa only [List.length_cons,List.replicate_succ] using congrArg (List.cons u) (shift_forces_replicate u vs ht)

theorem source_prefix_forces {C : List Char → Prop} (hc : PrefixFree C)
    (u : List Char) (vs : List (List Char)) (rest : List Char)
    (hu : C u) (hv : ∀ v∈vs, C v)
    (h : (u++vs.flatten).IsPrefix (vs.flatten++rest)) : vs=List.replicate vs.length u := by
  apply shift_forces_replicate u vs
  exact decode_prefix hc (u::vs) vs rest
    (by intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hu; exact hv w hw)
    hv (by simp) h

theorem replay_prefix_forces {C : List Char → Prop} (hc : PrefixFree C)
    (u : List Char) (vs : List (List Char)) (rest : List Char)
    (hu : C u) (hv : ∀ v∈vs, C v)
    (h : (power u (vs.length+1)).IsPrefix (vs.flatten++rest)) : vs=List.replicate vs.length u := by
  have hd := decode_prefix hc (List.replicate (vs.length+1) u) vs rest
    (by intro w hw; have := List.mem_replicate.mp hw; simpa [this.2] using hu)
    hv (by simp) h
  simpa using hd.symm

/-- The source replay and the target's fixed-count repeated runtime word
have identical partial results and continuations after the first codeword. -/
theorem collapse (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    {C : List Char → Prop} (hc : PrefixFree C) (u : List Char) (vs : List (List Char))
    (rest : List Char) (hu : C u) (hv : ∀ v∈vs, C v) (p : Nat)
    (hs : sfx x p=vs.flatten++rest) (b : MExp) (hb : b.FirstOrder) :
    evV g x s T [u++vs.flatten] (.seq (.param 0) b) p=
      evV g x s T [u] (.seq (replay (vs.length+1)) (view (vs.length+1) b)) p := by
  by_cases he : vs=List.replicate vs.length u
  · have hw : u++vs.flatten=power u (vs.length+1) := by
      rw [he]
      simp [power,List.replicate_succ]
    rw [hw]
    have hr : evV g x s T [u] (replay (vs.length+1)) p=
        evV g x s T [power u (vs.length+1)] (.param 0) p := by
      rw [replay_eval]; rfl
    change (match evV g x s T [power u (vs.length+1)] (.param 0) p with
      | some (some q) => evV g x s T [power u (vs.length+1)] b q | other => other)=
      (match evV g x s T [u] (replay (vs.length+1)) p with
      | some (some q) => evV g x s T [u] (view (vs.length+1) b) q | other => other)
    rw [hr]
    cases evV g x s T [power u (vs.length+1)] (.param 0) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some q => exact (view_eval g x s T u _ b hb q).symm
  · have hsource : Shallot.stripPrefix? (u++vs.flatten) (vs.flatten++rest)=none := by
      cases h : Shallot.stripPrefix? (u++vs.flatten) (vs.flatten++rest) with
      | none => rfl
      | some r => exact False.elim (he (source_prefix_forces hc u vs rest hu hv
          ⟨r,((CBVtoCBN.stripPrefix_exact _ _ _).mp h).symm⟩))
    have htarget : Shallot.stripPrefix? (power u (vs.length+1)) (vs.flatten++rest)=none := by
      cases h : Shallot.stripPrefix? (power u (vs.length+1)) (vs.flatten++rest) with
      | none => rfl
      | some r => exact False.elim (he (replay_prefix_forces hc u vs rest hu hv
          ⟨r,((CBVtoCBN.stripPrefix_exact _ _ _).mp h).symm⟩))
    rw [evV_seq_fail (show evV g x s T [u++vs.flatten] (.param 0) p=some none by simp [evV,hs,hsource])]
    apply Eq.symm
    apply evV_seq_fail
    rw [replay_eval]
    simp [evV,hs,htarget]

end Shallot.MacroPeg.CBV.CodewordReplay
