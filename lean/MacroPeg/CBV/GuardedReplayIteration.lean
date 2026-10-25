import MacroPeg.CBV.CaptureOriginRewrite
import MacroPeg.CBV.BlockCapture
import MacroPeg.CBV.SequenceArguments
import MacroPeg.CBV.PrefixCaptureQuery

namespace Shallot.MacroPeg.CBV.GuardedReplayIteration
open ClockFreezing (Table)

def step (u : List Char) : MExp := .seq (.lit u) (.andP (.param 0))
def header (u : List Char) : MExp := .seq (.star (step u)) (.param 0)

private theorem literal_length (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (u : List Char) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T E (.lit u) p=some (some q)) : q≤x.length ∧ p=u.length+q := by
  obtain ⟨hq,he⟩ := SequenceArguments.success_prefix g x s T E (.lit u) True.intro p q hp hv
  have hw : u=pre x p q := by
    simpa [WordArguments.value] using WordArguments.value_of_success g x s T E (.lit u) True.intro p q hp hv
  rw [←hw] at he
  have hl := congrArg List.length he
  rw [length_sfx x hp,List.length_append,length_sfx x hq] at hl
  exact ⟨hq,hl⟩

/-- A complete residual word equation transports arbitrarily many guarded
prefix iterations to the real capture endpoint. Zero-length iterations
remain undefined on both sides; no totality hypothesis is used. -/
theorem rotate (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w u v : List Char) (hrot : u++w=w++v) :
    ∀ p q, p≤x.length → evV g x s T [w] (.param 0) p=some (some q) →
    evV g x s T [w] (header u) p=evV g x s T [w] (.star (.lit v)) q := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro q hp ha
    have hlength := literal_length g x s T [w] w p q hp ha
    have ht := BlockCapture.prefix_rotate g x s T w u v hrot p
    rw [evV_seq_ok ha] at ht
    cases hb : evV g x s T [w] (.lit u) p with
    | none =>
      have hstep : evV g x s T [w] (step u) p=none := evV_seq_none hb
      have hc : evV g x s T [w] (.lit v) q=none := ht.symm.trans (evV_seq_none hb)
      rw [header,evV_seq_none (show evV g x s T [w] (.star (step u)) p=none from evStar_none hstep)]
      rw [evV_star,evStar_none hc]
    | some result => cases result with
      | none =>
        have hstep : evV g x s T [w] (step u) p=some none := evV_seq_fail hb
        have hc : evV g x s T [w] (.lit v) q=some none := ht.symm.trans (evV_seq_fail hb)
        rw [header,evV_seq_ok (show evV g x s T [w] (.star (step u)) p=some (some p) from evStar_fail hstep),ha]
        rw [evV_star,evStar_fail hc]
      | some j =>
        have hj := literal_length g x s T [w] u p j hp hb
        rw [evV_seq_ok hb] at ht
        cases had : evV g x s T [w] (.param 0) j with
        | none =>
          have hlook : evV g x s T [w] (.andP (.param 0)) j=none := by rw [CallLookahead.evV_peek,had]; rfl
          have hstep : evV g x s T [w] (step u) p=none := by rw [step,evV_seq_ok hb,hlook]
          have hc : evV g x s T [w] (.lit v) q=none := ht.symm.trans had
          rw [header,evV_seq_none (show evV g x s T [w] (.star (step u)) p=none from evStar_none hstep)]
          rw [evV_star,evStar_none hc]
        | some result => cases result with
          | none =>
            have hlook : evV g x s T [w] (.andP (.param 0)) j=some none := by rw [CallLookahead.evV_peek,had]; rfl
            have hstep : evV g x s T [w] (step u) p=some none := by rw [step,evV_seq_ok hb,hlook]
            have hc : evV g x s T [w] (.lit v) q=some none := ht.symm.trans had
            rw [header,evV_seq_ok (show evV g x s T [w] (.star (step u)) p=some (some p) from evStar_fail hstep),ha]
            rw [evV_star,evStar_fail hc]
          | some r =>
            have hlook : evV g x s T [w] (.andP (.param 0)) j=some (some j) := by rw [CallLookahead.evV_peek,had]; rfl
            have hstep : evV g x s T [w] (step u) p=some (some j) := by rw [step,evV_seq_ok hb,hlook]
            have hc : evV g x s T [w] (.lit v) q=some (some r) := ht.symm.trans had
            have hr := literal_length g x s T [w] w j r hj.1 had
            by_cases hstrict : j<p
            · have hstrict' : r<q := by omega
              change (match evStar (fun z => evV g x s T [w] (step u) z) p with
                | some (some z) => evV g x s T [w] (.param 0) z | other => other)=_
              rw [evStar_ok hstep hstrict]
              change evV g x s T [w] (header u) j=_
              rw [evV_star,evStar_ok hc hstrict']
              exact ih j hstrict r hj.1 had
            · have hstrict' : ¬r<q := by omega
              rw [header,evV_seq_none (show evV g x s T [w] (.star (step u)) p=none from evStar_stuck hstep hstrict)]
              rw [evV_star,evStar_stuck hc hstrict']

private theorem unary_overlap (c : Char) : ∀ w tail rest : List Char,
    w++tail=c::(w++rest) → w=List.replicate w.length c
  | [],_,_,_ => rfl
  | d::w,tail,rest,h => by
    have hd : d=c := (List.cons.inj h).1
    subst d
    have hr := (List.cons.inj h).2
    simpa [List.replicate_succ] using congrArg (List.cons c) (unary_overlap c w tail rest hr)

private theorem step_factor (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (c : Char) (p : Nat) :
    evV g x s T E (step [c]) p=
      evV g x s T E (.seq (.andP (.seq (.lit [c]) (.param 0))) (.lit [c])) p := by
  let L : Nat → MExp := fun i => if i=0 then .lit [c] else .seq (.lit [c]) (.param 0)
  exact PrefixCaptureQuery.prefix_query g x s T E (.lit [c]) (.param 0) true L 0 1 p rfl rfl

/-- For an actual captured prefix, one successful unary shift forces the
whole value to commute with that character. No finite palette is assumed. -/
theorem commute_of_first (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w : List Char) (c : Char) (p j : Nat) (hp : p≤x.length)
    (hcap : w.IsPrefix (sfx x p))
    (hfirst : evV g x s T [w] (.seq (.lit [c]) (.param 0)) p=some (some j)) : [c]++w=w++[c] := by
  have hs := (SequenceArguments.success_prefix g x s T [w]
    (.seq (.lit [c]) (.param 0)) ⟨True.intro,True.intro⟩ p j hp hfirst).2
  have hw : [c]++w=pre x p j := by
    simpa [WordArguments.value] using WordArguments.value_of_success g x s T [w]
      (.seq (.lit [c]) (.param 0)) ⟨True.intro,True.intro⟩ p j hp hfirst
  rw [←hw] at hs
  obtain ⟨tail,ht⟩ := hcap
  have he : w++tail=c::(w++sfx x j) := by simpa using ht.trans hs
  have hu := unary_overlap c w tail (sfx x j) he
  rw [hu,←List.replicate_one,List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm]

/-- An unbounded retained-value guarded prefix reduces to one fixed-shift
branch followed by a greedy residual scan, or an unchanged whole replay.
The branch is decided before the continuation is evaluated. -/
theorem header_result (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w : List Char) (c : Char) (p : Nat) (hp : p≤x.length) (hcap : w.IsPrefix (sfx x p)) :
    evV g x s T [w] (header [c]) p=
      match evV g x s T [w] (.seq (.lit [c]) (.param 0)) p with
      | none => none
      | some none => evV g x s T [w] (.param 0) p
      | some (some j) => evV g x s T [w] (.star (.lit [c])) j := by
  obtain ⟨tail,ht⟩ := hcap
  have ha : evV g x s T [w] (.param 0) p=some (some tail.length) := by
    simp [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr ht.symm]
  have hf := step_factor g x s T [w] c p
  cases hh : evV g x s T [w] (.seq (.lit [c]) (.param 0)) p with
  | none =>
    have hl : evV g x s T [w] (.andP (.seq (.lit [c]) (.param 0))) p=none := by rw [CallLookahead.evV_peek,hh]; rfl
    have hs : evV g x s T [w] (step [c]) p=none := hf.trans (evV_seq_none hl)
    exact evV_seq_none (show evV g x s T [w] (.star (step [c])) p=none from evStar_none hs)
  | some v => cases v with
    | none =>
      have hl : evV g x s T [w] (.andP (.seq (.lit [c]) (.param 0))) p=some none := by rw [CallLookahead.evV_peek,hh]; rfl
      have hs : evV g x s T [w] (step [c]) p=some none := hf.trans (evV_seq_fail hl)
      exact (evV_seq_ok (show evV g x s T [w] (.star (step [c])) p=some (some p) from evStar_fail hs))
    | some j =>
      have hrot := commute_of_first g x s T w c p j hp ⟨tail,ht⟩ hh
      have he := BlockCapture.prefix_rotate g x s T w [c] [c] hrot p
      rw [evV_seq_ok ha] at he
      have hc : evV g x s T [w] (.lit [c]) tail.length=some (some j) := he.symm.trans hh
      have hq := (literal_length g x s T [w] w p tail.length hp ha).1
      have hlen := literal_length g x s T [w] [c] tail.length j hq hc
      have hstrict : j<tail.length := by simp only [List.length_singleton] at hlen; omega
      rw [rotate g x s T w [c] [c] hrot p tail.length hp ha,evV_star,evStar_ok hc hstrict]
      rfl

def normalized (c : Char) (tail : MExp) : MExp :=
  let first := .seq (.lit [c]) (.param 0)
  RootObservation.branch (.andP first) (.seq first (.seq (.star (.lit [c])) tail)) (.seq (.param 0) tail)

theorem body_result (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w : List Char) (c : Char) (tail : MExp) (p : Nat) (hp : p≤x.length)
    (hcap : w.IsPrefix (sfx x p)) :
    evV g x s T [w] (.seq (header [c]) tail) p=evV g x s T [w] (normalized c tail) p := by
  rw [normalized,ChoiceArguments.branch_eval]
  have hh := header_result g x s T w c p hp hcap
  cases hf : evV g x s T [w] (.seq (.lit [c]) (.param 0)) p with
  | none =>
    rw [hf] at hh
    rw [evV_seq_none hh]
  | some v => cases v with
    | none =>
      rw [hf] at hh
      change (match evV g x s T [w] (header [c]) p with
        | some (some j) => evV g x s T [w] tail j | other => other)=_
      rw [hh]
      rfl
    | some j =>
      rw [hf] at hh
      rw [evV_seq_ok hf]
      change (match evV g x s T [w] (header [c]) p with
        | some (some r) => evV g x s T [w] tail r | other => other)=_
      rw [hh]
      rfl

private theorem parameter_environment (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (w : List Char) (hw : E[0]?=some w) (p : Nat) :
    evV g x s T E (.param 0) p=evV g x s T [w] (.param 0) p := by simp only [evV,hw,List.getElem?_cons_zero]

private theorem first_environment (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (w u : List Char) (hw : E[0]?=some w) (p : Nat) :
    evV g x s T E (.seq (.lit u) (.param 0)) p=evV g x s T [w] (.seq (.lit u) (.param 0)) p := by
  change (match evV g x s T E (.lit u) p with
    | some (some q) => evV g x s T E (.param 0) q | other => other)=_
  cases hv : evV g x s T E (.lit u) p with
  | none => rw [evV_seq_none (show evV g x s T [w] (.lit u) p=none from hv)]
  | some v => cases v with
    | none => rw [evV_seq_fail (show evV g x s T [w] (.lit u) p=some none from hv)]
    | some q =>
      rw [evV_seq_ok (show evV g x s T [w] (.lit u) p=some (some q) from hv)]
      exact parameter_environment g x s T E w hw q

private theorem header_environment (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (w u : List Char) (hw : E[0]?=some w) (p : Nat) :
    evV g x s T E (header u) p=evV g x s T [w] (header u) p := by
  have hs (q : Nat) : evV g x s T E (step u) q=evV g x s T [w] (step u) q := by
    change (match evV g x s T E (.lit u) q with
      | some (some j) => evV g x s T E (.andP (.param 0)) j | other => other)=_
    cases hv : evV g x s T E (.lit u) q with
    | none => rw [step,evV_seq_none (show evV g x s T [w] (.lit u) q=none from hv)]
    | some v => cases v with
      | none => rw [step,evV_seq_fail (show evV g x s T [w] (.lit u) q=some none from hv)]
      | some j =>
        rw [step,evV_seq_ok (show evV g x s T [w] (.lit u) q=some (some j) from hv)]
        change evV g x s T E (.andP (.param 0)) j=evV g x s T [w] (.andP (.param 0)) j
        rw [CallLookahead.evV_peek,CallLookahead.evV_peek,parameter_environment g x s T E w hw j]
  have hstar : evV g x s T E (.star (step u)) p=evV g x s T [w] (.star (step u)) p :=
    evStar_congr p (fun q _ => hs q)
  change (match evV g x s T E (.star (step u)) p with
    | some (some q) => evV g x s T E (.param 0) q | other => other)=_
  rw [hstar]
  cases hv : evV g x s T [w] (.star (step u)) p with
  | none => rw [header,evV_seq_none hv]
  | some v => cases v with
    | none => rw [header,evV_seq_fail hv]
    | some q => rw [header,evV_seq_ok hv]; exact parameter_environment g x s T E w hw q

theorem body_result_captured (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (c : Char) (tail : MExp) (p : Nat) (hp : p≤x.length)
    (hE : CaptureOriginRewrite.Captured x E p) :
    evV g x s T E (.seq (header [c]) tail) p=evV g x s T E (normalized c tail) p := by
  cases E with
  | nil =>
    have hs : evV g x s T [] (step [c]) p=some none := by
      simp only [step,MExp.andP,evV,List.getElem?_nil]
      cases Shallot.stripPrefix? [c] (sfx x p) <;> rfl
    have hh : evV g x s T [] (header [c]) p=some none := by
      rw [header,evV_seq_ok (show evV g x s T [] (.star (step [c])) p=some (some p) from evStar_fail hs)]
      rfl
    have hf : evV g x s T [] (.seq (.lit [c]) (.param 0)) p=some none := by
      simp only [evV,List.getElem?_nil]
      cases Shallot.stripPrefix? [c] (sfx x p) <;> rfl
    rw [evV_seq_fail hh,normalized,ChoiceArguments.branch_eval,hf]
    rfl
  | cons w W =>
    have hw : (w::W)[0]?=some w := rfl
    have hh := header_result g x s T w c p hp (hE w (by simp))
    rw [←header_environment g x s T (w::W) w [c] hw p,
      ←first_environment g x s T (w::W) w [c] hw p,
      ←parameter_environment g x s T (w::W) w hw p] at hh
    have hscan (q : Nat) : evV g x s T [w] (.star (.lit [c])) q=evV g x s T (w::W) (.star (.lit [c])) q := rfl
    simp only [hscan] at hh
    rw [normalized,ChoiceArguments.branch_eval]
    cases hf : evV g x s T (w::W) (.seq (.lit [c]) (.param 0)) p with
    | none => rw [hf] at hh; rw [evV_seq_none hh]
    | some v => cases v with
      | none =>
        rw [hf] at hh
        change (match evV g x s T (w::W) (header [c]) p with
          | some (some j) => evV g x s T (w::W) tail j | other => other)=_
        rw [hh]
        rfl
      | some j =>
        rw [hf] at hh
        rw [evV_seq_ok hf]
        change (match evV g x s T (w::W) (header [c]) p with
          | some (some r) => evV g x s T (w::W) tail r | other => other)=_
        rw [hh]
        rfl

end Shallot.MacroPeg.CBV.GuardedReplayIteration
