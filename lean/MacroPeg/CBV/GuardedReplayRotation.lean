import MacroPeg.CBV.BlockCapture
import MacroPeg.CBV.SequenceArguments

namespace Shallot.MacroPeg.CBV.GuardedReplayIteration
open ClockFreezing (Table)

def step (u : List Char) : MExp := .seq (.lit u) (.andP (.param 0))
def header (u : List Char) : MExp := .seq (.star (step u)) (.param 0)

theorem literal_length (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
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

end Shallot.MacroPeg.CBV.GuardedReplayIteration
