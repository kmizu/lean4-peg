import MacroPeg.CBV.DelimitedCopySyntax

namespace Shallot.MacroPeg.CBV.DelimitedCopyEvaluation
open DelimitedCopySyntax DelimiterTemplate DelimitedCopyTemplates
open ClockFreezing (Table)

/-- Pure user rows are unresolved at clock zero and fully defined thereafter. -/
def result (k : Nat) (v : Option (List Char)) : Res := match k with
  | 0 => none | _+1 => some (v.map List.length)

theorem source_row (bodies : List MExp) (d : Char) (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (tblV (source bodies d) x .callByValuePar k bodies.length E) p=
      result k (run d E (sourceBlockParts d) (sfx x p)) := by
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ (source_rule bodies d) E hp,compile_eval] <;> first | rfl | exact hp

theorem short_row (bodies : List MExp) (d : Char) (x : List Char) (k : Nat) (u : List Char) (p : Nat) (hp : p≤x.length) :
    valAt (tblV (target bodies d) x .callByValueSeq k bodies.length [u]) p=
      result k (run d [u] (shortBlockParts d) (sfx x p)) := by
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ (short_rule bodies d) [u] hp,compile_eval] <;> first | rfl | exact hp

theorem long_row (bodies : List MExp) (d : Char) (x : List Char) (k : Nat) (v : List Char) (p : Nat) (hp : p≤x.length) :
    valAt (tblV (target bodies d) x .callByValueSeq k (bodies.length+1) [v]) p=
      result k (run d [v] (longBlockParts d) (sfx x p)) := by
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ (long_rule bodies d) [v] hp,compile_eval] <;> first | rfl | exact hp

theorem short_call (bodies : List MExp) (d : Char) (x : List Char) (k p q : Nat) (hq : q≤x.length) (A : MExp)
    (hA : evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] A p=some (some q)) :
    evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (.call bodies.length [A]) p=
      result k (run d [pre x p q] (shortBlockParts d) (sfx x q)) := by
  rw [evV_call_seq (short_rule bodies d) rfl,evSeq_cons_ok hA,evSeq_nil]
  exact short_row bodies d x k _ q hq

theorem long_call (bodies : List MExp) (d : Char) (x : List Char) (k p q : Nat) (hq : q≤x.length) (B : MExp)
    (hB : evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] B p=some (some q)) :
    evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (.call (bodies.length+1) [B]) p=
      result k (run d [pre x p q] (longBlockParts d) (sfx x q)) := by
  rw [evV_call_seq (long_rule bodies d) rfl,evSeq_cons_ok hB,evSeq_nil]
  exact long_row bodies d x k _ q hq

/-- The original left-to-right actual preflight precedes both projections.
It is essential even at clock zero and when a later actual is undefined. -/
theorem physical (bodies : List MExp) (alphabet : List Char) (d : Char) (A B : MExp)
    (hc : Checked bodies alphabet d A B) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source bodies d) x .callByValuePar (tblV (source bodies d) x .callByValuePar k) [] (root bodies A B) p=
      evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (targetRoot bodies A B) p := by
  have hA := queries_eq bodies d hc.library A hc.left x k p hp
  have hB := queries_eq bodies d hc.library B hc.right x k p hp
  have hFO := source_firstOrder bodies d hc.library
  have haFO := RecursiveParserStability.lexical_firstOrder _ A hc.left
  have hbFO := RecursiveParserStability.lexical_firstOrder _ B hc.right
  rw [root,evV_call_par (source_rule bodies d) rfl (by decide)]
  unfold targetRoot
  change (match evParArgs (source bodies d) x .callByValuePar (tblV (source bodies d) x .callByValuePar k) [] [A,B] p with
    | some (some W) => valAt (tblV (source bodies d) x .callByValuePar k bodies.length W) p | some none => some none | none => none)=
    (match evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (.andP A) p with
      | some (some q) => evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) []
        (.seq (.andP B) (.seq (.andP (.call bodies.length [A])) (.call (bodies.length+1) [B]))) q | other => other)
  rw [CallLookahead.evV_peek,←hA]
  cases ha : evV (source bodies d) x .callByValuePar (tblV (source bodies d) x .callByValuePar k) [] A p with
  | none => rw [evPar_cons_none ha]; rfl
  | some va => cases va with
    | none => rw [evPar_cons_fail ha]; rfl
    | some a =>
      rw [evPar_cons_ok ha]
      dsimp only [CallLookahead.peek]
      change _=(match evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (.andP B) p with
        | some (some q) => evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) []
          (.seq (.andP (.call bodies.length [A])) (.call (bodies.length+1) [B])) q | other => other)
      rw [CallLookahead.evV_peek,←hB]
      cases hb : evV (source bodies d) x .callByValuePar (tblV (source bodies d) x .callByValuePar k) [] B p with
      | none => rw [evPar_cons_none hb]; rfl
      | some vb => cases vb with
        | none => rw [evPar_cons_fail hb]; rfl
        | some b =>
          rw [evPar_cons_ok hb,evPar_nil]
          dsimp only [CallLookahead.peek]
          have ha' := evV_ok (tblV_ok _ _ _ k) A p hp a ha
          have hb' := evV_ok (tblV_ok _ _ _ k) B p hp b hb
          have hcapA := ReplayFusion.success_prefix (tblV_sound hFO (by decide) k) [] A haFO p a hp ha
          have hcapB := ReplayFusion.success_prefix (tblV_sound hFO (by decide) k) [] B hbFO p b hp hb
          have hfreeA := CaptureDelimiterSafety.captured_free (source_installed bodies d) hFO _ alphabet hc.valid d hc.separator A hc.safeLeft haFO x .callByValuePar (by decide) k p a hp ha
          have hfreeB := CaptureDelimiterSafety.captured_free (source_installed bodies d) hFO _ alphabet hc.valid d hc.separator B hc.safeRight hbFO x .callByValuePar (by decide) k p b hp hb
          rw [source_row bodies d x k _ p hp]
          change _=(match evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (.andP (.call bodies.length [A])) p with
            | some (some q) => evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] (.call (bodies.length+1) [B]) q | other => other)
          rw [CallLookahead.evV_peek,short_call bodies d x k p a ha' A (hA.symm.trans ha)]
          have he := block_run_eq d (sfx x p) (pre x p a) (pre x p b) (sfx x a) (sfx x b) hfreeA hfreeB hcapA.2 hcapB.2
          rw [he]
          cases k with
          | zero => rfl
          | succ k =>
            cases hs : run d [pre x p a] (shortBlockParts d) (sfx x a) with
            | none => simp [result,hs,CallLookahead.peek]
            | some rest =>
              simp only [result,hs,Option.map_some,Option.bind_some,CallLookahead.peek]
              rw [long_call bodies d x (k+1) p b hb' B (hB.symm.trans hb)]
              rfl

end Shallot.MacroPeg.CBV.DelimitedCopyEvaluation
