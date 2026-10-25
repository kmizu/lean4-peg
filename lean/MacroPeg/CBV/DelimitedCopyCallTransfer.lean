import MacroPeg.CBV.DelimitedCopyEvaluation

namespace Shallot.MacroPeg.CBV.DelimitedCopyCallTransfer
open DelimitedCopySyntax DelimiterTemplate DelimitedCopyTemplates
open ClockFreezing (Table)

abbrev result := DelimitedCopyEvaluation.result

def head (n : Nat) (A B : MExp) : MExp := .call n [A,B]
def targetHead (n : Nat) (A B : MExp) : MExp :=
  .seq (.andP A) (.seq (.andP B) (.seq (.andP (.call n [A])) (.call (n+1) [B])))

theorem source_row (g : MGrammar) (n : Nat) (d : Char) (x : List Char) (k : Nat) (hr : ruleAtM g.rules n=some ⟨2,compile d (sourceBlockParts d)⟩) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (tblV g x .callByValuePar k n E) p=
      result k (run d E (sourceBlockParts d) (sfx x p)) := by
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr E hp,compile_eval] <;> first | rfl | exact hp

theorem short_row (g : MGrammar) (n : Nat) (d : Char) (x : List Char) (k : Nat) (hr : ruleAtM g.rules n=some ⟨1,compile d (shortBlockParts d)⟩) (u : List Char) (p : Nat) (hp : p≤x.length) :
    valAt (tblV g x .callByValueSeq k n [u]) p=
      result k (run d [u] (shortBlockParts d) (sfx x p)) := by
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr [u] hp,compile_eval] <;> first | rfl | exact hp

theorem long_row (g : MGrammar) (n : Nat) (d : Char) (x : List Char) (k : Nat) (hr : ruleAtM g.rules (n+1)=some ⟨1,compile d (longBlockParts d)⟩) (v : List Char) (p : Nat) (hp : p≤x.length) :
    valAt (tblV g x .callByValueSeq k (n+1) [v]) p=
      result k (run d [v] (longBlockParts d) (sfx x p)) := by
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr [v] hp,compile_eval] <;> first | rfl | exact hp

theorem short_call (g : MGrammar) (n : Nat) (d : Char) (x : List Char) (k p q : Nat) (hq : q≤x.length) (hr : ruleAtM g.rules n=some ⟨1,compile d (shortBlockParts d)⟩) (A : MExp)
    (hA : evV g x .callByValueSeq (tblV g x .callByValueSeq k) [] A p=some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq k) [] (.call n [A]) p=
      result k (run d [pre x p q] (shortBlockParts d) (sfx x q)) := by
  rw [evV_call_seq hr rfl,evSeq_cons_ok hA,evSeq_nil]
  exact short_row g n d x k hr _ q hq

theorem long_call (g : MGrammar) (n : Nat) (d : Char) (x : List Char) (k p q : Nat) (hq : q≤x.length) (hr : ruleAtM g.rules (n+1)=some ⟨1,compile d (longBlockParts d)⟩) (B : MExp)
    (hB : evV g x .callByValueSeq (tblV g x .callByValueSeq k) [] B p=some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq k) [] (.call (n+1) [B]) p=
      result k (run d [pre x p q] (longBlockParts d) (sfx x q)) := by
  rw [evV_call_seq hr rfl,evSeq_cons_ok hB,evSeq_nil]
  exact long_row g n d x k hr _ q hq

/-- Calls may occur inside transformed clients and inside actuals. Only
current actual-result equalities are premises; no independent-library or
fixed-point oracle is needed. Recursive correspondence discharges them. -/
theorem physical (g h : MGrammar) (n : Nat) (d : Char)
    (bodies : List MExp) (mask : List Bool) (alphabet : List Char)
    (hinst : RecursiveParserStability.Installed bodies g) (hgFO : g.FirstOrder)
    (hvalid : MaskedScannerAbsorption.Valid bodies mask alphabet) (hd : d∉alphabet)
    (A B C D : MExp) (hsA : MaskedScannerAbsorption.Safe mask alphabet A)
    (hsB : MaskedScannerAbsorption.Safe mask alphabet B) (haFO : A.FirstOrder) (hbFO : B.FirstOrder)
    (hsrc : ruleAtM g.rules n=some ⟨2,compile d (sourceBlockParts d)⟩)
    (hshort : ruleAtM h.rules n=some ⟨1,compile d (shortBlockParts d)⟩)
    (hlong : ruleAtM h.rules (n+1)=some ⟨1,compile d (longBlockParts d)⟩)
    (x : List Char) (k p : Nat) (hp : p≤x.length)
    (hA : evV g x .callByValuePar (tblV g x .callByValuePar k) [] A p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] C p)
    (hB : evV g x .callByValuePar (tblV g x .callByValuePar k) [] B p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] D p) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] (head n A B) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (targetHead n C D) p := by
  rw [head,evV_call_par hsrc rfl (by decide)]
  unfold targetHead
  change (match evParArgs g x .callByValuePar (tblV g x .callByValuePar k) [] [A,B] p with
    | some (some W) => valAt (tblV g x .callByValuePar k n W) p | some none => some none | none => none)=
    (match evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (.andP C) p with
      | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) []
        (.seq (.andP D) (.seq (.andP (.call n [C])) (.call (n+1) [D]))) q | other => other)
  rw [CallLookahead.evV_peek,←hA]
  cases ha : evV g x .callByValuePar (tblV g x .callByValuePar k) [] A p with
  | none => rw [evPar_cons_none ha]; rfl
  | some va => cases va with
    | none => rw [evPar_cons_fail ha]; rfl
    | some a =>
      rw [evPar_cons_ok ha]
      dsimp only [CallLookahead.peek]
      change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (.andP D) p with
        | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) []
          (.seq (.andP (.call n [C])) (.call (n+1) [D])) q | other => other)
      rw [CallLookahead.evV_peek,←hB]
      cases hb : evV g x .callByValuePar (tblV g x .callByValuePar k) [] B p with
      | none => rw [evPar_cons_none hb]; rfl
      | some vb => cases vb with
        | none => rw [evPar_cons_fail hb]; rfl
        | some b =>
          rw [evPar_cons_ok hb,evPar_nil]
          dsimp only [CallLookahead.peek]
          have ha' := evV_ok (tblV_ok _ _ _ k) A p hp a ha
          have hb' := evV_ok (tblV_ok _ _ _ k) B p hp b hb
          have hcapA := ReplayFusion.success_prefix (tblV_sound hgFO (by decide) k) [] A haFO p a hp ha
          have hcapB := ReplayFusion.success_prefix (tblV_sound hgFO (by decide) k) [] B hbFO p b hp hb
          have hfreeA := CaptureDelimiterSafety.captured_free hinst hgFO mask alphabet hvalid d hd A hsA haFO x .callByValuePar (by decide) k p a hp ha
          have hfreeB := CaptureDelimiterSafety.captured_free hinst hgFO mask alphabet hvalid d hd B hsB hbFO x .callByValuePar (by decide) k p b hp hb
          rw [source_row g n d x k hsrc _ p hp]
          change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (.andP (.call n [C])) p with
            | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (.call (n+1) [D]) q | other => other)
          rw [CallLookahead.evV_peek,short_call h n d x k p a ha' hshort C (hA.symm.trans ha)]
          have he := block_run_eq d (sfx x p) (pre x p a) (pre x p b) (sfx x a) (sfx x b) hfreeA hfreeB hcapA.2 hcapB.2
          rw [he]
          cases k with
          | zero => rfl
          | succ k =>
            cases hs : run d [pre x p a] (shortBlockParts d) (sfx x a) with
            | none => simp [result,DelimitedCopyEvaluation.result,hs,CallLookahead.peek]
            | some rest =>
              simp only [result,DelimitedCopyEvaluation.result,hs,Option.map_some,Option.bind_some,CallLookahead.peek]
              rw [long_call h n d x (k+1) p b hb' hlong D (hB.symm.trans hb)]
              rfl


end Shallot.MacroPeg.CBV.DelimitedCopyCallTransfer
