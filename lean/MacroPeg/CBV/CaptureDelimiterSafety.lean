import MacroPeg.CBV.DelimitedCopyTemplates
import MacroPeg.CBV.MaskedScannerAbsorption

namespace Shallot.MacroPeg.CBV.CaptureDelimiterSafety
open RecursiveParserStability (Installed)
open MaskedScannerAbsorption (Safe Valid enabled)
open NestedScannerArguments (accepts)
open ClockFreezing (Table)
open DelimitedCopyProjection (Free)

/-- A consumed prefix cannot pass a nonalphabet character if the maximal
alphabet suffix is unchanged. No maximal-endpoint assumption is required. -/
theorem all_of_drop_eq (A : List Char) : ∀ w rest : List Char,
    (w++rest).dropWhile (accepts A)=rest.dropWhile (accepts A) → w.all (accepts A)=true
  | [],_,_ => rfl
  | c::w,rest,h => by
    cases hc : accepts A c with
    | false =>
      have he : (c::w++rest).length=(rest.dropWhile (accepts A)).length := congrArg List.length (by simpa [List.dropWhile_cons,hc] using h)
      have hl := (List.dropWhile_suffix (accepts A) (l := rest)).length_le
      simp only [List.length_cons,List.length_append] at he
      omega
    | true =>
      have ht := all_of_drop_eq A w rest (by simpa [List.dropWhile_cons,hc] using h)
      simp [hc,ht]

theorem captured_free {bodies : List MExp} {g : MGrammar} (hg : Installed bodies g) (hFO : g.FirstOrder)
    (mask : List Bool) (A : List Char) (hmask : Valid bodies mask A)
    (d : Char) (hd : d∉A) (e : MExp) (he : Safe mask A e) (heFO : e.FirstOrder)
    (x : List Char) (s : Strategy) (hs : s≠.callByName) (k p q : Nat) (hp : p≤x.length)
    (hv : evV g x s (tblV g x s k) [] e p=some (some q)) : Free d (pre x p q) := by
  have hi : ∀ i, enabled mask i=true → ∃ b, ruleAtM g.rules i=some ⟨0,b⟩ := by
    intro i he
    exact ⟨bodies[i]'(hmask.1 i he),hg i _ (List.getElem?_eq_getElem (hmask.1 i he))⟩
  have hdrop := MaskedScannerAbsorption.evaluator_safe mask hi A x s (tblV g x s k)
    (MaskedScannerAbsorption.physical_rows hg mask A hmask x s k) (tblV_ok g x s k) [] e he p q hp hv
  have hcap := DependentCaptureFilter.success_prefix hs (tblV_sound hFO hs k) [] e heFO p q hp hv
  rw [hcap.2] at hdrop
  have hall := all_of_drop_eq A (pre x p q) (sfx x q) hdrop
  intro hm
  have hb := List.all_eq_true.mp hall d hm
  exact hd ((NestedScannerArguments.accepts_iff_mem A d).mp hb)

end Shallot.MacroPeg.CBV.CaptureDelimiterSafety
