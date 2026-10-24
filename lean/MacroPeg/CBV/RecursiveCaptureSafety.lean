import MacroPeg.CBV.TotalCaptureSafety
import MacroPeg.CBV.RecursiveParserStability
import MacroPeg.CBV.DependentCaptureFilter

namespace Shallot.MacroPeg.CBV.RecursiveCaptureSafety
open TotalCaptureSafety
open ClockFreezing (Table)

/-- A finite check of consuming paths; queries preserve their original
semantics and need no termination or successful-capture assumptions. -/
def check {n : Nat} (M : StatefulScanner.Machine n) (size : Nat) : MExp → Bool
  | .call i [] => decide (i<size)
  | .eps | .notP _ | .param _ => true
  | .lit w => wordCheck M w
  | .seq a b | .alt a b => check M size a && check M size b
  | .star a => check M size a
  | _ => false

theorem check_sound {n : Nat} (M : StatefulScanner.Machine n) (size : Nat) :
    ∀ e, check M size e=true → SafeCalls M size e
  | .call i [], h => by
    change i<size
    exact of_decide_eq_true (show decide (i<size)=true from h)
  | .eps, _ | .notP _, _ | .param _, _ => True.intro
  | .lit w, h => wordCheck_sound M w h
  | .seq a b, h | .alt a b, h =>
    ⟨check_sound M size a (Bool.and_eq_true_iff.mp h).1,
      check_sound M size b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a, h => check_sound M size a h
  | .call _ (_::_), h | .chr _, h | .any, h | .range _ _, h | .dbg _, h
  | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => by cases h

def Component {n : Nat} (M : StatefulScanner.Machine n) (bodies : List MExp) : Prop :=
  ∀ b∈bodies, SafeCalls M bodies.length b

theorem component_check_sound {n : Nat} (M : StatefulScanner.Machine n) (bodies : List MExp)
    (h : bodies.all (check M bodies.length)=true) : Component M bodies := by
  intro b hb
  exact check_sound M bodies.length b ((List.all_eq_true.mp h) b hb)

/-- Actual physical helper rows derive the frontier invariant. The proof
covers mutual recursion and undefined cycles at every clock. -/
theorem physical_rows {n : Nat} (M : StatefulScanner.Machine n) (bodies : List MExp)
    (hB : Component M bodies) (g : MGrammar)
    (hg : RecursiveParserStability.Installed bodies g) (x : List Char) (s : Strategy) (k : Nat) :
    Rows M bodies.length x (tblV g x s k) := by
  have hInstalled : ∀ i, i<bodies.length → ∃ b, ruleAtM g.rules i=some ⟨0,b⟩ := by
    intro i hi
    exact ⟨bodies[i],hg i bodies[i] (List.getElem?_eq_getElem hi)⟩
  induction k with
  | zero => intro i hi p q hp h; simp [tblV,valAt_nil] at h
  | succ k ih =>
    intro i hi p q hp h
    have hb := List.getElem?_eq_getElem hi
    rw [valAt_tblV_succ (hg i bodies[i] hb) [] hp] at h
    exact suffix_shape_calls M g x s (tblV g x s k) [] (by intro w hw; cases hw)
      bodies.length ih hInstalled bodies[i] (hB _ (List.mem_of_getElem? hb)) p q hp h

/-- Freezing an actual helper prefix preserves capture safety at every
user clock; no stabilization or parser-totality premise is needed here. -/
theorem frozen_rows {n : Nat} (M : StatefulScanner.Machine n) (bodies : List MExp)
    (hB : Component M bodies) (g : MGrammar)
    (hg : RecursiveParserStability.Installed bodies g) (x : List Char) (s : Strategy)
    (pick : Nat → Bool) (floor k : Nat) (hPick : ∀ i, i<bodies.length → pick i=true) :
    Rows M bodies.length x (ClockFreezing.frozen g x s pick floor k) := by
  intro i hi p q hp h
  rw [ClockFreezing.frozen_rows g x s pick floor k i (hPick i hi) []] at h
  exact physical_rows M bodies hB g hg x s floor i hi p q hp h

theorem capture_of_rows {n : Nat} (M : StatefulScanner.Machine n) (size : Nat)
    (g : MGrammar) (installed : ∀ i, i<size → ∃ b, ruleAtM g.rules i=some ⟨0,b⟩)
    (x : List Char) (s : Strategy) (T : Table) (hRows : Rows M size x T)
    (E : List (List Char)) (hE : Environment M E)
    (e : MExp) (he : SafeCalls M size e) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E e p=some (some q)) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q := by
  obtain ⟨hqp,w,hw,hs⟩ := suffix_shape_calls M g x s T E hE size hRows installed e he p q hp h
  have hpw : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using
      pre_eq (sfx_is_suffix x p) hs
  exact ⟨hpw.symm ▸ hw,hpw.symm ▸ hs⟩

theorem capture {n : Nat} (M : StatefulScanner.Machine n) (bodies : List MExp)
    (hB : Component M bodies) (g : MGrammar)
    (hg : RecursiveParserStability.Installed bodies g) (x : List Char) (s : Strategy)
    (k : Nat) (E : List (List Char)) (hE : Environment M E)
    (e : MExp) (he : SafeCalls M bodies.length e) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s (tblV g x s k) E e p=some (some q)) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q := by
  obtain ⟨hqp,w,hw,hs⟩ := suffix_shape_calls M g x s _ E hE bodies.length
    (physical_rows M bodies hB g hg x s k)
    (fun i hi => ⟨bodies[i],hg i bodies[i] (List.getElem?_eq_getElem hi)⟩) e he p q hp h
  have hpw : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using
      pre_eq (sfx_is_suffix x p) hs
  exact ⟨hpw.symm ▸ hw,hpw.symm ▸ hs⟩

theorem frozen_capture {n : Nat} (M : StatefulScanner.Machine n) (bodies : List MExp)
    (hB : Component M bodies) (g : MGrammar)
    (hg : RecursiveParserStability.Installed bodies g) (x : List Char) (s : Strategy)
    (pick : Nat → Bool) (floor k : Nat) (hPick : ∀ i, i<bodies.length → pick i=true)
    (E : List (List Char)) (hE : Environment M E)
    (e : MExp) (he : SafeCalls M bodies.length e) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s (ClockFreezing.frozen g x s pick floor k) E e p=some (some q)) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q :=
  capture_of_rows M bodies.length g
    (fun i hi => ⟨bodies[i],hg i bodies[i] (List.getElem?_eq_getElem hi)⟩)
    x s _ (frozen_rows M bodies hB g hg x s pick floor k hPick) E hE e he p q hp h

/-- Original recursive nodes precede their generated observer products and
any user rules. Their consuming-path certificate needs no product invariant. -/
theorem nodes_installed (nodes : List RegularCaptureProduct.Node)
    (D : RegularCaptureProduct.Machine) (extra : List MRule) :
    RecursiveParserStability.Installed (nodes.map RegularCaptureProduct.body)
      (FilteredOverlapCaller.extend nodes D extra) := by
  intro i b hb
  have hlen : i<nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hb).1
    simpa using this
  have hn : nodes[i]?=some nodes[i] := List.getElem?_eq_getElem hlen
  have he : RegularCaptureProduct.body nodes[i]=b := by
    simpa [List.getElem?_map,hn] using hb
  subst b
  have hr := RegularCaptureProduct.original_rule nodes D i nodes[i] hn
  rw [ruleAtM_eq_getElem?] at hr
  unfold FilteredOverlapCaller.extend
  rw [ruleAtM_eq_getElem?,List.getElem?_append_left]
  · exact hr
  · have := (List.getElem?_eq_some_iff.mp (show (RegularCaptureProduct.grammar nodes D).rules[i]?=
        some ⟨0,RegularCaptureProduct.body nodes[i]⟩ from hr)).1
    exact this

end Shallot.MacroPeg.CBV.RecursiveCaptureSafety
