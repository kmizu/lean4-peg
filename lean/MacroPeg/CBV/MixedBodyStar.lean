import MacroPeg.CBV.MixedBodyForm
import MacroPeg.CBV.NullableStarControl

namespace Shallot.MacroPeg.CBV.MixedBodyStar
open AdjacentCallsiteRecursive (Header)
open MixedAdjacentRecursive (Body)
open MixedOriginControl (Part Spec render)
open MixedBodyForm (Form)
open ReplayControlFusion (Plan)
open ContinuationPlan (sem sequence)
open NullableStarControl (freeze bounded consumer Change eval_change star_change sequence_identity)
variable {H : Header}

/-- Positive epsilon returns the actual origin even outside the input range. -/
def identity (H : Header) : Body H := .notP (.notP (.lit []))
def diverge (H : Header) : Part H := ⟨false,.eps,true⟩
def dummy (H : Header) : Part H := ⟨false,.eps,false⟩

def strict (f : Form H) : Form H :=
  ⟨f.leaves++[diverge H,dummy H],freeze f.leaves.length (f.leaves.length+1) f.plan,
    by simpa only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero] using bounded _ _ f.bounded,
    by simp⟩

def done (H : Header) : Form H := MixedBodyForm.neg (MixedBodyForm.atom ⟨false,.notP (.lit []),false⟩)
def iterate (f : Form H) : Form H := MixedBodyForm.repeatThen (strict f) (identity H) (done H)

theorem identity_eval (H : Header) (ps : List Spec)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render H ps (identity H)) p=some (some p) := by
  simp [identity,render,evV,stripPrefix?]

theorem diverge_eval (H : Header) (ps : List Spec)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render H ps (MixedBodyLeaves.raw (diverge H))) p=none := by
  rw [MixedBodyLeaves.raw_render]
  simp only [diverge,ite_true,MixedOriginControl.stuck_eval]

theorem strict_change (H : Header) (ps : List Spec) (f : Form H)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    Change p (evV g x s T E (render H ps f.syntax) p)
      (evV g x s T E (render H ps (strict f).syntax) p) := by
  rw [MixedBodyForm.Form.syntax,MixedBodyForm.Form.syntax,MixedBodyLeaves.control_eval,MixedBodyLeaves.control_eval]
  apply eval_change _ _ _ _ _ _ _ f.bounded p
  · intro i hi q
    rw [show (strict f).leaves=f.leaves++[diverge H,dummy H] from rfl,
      MixedBodyLeaves.lookup_prefix _ _ i hi]
  · intro q
    have hd : MixedBodyLeaves.lookup (strict f).leaves f.leaves.length=MixedBodyLeaves.raw (diverge H) := by
      simp [strict,MixedBodyLeaves.lookup]
    rw [hd]
    exact diverge_eval H ps g x s T E q

theorem done_eval (H : Header) (ps : List Spec) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render H ps (done H).syntax) p=some (some p) := by
  change evV g x s T E (.notP (.seq (.param 0) (.notP (.lit [])))) p=some (some p)
  simp only [evV]
  cases E[0]? with
  | none => rfl
  | some w =>
    cases h : stripPrefix? w (sfx x p) <;> simp only [h,stripPrefix?]

theorem repeat_eval (H : Header) (ps : List Spec) (f : Form H)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.star (render H ps f.syntax)) p=
    evV g x s T E (render H ps (iterate f).syntax) p := by
  have hstar := star_change (fun q => evV g x s T E (render H ps f.syntax) q)
    (fun q => evV g x s T E (render H ps (strict f).syntax) q) p
    (fun q _ => strict_change H ps f g x s T E q)
  have he := MixedBodyForm.repeatThen_eval H ps (strict f) (done H)
    (identity H) (consumer _ _ _) g x s hs T hT E p hp
  have hi : (fun q => evV g x s T E (render H ps (identity H)) q)=(fun q => some (some q)) := by
    funext q; exact identity_eval H ps g x s T E q
  change sequence (evStar (sequence (fun q => evV g x s T E (render H ps (strict f).syntax) q)
    (fun q => evV g x s T E (render H ps (identity H)) q)))
    (fun q => evV g x s T E (render H ps (done H).syntax) q) p=_ at he
  have hc : (fun q => evV g x s T E (render H ps (done H).syntax) q)=(fun q => some (some q)) := by
    funext q; exact done_eval H ps g x s T E q
  rw [hi,hc] at he
  have hid : sequence (fun q => evV g x s T E (render H ps (strict f).syntax) q)
      (fun q => some (some q))=(fun q => evV g x s T E (render H ps (strict f).syntax) q) := by
    funext q; exact sequence_identity _ q
  rw [hid,sequence_identity] at he
  exact hstar.trans he

end Shallot.MacroPeg.CBV.MixedBodyStar
