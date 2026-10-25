import MacroPeg.CBV.GuardedFinitePrefix

namespace Shallot.MacroPeg.CBV.FinitePrefixMachines
open StatefulScanner (Machine next)

/-- One rotation step; an empty word stays empty. -/
def turn : List Char → List Char
  | [] => []
  | c::w => w++[c]

def turns : Nat → List Char → List Char
  | 0,w => w
  | k+1,w => turns k (turn w)

theorem turns_succ (k : Nat) (w : List Char) : turns (k+1) w=turn (turns k w) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih => exact ih (turn w)

theorem turns_split (u v : List Char) : turns u.length (u++v)=v++u := by
  induction u generalizing v with
  | nil => simp [turns]
  | cons c u ih => simpa [turns,turn,List.append_assoc] using ih (v++[c])

theorem turns_cycle (w : List Char) : turns w.length w=w := by
  simpa using turns_split w []

def rotations (w : List Char) : List (List Char) :=
  (List.range w.length).map (fun k => turns k w)

theorem rotations_self (w : List Char) (hw : w≠[]) : w∈rotations w := by
  apply List.mem_map.mpr
  exact ⟨0,List.mem_range.mpr (List.length_pos_iff.mpr hw),rfl⟩

theorem rotations_turn (w v : List Char) (hv : v∈rotations w) : turn v∈rotations w := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hv
  have hk := List.mem_range.mp hk
  rw [←turns_succ]
  by_cases he : k+1=w.length
  · rw [he,turns_cycle]
    exact rotations_self w (by intro h; simp [h] at hk)
  · exact List.mem_map.mpr ⟨k+1,List.mem_range.mpr (by omega),rfl⟩

theorem turns_length (k : Nat) (w : List Char) : (turns k w).length=w.length := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih => rw [turns,ih]; cases w <;> simp [turn]

theorem rotations_nonempty (w v : List Char) (hv : v∈rotations w) : v≠[] := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hv
  have hk := List.mem_range.mp hk
  intro he
  have hl := turns_length k w
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega

def suffixes : List Char → List (List Char)
  | [] => [[]]
  | c::w => (c::w)::suffixes w

theorem suffixes_self (w : List Char) : w∈suffixes w := by cases w <;> simp [suffixes]

theorem suffixes_tail (w : List Char) (c : Char) (v : List Char) (hv : c::v∈suffixes w) :
    v∈suffixes w := by
  induction w with
  | nil => simp [suffixes] at hv
  | cons d w ih =>
    rcases List.mem_cons.mp hv with he | hv
    · cases he; exact List.mem_cons_of_mem _ (suffixes_self v)
    · exact List.mem_cons_of_mem _ (ih hv)

inductive Node where
  | literal (w : List Char)
  | rotating (w : List Char)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Literal suffix states and rotating residual states have different jobs.
The empty literal state doubles as the source-alphabet frontier. -/
def nodes (words : List (List Char)) : List Node :=
  (.literal []::((words.flatMap suffixes).map Node.literal ++
    (words.flatMap rotations).map Node.rotating)).eraseDups

theorem empty_mem (words : List (List Char)) : Node.literal []∈nodes words :=
  List.mem_eraseDups.mpr List.mem_cons_self

theorem literal_mem (words : List (List Char)) (w : List Char) (hw : w∈words) :
    Node.literal w∈nodes words :=
  List.mem_eraseDups.mpr (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_map.mpr ⟨w,List.mem_flatMap.mpr ⟨w,hw,suffixes_self w⟩,rfl⟩)))

theorem rotating_mem (words : List (List Char)) (w : List Char) (hw : w∈words) (hn : w≠[]) :
    Node.rotating w∈nodes words :=
  List.mem_eraseDups.mpr (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_map.mpr ⟨w,List.mem_flatMap.mpr ⟨w,hw,rotations_self w hn⟩,rfl⟩)))

theorem tail_mem (words : List (List Char)) (c : Char) (w : List Char)
    (h : Node.literal (c::w)∈nodes words) : Node.literal w∈nodes words := by
  rcases List.mem_cons.mp (List.mem_eraseDups.mp h) with he | h
  · cases he
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨v,hv,he⟩ := List.mem_map.mp h
      cases he
      obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp hv
      exact List.mem_eraseDups.mpr (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.mpr ⟨w,List.mem_flatMap.mpr ⟨u,hu,suffixes_tail u c w hv⟩,rfl⟩)))
    · obtain ⟨v,_,he⟩ := List.mem_map.mp h
      cases he

theorem turn_mem (words : List (List Char)) (w : List Char)
    (h : Node.rotating w∈nodes words) : Node.rotating (turn w)∈nodes words ∧ w≠[] := by
  rcases List.mem_cons.mp (List.mem_eraseDups.mp h) with he | h
  · cases he
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨v,_,he⟩ := List.mem_map.mp h
      cases he
    · obtain ⟨v,hv,he⟩ := List.mem_map.mp h
      cases he
      obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp hv
      exact ⟨List.mem_eraseDups.mpr (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_map.mpr ⟨turn w,List.mem_flatMap.mpr ⟨u,hu,rotations_turn u w hv⟩,rfl⟩))),
        rotations_nonempty u w hv⟩

abbrev Size (words : List (List Char)) := (nodes words).length

def index (words : List (List Char)) (node : Node) : Fin (Size words) :=
  if h : node∈nodes words then ⟨(nodes words).idxOf node,List.idxOf_lt_length_iff.mpr h⟩
  else ⟨0,List.length_pos_iff.mpr (by intro hn; have := empty_mem words; simp [hn] at this)⟩

theorem index_value (words : List (List Char)) (node : Node) (h : node∈nodes words) :
    (nodes words)[(index words node).val]=node := by
  simp only [index,dif_pos h]
  exact (List.getElem?_eq_some_iff.mp (DependentProfileCall.index_correct node (nodes words) h)).2

def machine (alphabet : List Char) (words : List (List Char)) : Machine (Size words) :=
  ⟨fun q => match (nodes words)[q.val] with
    | .literal [] => alphabet.map (fun c => (c,index words (.literal [])))
    | .literal (c::w) => [(c,index words (.literal w))]
    | .rotating [] => []
    | .rotating (c::w) => [(c,index words (.rotating (w++[c]))) ]⟩

def literals (words : List (List Char)) : LiteralPrefixObservation.Labels (Size words) :=
  fun q => match (nodes words)[q.val] with | .literal w => some w | _ => none

def residuals (words : List (List Char)) : ScannerReplayResidual.Labels (Size words) :=
  fun q => match (nodes words)[q.val] with | .rotating w => some w | _ => none


theorem next_constant {Q : Type} (alphabet : List Char) (q : Q) (c : Char) (hc : c∈alphabet) :
    next (alphabet.map (fun d => (d,q))) c=some q := by
  induction alphabet with
  | nil => cases hc
  | cons d alphabet ih =>
    by_cases hd : Shallot.beqChar d c=true
    · simp [next,hd]
    · have ht : c∈alphabet := by
        rcases List.mem_cons.mp hc with he | ht
        · subst d; exact False.elim (hd (by simp [Shallot.beqChar]))
        · exact ht
      simpa [next,hd] using ih ht

theorem literals_checked (alphabet : List Char) (words : List (List Char)) :
    LiteralPrefixObservation.check (machine alphabet words) alphabet (literals words)=true := by
  apply List.all_eq_true.mpr
  intro q _
  cases hn : (nodes words)[q.val] with
  | rotating w => simp [literals,hn]
  | literal w =>
    cases w with
    | nil =>
      simp only [literals,hn,machine]
      refine Bool.and_eq_true_iff.mpr ⟨?_,?_⟩
      · apply List.all_eq_true.mpr
        intro cr hcr
        obtain ⟨c,_,rfl⟩ := List.mem_map.mp hcr
        simp [index_value words (.literal []) (empty_mem words)]
      · apply List.all_eq_true.mpr
        intro c hc
        rw [next_constant alphabet _ c hc]
        rfl
    | cons c w =>
      have ht := tail_mem words c w (List.mem_of_getElem hn)
      simp [literals,hn,machine,index_value words (.literal w) ht,next,Shallot.beqChar]

theorem residuals_checked (alphabet : List Char) (words : List (List Char)) :
    ScannerReplayResidual.check (machine alphabet words) (residuals words)=true := by
  apply List.all_eq_true.mpr
  intro q _
  cases hn : (nodes words)[q.val] with
  | literal w => simp [residuals,hn]
  | rotating w =>
    have ht := turn_mem words w (List.mem_of_getElem hn)
    cases w with
    | nil => exact False.elim (ht.2 rfl)
    | cons c w =>
      simp [residuals,hn,machine,index_value words (.rotating (w++[c])) ht.1]

theorem residuals_complete (alphabet : List Char) (words : List (List Char)) :
    ScannerReplayResidual.completeCheck (machine alphabet words) (residuals words)=true := by
  apply List.all_eq_true.mpr
  intro q _
  cases hn : (nodes words)[q.val] with
  | literal w => simp [residuals,hn]
  | rotating w =>
    have ht := turn_mem words w (List.mem_of_getElem hn)
    cases w with
    | nil => exact False.elim (ht.2 rfl)
    | cons c w => simp [residuals,hn,machine,next,Shallot.beqChar]

theorem alphabet_checked (alphabet : List Char) (words : List (List Char)) :
    LiteralPrefixObservation.alphabetCheck (machine alphabet words) alphabet (index words (.literal []))=true := by
  simp only [LiteralPrefixObservation.alphabetCheck,machine,index_value words (.literal []) (empty_mem words)]
  refine Bool.and_eq_true_iff.mpr ⟨?_,?_⟩
  · apply List.all_eq_true.mpr
    intro cr hcr
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hcr
    simp [hc]
  · apply List.all_eq_true.mpr
    intro c hc
    rw [next_constant alphabet _ c hc]
    simp

def read (alphabet : List Char) (words : List (List Char)) : GuardedFinitePrefix.Words (Size words) :=
  fun u => .literalQuery alphabet (index words (.literal [])) (index words (.literal u)) (literals words)

def finish (words : List (List Char)) : GuardedFinitePrefix.Words (Size words) :=
  fun u => if u=[] then .replayQuery else .shift (index words (.rotating u)) (residuals words)

theorem read_label (words : List (List Char)) (u : List Char) (hu : u∈words) :
    literals words (index words (.literal u))=some u := by
  simp [literals,index_value words (.literal u) (literal_mem words u hu)]

theorem finish_label (words : List (List Char)) (u : List Char) (hu : u∈words) (hn : u≠[]) :
    residuals words (index words (.rotating u))=some u := by
  simp [residuals,index_value words (.rotating u) (rotating_mem words u hu hn)]

theorem read_checked (alphabet : List Char) (words : List (List Char)) (u : List Char) (hu : u∈words) :
    GuardedFinitePrefix.readCheck (read alphabet words) u=true ∧
    GuardedReplayControl.check (machine alphabet words) (read alphabet words u)=true := by
  simp [read,GuardedFinitePrefix.readCheck,read_label words u hu,GuardedReplayControl.check,
    literals_checked,alphabet_checked]

theorem finish_checked (alphabet : List Char) (words : List (List Char)) (u : List Char) (hu : u∈words) :
    GuardedFinitePrefix.finishCheck (finish words) u=true ∧
    GuardedReplayControl.check (machine alphabet words) (finish words u)=true := by
  by_cases hn : u=[]
  · simp [finish,hn,GuardedFinitePrefix.finishCheck,GuardedReplayControl.check]
  · simp [finish,hn,GuardedFinitePrefix.finishCheck,GuardedReplayControl.check,
      ScannerReplayResidual.entryCheck,finish_label words u hu hn,residuals_checked,residuals_complete]

/-- Generated literal probes use only the generated alphabet frontier;
other observer states may fail to read a capture. -/
theorem read_capture (alphabet : List Char) (words : List (List Char)) (u w : List Char)
    (hw : LiteralPrefixObservation.Word alphabet w) :
    GuardedReplayControl.captureCheck
      (CaptureTransitionProfile.profile (DynamicScannerCapture.observer (machine alphabet words)) w)
      (read alphabet words u)=true := by
  apply (ScannerFrontierCertificate.check_actual (machine alphabet words) w _).mpr
  rw [LiteralPrefixObservation.alphabet_advance _ _ _ (alphabet_checked alphabet words) w hw]
  simp

theorem finish_capture (words : List (List Char)) (u : List Char) (P : List Nat) :
    GuardedReplayControl.captureCheck P (finish words u)=true := by
  simp only [finish]
  split <;> rfl


abbrev Word := LiteralPrefixObservation.Word

theorem turn_word (alphabet w : List Char) (hw : Word alphabet w) : Word alphabet (turn w) := by
  cases w with
  | nil => exact hw
  | cons c w =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hw d (List.mem_cons_of_mem _ hd)
    · have he : d=c := by simpa using hd
      subst d
      exact hw c List.mem_cons_self

theorem turns_word (alphabet : List Char) (k : Nat) (w : List Char) (hw : Word alphabet w) :
    Word alphabet (turns k w) := by
  induction k generalizing w with
  | zero => exact hw
  | succ k ih => exact ih (turn w) (turn_word alphabet w hw)

theorem suffixes_word (alphabet w v : List Char) (hw : Word alphabet w) (hv : v∈suffixes w) :
    Word alphabet v := by
  induction w with
  | nil => obtain rfl := List.mem_singleton.mp hv; exact hw
  | cons c w ih =>
    rcases List.mem_cons.mp hv with he | hv
    · simpa [←he] using hw
    · exact ih (fun d hd => hw d (List.mem_cons_of_mem _ hd)) hv

theorem node_word (alphabet : List Char) (words : List (List Char))
    (hw : ∀ w∈words, Word alphabet w) (node : Node) (hn : node∈nodes words) :
    match node with | .literal w | .rotating w => Word alphabet w := by
  rcases List.mem_cons.mp (List.mem_eraseDups.mp hn) with he | hn
  · subst node
    intro c hc
    cases hc
  · rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hn
      obtain ⟨w,hw',hv⟩ := List.mem_flatMap.mp hv
      exact suffixes_word alphabet w v (hw w hw') hv
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hn
      obtain ⟨w,hw',hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hv
      exact turns_word alphabet k w (hw w hw')

theorem machine_alphabet (alphabet : List Char) (words : List (List Char))
    (hw : ∀ w∈words, Word alphabet w) :
    AlphabetCaptureProfiles.machineCheck (machine alphabet words) alphabet=true := by
  apply List.all_eq_true.mpr
  intro q _
  cases hn : (nodes words)[q.val] with
  | literal w =>
    have hh : Word alphabet w := node_word alphabet words hw (.literal w) (List.mem_of_getElem hn)
    cases w with
    | nil =>
      apply List.all_eq_true.mpr
      intro cr hcr
      simp only [machine,hn] at hcr
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hcr
      exact List.contains_iff_mem.mpr hc
    | cons c w =>
      have hc := hh c List.mem_cons_self
      simpa [machine,hn] using List.contains_iff_mem.mpr hc
  | rotating w =>
    have hh : Word alphabet w := node_word alphabet words hw (.rotating w) (List.mem_of_getElem hn)
    cases w with
    | nil => simp [machine,hn]
    | cons c w =>
      have hc := hh c List.mem_cons_self
      simpa [machine,hn] using List.contains_iff_mem.mpr hc

end Shallot.MacroPeg.CBV.FinitePrefixMachines
