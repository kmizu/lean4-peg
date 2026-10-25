import MacroPeg.CBV.CaptureDelimiterSafety

namespace Shallot.MacroPeg.CBV.DelimitedCopySyntax
open DelimiterTemplate DelimitedCopyTemplates
open RecursiveParserStability (Lexical Installed)

def source (bodies : List MExp) (d : Char) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++[⟨2,compile d (sourceBlockParts d)⟩]⟩
def target (bodies : List MExp) (d : Char) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++[⟨1,compile d (shortBlockParts d)⟩,⟨1,compile d (longBlockParts d)⟩]⟩
def root (bodies : List MExp) (A B : MExp) : MExp := .call bodies.length [A,B]
def targetRoot (bodies : List MExp) (A B : MExp) : MExp :=
  .seq (.andP A) (.seq (.andP B) (.seq (.andP (.call bodies.length [A])) (.call (bodies.length+1) [B])))

def lexicalCheck (n : Nat) : MExp → Bool
  | .call i [] => decide (i<n)
  | .seq a b | .alt a b => lexicalCheck n a && lexicalCheck n b
  | .notP a | .star a => lexicalCheck n a
  | .eps | .any | .chr _ | .range _ _ | .lit _ => true
  | _ => false

theorem lexical_checked (n : Nat) : ∀ e, lexicalCheck n e=true → Lexical n e
  | .call i [],h => (show i<n from of_decide_eq_true h)
  | .seq a b,h | .alt a b,h => ⟨lexical_checked n a (Bool.and_eq_true_iff.mp h).1,lexical_checked n b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h | .star a,h => lexical_checked n a h
  | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ => True.intro
  | .call _ (_::_),h | .param _,h | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => by cases h

def check (bodies : List MExp) (alphabet : List Char) (d : Char) (A B : MExp) : Bool :=
  bodies.all (lexicalCheck bodies.length) && lexicalCheck bodies.length A && lexicalCheck bodies.length B &&
    decide (d∉alphabet) && MaskedScannerAbsorption.check bodies alphabet A && MaskedScannerAbsorption.check bodies alphabet B

structure Checked (bodies : List MExp) (alphabet : List Char) (d : Char) (A B : MExp) : Prop where
  library : RecursiveParserStability.Valid bodies
  left : Lexical bodies.length A
  right : Lexical bodies.length B
  separator : d∉alphabet
  valid : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies alphabet) alphabet
  safeLeft : MaskedScannerAbsorption.Safe (MaskedScannerAbsorption.mask bodies alphabet) alphabet A
  safeRight : MaskedScannerAbsorption.Safe (MaskedScannerAbsorption.mask bodies alphabet) alphabet B

theorem checked (bodies : List MExp) (alphabet : List Char) (d : Char) (A B : MExp)
    (hc : check bodies alphabet d A B=true) : Checked bodies alphabet d A B := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hl,hA⟩,hB⟩,hd⟩,hsA⟩,hsB⟩ := hc
  obtain ⟨hv,ha⟩ := MaskedScannerAbsorption.checked bodies alphabet A hsA
  obtain ⟨_,hb⟩ := MaskedScannerAbsorption.checked bodies alphabet B hsB
  exact ⟨fun e he => lexical_checked _ e (List.all_eq_true.mp hl e he),lexical_checked _ A hA,lexical_checked _ B hB,
    of_decide_eq_true hd,hv,ha,hb⟩

theorem installed_append (bodies : List MExp) (extra : List MRule) : Installed bodies ⟨bodies.map (fun b => ⟨0,b⟩)++extra⟩ := by
  intro i b hi
  have hidx := (List.getElem?_eq_some_iff.mp hi).1
  simp only [ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hidx)]
  simp [List.getElem?_map,hi]

theorem source_installed (bodies : List MExp) (d : Char) : Installed bodies (source bodies d) := installed_append _ _
theorem target_installed (bodies : List MExp) (d : Char) : Installed bodies (target bodies d) := installed_append _ _

theorem source_rule (bodies : List MExp) (d : Char) :
    ruleAtM (source bodies d).rules bodies.length=some ⟨2,compile d (sourceBlockParts d)⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]

theorem short_rule (bodies : List MExp) (d : Char) :
    ruleAtM (target bodies d).rules bodies.length=some ⟨1,compile d (shortBlockParts d)⟩ := by
  simp [target,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]

theorem long_rule (bodies : List MExp) (d : Char) :
    ruleAtM (target bodies d).rules (bodies.length+1)=some ⟨1,compile d (longBlockParts d)⟩ := by
  simp [target,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]

theorem source_firstOrder (bodies : List MExp) (d : Char) (hb : RecursiveParserStability.Valid bodies) : (source bodies d).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp h
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · have he : r=⟨2,compile d (sourceBlockParts d)⟩ := by simpa using h
    subst r
    exact compile_firstOrder _ _

theorem target_firstOrder (bodies : List MExp) (d : Char) (hb : RecursiveParserStability.Valid bodies) : (target bodies d).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp h
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · rcases (show r=⟨1,compile d (shortBlockParts d)⟩ ∨ r=⟨1,compile d (longBlockParts d)⟩ from by simpa using h) with rfl|rfl <;> exact compile_firstOrder _ _

theorem queries_eq (bodies : List MExp) (d : Char) (hb : RecursiveParserStability.Valid bodies)
    (e : MExp) (he : Lexical bodies.length e) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source bodies d) x .callByValuePar (tblV (source bodies d) x .callByValuePar k) [] e p=
      evV (target bodies d) x .callByValueSeq (tblV (target bodies d) x .callByValueSeq k) [] e p :=
  RecursiveParserStability.lexical_eval (source_installed bodies d) (target_installed bodies d) x _ _ _ _ (tblV_ok _ _ _ k)
    (fun i hi q hq => congrArg (fun row => valAt row q) (RecursiveParserStability.helper_rows_eq hb (source_installed bodies d) (target_installed bodies d) x _ _ k i hi [] [])) [] [] e he p hp

theorem root_firstOrder (bodies : List MExp) (A B : MExp) (hA : A.FirstOrder) (hB : B.FirstOrder) : (root bodies A B).FirstOrder := ⟨hA,hB,True.intro⟩
theorem targetRoot_firstOrder (bodies : List MExp) (A B : MExp) (hA : A.FirstOrder) (hB : B.FirstOrder) : (targetRoot bodies A B).FirstOrder :=
  ⟨hA,hB,⟨hA,True.intro⟩,hB,True.intro⟩

end Shallot.MacroPeg.CBV.DelimitedCopySyntax
