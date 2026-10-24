import MacroPeg.CBV.RecursiveCodeGrammar
import MacroPeg.CBV.ScannerCapturedArguments

/-! A genuinely recursive balanced-word header and argument, with reuse of
both child and parent captures, plus an unproductive helper component. -/
namespace Shallot.MacroPeg.CBV.RecursiveCodeExamples
open RecursiveCodeGrammar
open NestedScannerArguments (accepts)

def balanced : MExp := .alt (.seq (.lit ['a']) (.seq (.call 1 []) (.lit ['b']))) .eps
def bodies : List MExp := [.call 0 [],balanced]
def head : MExp := .seq (.call 1 []) (.lit ['#'])
def code (w : List Char) : Prop := w.dropWhile (accepts ['a','b'])=['#']

theorem bodies_valid : RecursiveParserStability.Valid bodies := by
  intro e he
  simp only [bodies,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl <;>
    simp [balanced,RecursiveParserStability.Lexical,bodies]

theorem bodies_safe : ∀ e ∈ bodies, ScannerAbsorption.Safe bodies.length ['a','b'] e := by
  intro e he
  simp only [bodies,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl <;>
    simp [balanced,ScannerAbsorption.Safe,bodies,accepts,Shallot.beqChar]

theorem code_prefixFree : PrefixCodeCapture.PrefixFree code := by
  rintro u v hu hv ⟨r,hr⟩
  change u.dropWhile (accepts ['a','b'])=['#'] at hu
  change v.dropWhile (accepts ['a','b'])=['#'] at hv
  rw [←hr] at hv
  have he : r=[] := by simpa [List.dropWhile_append,hu] using hv
  simpa [he] using hr

theorem helpers_firstOrder : (RecursiveParserStability.grammar bodies).FirstOrder := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  exact RecursiveParserStability.lexical_firstOrder _ e (bodies_valid e he)

theorem head_captured (x : List Char) (p q : Nat) (hp : p≤x.length)
    (h : evV (RecursiveParserStability.grammar bodies) x .callByValuePar
      (canonical bodies x) [] head p=some (some q)) : code (pre x p q) := by
  let g := RecursiveParserStability.grammar bodies
  let T := canonical bodies x
  cases ha : evV g x .callByValuePar T [] (.call 1 []) p with
  | none => rw [head,evV_seq_none ha] at h; cases h
  | some result => cases result with
    | none => rw [head,evV_seq_fail ha] at h; cases h
    | some j =>
      rw [head,evV_seq_ok ha] at h
      have hfo : (MExp.call 1 []).FirstOrder := by trivial
      have hfirst := ReplayFusion.success_prefix (tblV_sound helpers_firstOrder (by decide) _) [] _ hfo p j hp ha
      have hs := ScannerAbsorption.evaluator_safe (RecursiveParserStability.installed bodies)
        ['a','b'] x .callByValuePar T
        (ScannerAbsorption.physical_rows_safe (RecursiveParserStability.installed bodies) ['a','b'] bodies_safe
          x .callByValuePar (RecursiveParserStability.floor bodies x))
        (tblV_ok g x .callByValuePar _) [] (.call 1 []) (by change 1<2; omega) p j hp ha
      rw [hfirst.2] at hs
      have hw := ScannerCapturedArguments.all_of_dropWhile_append ['a','b'] (pre x p j) (sfx x j) hs
      have hlast := ReplayFusion.success_prefix (tblV_sound helpers_firstOrder (by decide) _)
        [] (.lit ['#']) (by trivial) j q hfirst.1 h
      have hv := WordArguments.value_of_success g x .callByValuePar T [] (.lit ['#']) (by trivial) j q hfirst.1 h
      have hv' : pre x j q=['#'] := by simpa [WordArguments.value] using hv.symm
      rw [SequenceArguments.pre_concat hp hlast.1 hfirst.2 hlast.2,hv']
      change ((pre x p j)++['#']).dropWhile (accepts ['a','b'])=['#']
      rw [ScannerAbsorption.dropWhile_append _ _ hw]
      rfl

def header : Header where
  bodies := bodies
  valid := bodies_valid
  head := head
  lexical := by simp [head,bodies,RecursiveParserStability.Lexical]
  code := code
  prefixFree := code_prefixFree
  captured := head_captured

def two : MExp := .seq head head

theorem two_captured (x : List Char) (p q : Nat) (hp : p≤x.length)
    (h : evV (RecursiveParserStability.grammar bodies) x .callByValuePar
      (canonical bodies x) [] two p=some (some q)) :
    ∃ u v, code u ∧ code v ∧ pre x p q=u++v := by
  change lexical header two x p=some (some q) at h
  unfold lexical at h
  cases ha : evV (RecursiveParserStability.grammar header.bodies) x .callByValuePar (canonical header.bodies x) [] head p with
  | none => rw [two,evV_seq_none ha] at h; cases h
  | some result => cases result with
    | none => rw [two,evV_seq_fail ha] at h; cases h
    | some j =>
      rw [two,evV_seq_ok ha] at h
      have hfirst := lexical_success header head header.lexical x p j hp ha
      have hlast := lexical_success header head header.lexical x j q hfirst.1 h
      exact ⟨pre x p j,pre x j q,head_captured x p j hp ha,head_captured x j q hfirst.1 h,
        SequenceArguments.pre_concat hp hlast.1 hfirst.2 hlast.2⟩

def user (mark : Char) (next : Nat) : User header where
  arg := two
  lexical := by simp [two,head,bodies,RecursiveParserStability.Lexical,header]
  captured := two_captured
  body := .alt (.seq (.lit [mark]) (.seq (.call next []) (.seq (.lit ['?']) (.param 0)))) (.lit ['!'])

def tails : List (User header) := [user '@' 1,user '%' 0]
def root : MExp := .call 0 []
def good : List Char := "aabb#aabb#aabb#@ab#ab#ab#!?aabb#aabb#".toList
def shortParent : List Char := "aabb#aabb#aabb#@ab#ab#ab#!?aabb#".toList

theorem source_execution :
    evV (source header tails) good .callByValuePar
      (tblV (source header tails) good .callByValuePar 12) [] (render header tails true root) good.length=some (some 0) ∧
    evV (source header tails) shortParent .callByValuePar
      (tblV (source header tails) shortParent .callByValuePar 12) [] (render header tails true root) shortParent.length=some none := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
    SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

theorem translated_execution :
    SObs (target header tails) .callByValueSeq (render header tails false root) good (some []) ∧
    SObs (target header tails) .callByValueSeq (render header tails false root) shortParent none := by
  constructor
  · apply (all_inputs good (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header tails) (by decide)
      (render_firstOrder header tails true root) 12 (Nat.le_refl _) source_execution.1
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  · apply (all_inputs shortParent none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header tails) (by decide)
      (render_firstOrder header tails true root) 12 (Nat.le_refl _) source_execution.2
    rw [sfx_self,obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩


def cyclicUser : User header where
  arg := .call 0 []
  lexical := by change 0<2; omega
  captured := by
    intro x p q hp h
    have hn := RecursiveParserStability.cycle_undefined
      (g:=RecursiveParserStability.grammar bodies) (by rfl) x .callByValuePar
      (RecursiveParserStability.floor bodies x) [] p hp
    change evV (RecursiveParserStability.grammar bodies) x .callByValuePar
      (tblV (RecursiveParserStability.grammar bodies) x .callByValuePar (RecursiveParserStability.floor bodies x))
      [] (.call 0 []) p=some (some q) at h
    rw [hn] at h
    cases h
  body := .eps

theorem cyclic_argument_undefined (x : List Char) (p : Nat) (hp : p≤x.length) :
    argument header cyclicUser x p=none :=
  RecursiveParserStability.cycle_undefined (by rfl) x .callByValuePar
    (RecursiveParserStability.floor bodies x) [] p hp

/-- An actual unproductive helper remains undefined in the ordinary source
at every physical stage, independently of the productive header. -/
theorem cyclic_source_undefined (x : List Char) (k : Nat) (p : Nat) (hp : p≤x.length) :
    evV (source header [cyclicUser]) x .callByValuePar
      (tblV (source header [cyclicUser]) x .callByValuePar k) []
      (render header [cyclicUser] true root) p=none := by
  have hs : ruleAtM (source header [cyclicUser]).rules 2=
      some ⟨1,.seq head (.seq (.param 0) .eps)⟩ := by rfl
  change evV _ x .callByValuePar _ [] (.call 2 [.call 0 []]) p=none
  rw [evV_call_par hs rfl (by decide)]
  simp only [evParArgs,RecursiveParserStability.cycle_undefined (g:=source header [cyclicUser])
    (by rfl) x .callByValuePar k [] p hp]

theorem cyclic_no_observation (x : List Char) (r : Option (List Char)) :
    ¬SObs (target header [cyclicUser]) .callByValueSeq
      (render header [cyclicUser] false root) x r := by
  rw [←observations_iff header [cyclicUser] root x r,
    ←decideObsV_iff (source_firstOrder header [cyclicUser]) (by decide)
      (render_firstOrder header [cyclicUser] true root)]
  unfold decideObsV
  rw [cyclic_source_undefined x _ x.length (Nat.le_refl _)]
  simp

end Shallot.MacroPeg.CBV.RecursiveCodeExamples
