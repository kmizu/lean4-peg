import MacroPeg.CBV.CountedCodeGrammar
import MacroPeg.CBV.RecursiveCodeExamples

/-! Count certificates come from actual recursive header parsing, for all
positive counts. Different user rules retain different codeword counts. -/
namespace Shallot.MacroPeg.CBV.CountedCodeExamples
open CountedCodeGrammar
open RecursiveCodeExamples (header bodies head)
open RecursiveCodeGrammar (canonical)

def headers : Nat → MExp
  | 0 => .lit []
  | n+1 => .seq head (headers n)

theorem headers_allowed : ∀ n, HelperArgument.Syntax bodies.length (headers n)
  | 0 => trivial
  | n+1 => ⟨by simp [head,bodies,HelperArgument.Syntax],headers_allowed n⟩

theorem head_captured_env (x : List Char) (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (h : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E head p=some (some q)) :
    header.code (pre x p q) := by
  have hh := RecursiveParserStability.lexical_eval (RecursiveParserStability.installed bodies)
    (RecursiveParserStability.installed bodies) x .callByValuePar .callByValuePar
    (canonical bodies x) (canonical bodies x) (tblV_ok _ _ _ _)
    (by intro i hi j hj; rfl) E [] head header.lexical p hp
  exact header.captured x p q hp (hh ▸ h)

theorem headers_captured (x : List Char) (E : List (List Char)) :
    ∀ n p q, p≤x.length →
      evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (headers n) p=some (some q) →
      ∃ ws : List (List Char), ws.length=n ∧ (∀ w∈ws, header.code w) ∧ pre x p q=ws.flatten
  | 0, p, q, hp, h => by
    have hq : p=q := by simpa [headers,evV,Shallot.stripPrefix?,length_sfx x hp] using h
    subst q
    exact ⟨[],rfl,by simp,by simp [pre]⟩
  | n+1, p, q, hp, h => by
    cases ha : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E head p with
    | none => rw [headers,evV_seq_none ha] at h; cases h
    | some result => cases result with
      | none => rw [headers,evV_seq_fail ha] at h; cases h
      | some j =>
        rw [headers,evV_seq_ok ha] at h
        have hf := ReplayFusion.success_prefix (tblV_sound RecursiveCodeExamples.helpers_firstOrder (by decide) _)
          E head (RecursiveParserStability.lexical_firstOrder _ head header.lexical) p j hp ha
        have hl := ReplayFusion.success_prefix (tblV_sound RecursiveCodeExamples.helpers_firstOrder (by decide) _)
          E (headers n) (HelperArgument.firstOrder _ _ (headers_allowed n)) j q hf.1 h
        obtain ⟨ws,hlen,hcode,hw⟩ := headers_captured x E n j q hf.1 h
        refine ⟨pre x p j::ws,by simp [hlen],?_,?_⟩
        · intro w hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact head_captured_env x E p j hp ha
          · exact hcode w hmem
        · rw [SequenceArguments.pre_concat hp hl.1 hf.2 hl.2,hw]
          rfl

def guarded (n : Nat) : MExp := .seq (.notP (.param 0)) (headers n)

theorem guarded_captured (extra : Nat) (x : List Char) (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (h : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (guarded (extra+1)) p=some (some q)) :
    ∃ (u : List Char) (vs : List (List Char)), header.code u ∧ (∀ v∈vs, header.code v) ∧ vs.length=extra ∧ pre x p q=u++vs.flatten := by
  have hcap : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (headers (extra+1)) p=some (some q) := by
    cases ht : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (.param 0) p with
    | none =>
      have hn : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (.notP (.param 0)) p=none := by
        change (match evV (RecursiveParserStability.grammar bodies) x .callByValuePar
            (canonical bodies x) E (.param 0) p with
          | some (some _) => some none | some none => some (some p) | none => none)=_
        rw [ht]
      rw [guarded,evV_seq_none hn] at h
      cases h
    | some result => cases result with
      | none =>
        have hn : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (.notP (.param 0)) p=some (some p) := by
          change (match evV (RecursiveParserStability.grammar bodies) x .callByValuePar
              (canonical bodies x) E (.param 0) p with
            | some (some _) => some none | some none => some (some p) | none => none)=_
          rw [ht]
        rw [guarded,evV_seq_ok hn] at h
        exact h
      | some j =>
        have hn : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (.notP (.param 0)) p=some none := by
          change (match evV (RecursiveParserStability.grammar bodies) x .callByValuePar
              (canonical bodies x) E (.param 0) p with
            | some (some _) => some none | some none => some (some p) | none => none)=_
          rw [ht]
        rw [guarded,evV_seq_fail hn] at h
        cases h
  obtain ⟨ws,hlen,hcode,hw⟩ := headers_captured x E (extra+1) p q hp hcap
  cases ws with
  | nil => simp at hlen
  | cons u vs =>
    exact ⟨u,vs,hcode u (by simp),fun v hv => hcode v (by simp [hv]),by simpa using hlen,hw⟩

def user (extra : Nat) (mark : Char) (next : Nat) : User header where
  extra := extra
  arg := guarded (extra+1)
  allowed := ⟨True.intro,headers_allowed (extra+1)⟩
  captured := guarded_captured extra
  body := (RecursiveCodeExamples.user mark next).body

def tails : List (User header) := [user 2 '@' 1,user 0 '%' 0]
def root : MExp := .call 0 []
def good : List Char := "aabb#aabb#aabb#aabb#@ab#ab#%####!?ab#?aabb#aabb#aabb#".toList
def shortParent : List Char := "aabb#aabb#aabb#aabb#@ab#ab#%####!?ab#?aabb#aabb#".toList
def unequal : List Char := "aabb#aabb#ab#aabb#!".toList

theorem source_execution :
    evV (source header tails) good .callByValuePar
      (tblV (source header tails) good .callByValuePar 16) [] (render header tails 1 true root) good.length=some (some 0) ∧
    evV (source header tails) shortParent .callByValuePar
      (tblV (source header tails) shortParent .callByValuePar 16) [] (render header tails 1 true root) shortParent.length=some none ∧
    evV (source header tails) unequal .callByValuePar
      (tblV (source header tails) unequal .callByValuePar 16) [] (render header tails 1 true root) unequal.length=some none := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails 1 true root) x r ↔
    SObs (target header tails) .callByValueSeq (render header tails 1 false root) x r :=
  observations_iff header tails 1 root x r (by decide)

theorem translated_execution :
    SObs (target header tails) .callByValueSeq (render header tails 1 false root) good (some []) ∧
    SObs (target header tails) .callByValueSeq (render header tails 1 false root) shortParent none ∧
    SObs (target header tails) .callByValueSeq (render header tails 1 false root) unequal none := by
  have accept (x : List Char)
      (h : evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 16) [] (render header tails 1 true root) x.length=some (some 0)) :
      SObs (target header tails) .callByValueSeq (render header tails 1 false root) x (some []) := by
    apply (all_inputs x (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header tails) (by decide)
      (render_firstOrder header tails 1 true root) 16 (Nat.le_refl _) h
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  have reject (x : List Char)
      (h : evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 16) [] (render header tails 1 true root) x.length=some none) :
      SObs (target header tails) .callByValueSeq (render header tails 1 false root) x none := by
    apply (all_inputs x none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header tails) (by decide)
      (render_firstOrder header tails 1 true root) 16 (Nat.le_refl _) h
    rw [sfx_self,obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩
  exact ⟨accept good source_execution.1,reject shortParent source_execution.2.1,reject unequal source_execution.2.2⟩

end Shallot.MacroPeg.CBV.CountedCodeExamples
