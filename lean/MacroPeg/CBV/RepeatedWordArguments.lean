import MacroPeg.CBV.WordViewSubstitution

namespace Shallot.MacroPeg.CBV.RepeatedWordArguments

def copies (w : List Char) : Nat → List Char
  | 0 => []
  | n+1 => w++copies w n

def expression (a : MExp) : Nat → MExp
  | 0 => .lit []
  | n+1 => .seq a (expression a n)

theorem copies_nil (n : Nat) : copies [] n=[] := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem expression_word (a : MExp) (ha : WordArguments.Word a) (n : Nat) :
    WordArguments.Word (expression a n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ha,ih⟩

theorem expression_value (E : List (List Char)) (a : MExp) (w : List Char)
    (hv : WordArguments.value E a=some w) (n : Nat) :
    WordArguments.value E (expression a n)=some (copies w n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expression,copies,WordArguments.value,hv,ih,Option.bind_some,Option.map_some]

theorem strip_concat (u v input : List Char) :
    Shallot.stripPrefix? (u++v) input = (Shallot.stripPrefix? u input).bind (Shallot.stripPrefix? v) := by
  induction u generalizing input with
  | nil => rfl
  | cons c u ih =>
    cases input with
    | nil => rfl
    | cons d input => simp only [List.cons_append,Shallot.stripPrefix?]; split <;> simp_all

/-- Repeated sequential arguments capture separate equal values, rather
than one concatenated value. Matching is still exact on the original input. -/
theorem sequential (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (a : MExp) (ha : WordArguments.Word a) (w : List Char)
    (hv : WordArguments.value E a=some w) (n p : Nat) (hp : p≤x.length) :
    evSeqArgs g x s T E (List.replicate n a) p =
      match Shallot.stripPrefix? (copies w n) (sfx x p) with
      | none => some none
      | some rest => some (some (List.replicate n w,rest.length)) := by
  induction n generalizing p with
  | zero => simp only [List.replicate_zero,evSeqArgs,copies,Shallot.stripPrefix?,length_sfx x hp]
  | succ n ih =>
    have he := WordArguments.word_eval g x s T E a ha p
    simp only [hv,WordArguments.literal,evV] at he
    simp only [List.replicate_succ,evSeqArgs,he,copies,strip_concat]
    cases hs : Shallot.stripPrefix? w (sfx x p) with
    | none => rfl
    | some rest =>
      have hsuf := suffix_trans (sfx_is_suffix x p)
        ⟨w,(CBVtoCBN.stripPrefix_exact _ _ _).mp hs⟩
      have hb : rest.length≤x.length := by
        obtain ⟨u,hu⟩ := hsuf
        have hl := congrArg List.length hu
        simp only [List.length_append] at hl
        omega
      have hpre : pre x p rest.length=w := by
        simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) ((CBVtoCBN.stripPrefix_exact _ _ _).mp hs)
      simp only [Option.bind_some,ih rest.length hb,sfx_suffix hsuf.choose_spec,hpre]
      cases Shallot.stripPrefix? (copies w n) rest <;> rfl

end Shallot.MacroPeg.CBV.RepeatedWordArguments
