import MacroPeg.CBV.SequentialCaptures
import Init.Data.List.Sort.Lemmas

/-! Any successful Par argument tuple admits a lossless, disjoint chunk
representation of the same arity. This is a value representation theorem;
it does not construct parsers that discover the chunks from the source syntax. -/
namespace Shallot.MacroPeg.CBV.CommonOriginCaptures

/-- Split nested prefixes into adjacent differences. Repeated boundaries
produce empty chunks, so no assumption about distinct capture lengths is used. -/
def differences (base : List Char) : List (List Char) → List (List Char)
  | [] => []
  | w :: ws => w.drop base.length :: differences w ws

def ordered (words : List (List Char)) : List (List Char) :=
  words.mergeSort (fun a b => a.length ≤ b.length)

def chunks (words : List (List Char)) : List (List Char) := differences [] (ordered words)

def views (parts : List (List Char)) : List (List Char) := parts.scanl (· ++ ·) []

/-- Each original parameter is identified by how many chunks reconstruct it. -/
def ranks (words : List (List Char)) : List Nat := words.map ((views (chunks words)).idxOf ·)

/-- The control family is determined by arity alone, independently of input
length, the character alphabet, and all captured word values. -/
def controls (bound : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range (bound+1)).flatMap (fun k => (controls bound n).map (k :: ·))

theorem mem_controls (bound : Nat) : ∀ n C,
    C ∈ controls bound n ↔ C.length=n ∧ ∀ k ∈ C, k ≤ bound := by
  intro n
  induction n with
  | zero => intro C; cases C <;> simp [controls]
  | succ n ih =>
    intro C
    cases C with
    | nil => simp [controls]
    | cons k C =>
      simp only [controls,List.mem_flatMap,List.mem_map]
      constructor
      · rintro ⟨a,ha,A,hA,he⟩
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        have h := (ih A).mp hA
        refine ⟨by simp [h.1],?_⟩
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · have hb := List.mem_range.mp ha; omega
        · exact h.2 j hj
      · rintro ⟨hlen,hC⟩
        exact ⟨k,List.mem_range.mpr (by have h := hC k (by simp); omega),C,
          (ih C).mpr ⟨by simpa using hlen,fun j hj => hC j (by simp [hj])⟩,rfl⟩

theorem controls_length (bound n : Nat) : (controls bound n).length = (bound+1)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [controls,List.length_flatMap,ih,List.map_const',List.sum_replicate_nat,
      Nat.pow_succ,Nat.mul_comm]

theorem differences_length (base : List Char) (words : List (List Char)) :
    (differences base words).length = words.length := by
  induction words generalizing base with
  | nil => rfl
  | cons w ws ih => simp [differences,ih]

theorem ordered_perm (words : List (List Char)) : (ordered words).Perm words :=
  List.mergeSort_perm _ _

theorem ordered_pairwise (words : List (List Char)) :
    (ordered words).Pairwise (fun a b => a.length ≤ b.length) := by
  have h := List.pairwise_mergeSort (le := fun a b : List Char => decide (a.length ≤ b.length))
    (fun _ _ _ hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) words
  simpa only [ordered,decide_eq_true_eq] using h

theorem differences_scan (input base : List Char) (words : List (List Char))
    (hp : ∀ w ∈ words, w <+: input) (hs : words.Pairwise (fun a b => a.length ≤ b.length))
    (hb : ∀ w ∈ words, base <+: w) :
    (differences base words).scanl (· ++ ·) base = base :: words := by
  induction words generalizing base with
  | nil => rfl
  | cons w ws ih =>
    have he := List.prefix_iff_eq_append.mp (hb w (by simp))
    simp only [List.pairwise_cons] at hs
    simp only [differences,List.scanl_cons,he]
    rw [ih w (fun a ha => hp a (by simp [ha])) hs.2]
    intro a ha
    exact List.prefix_of_prefix_length_le (hp w (by simp)) (hp a (by simp [ha])) (hs.1 a ha)

theorem differences_prefix (input base : List Char) (words : List (List Char))
    (hbase : base <+: input) (hp : ∀ w ∈ words, w <+: input)
    (hs : words.Pairwise (fun a b => a.length ≤ b.length)) (hb : ∀ w ∈ words, base <+: w) :
    base ++ (differences base words).flatten <+: input := by
  induction words generalizing base with
  | nil => simpa [differences] using hbase
  | cons w ws ih =>
    have he := List.prefix_iff_eq_append.mp (hb w (by simp))
    simp only [List.pairwise_cons] at hs
    simp only [differences,List.flatten_cons,← List.append_assoc,he]
    apply ih w (hp w (by simp)) (fun a ha => hp a (by simp [ha])) hs.2
    intro a ha
    exact List.prefix_of_prefix_length_le (hp w (by simp)) (hp a (by simp [ha])) (hs.1 a ha)

theorem chunks_length (words : List (List Char)) : (chunks words).length = words.length := by
  rw [chunks,differences_length,(ordered_perm words).length_eq]

theorem views_eq {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input) : views (chunks words) = [] :: ordered words := by
  exact differences_scan input [] (ordered words)
    (fun w hw => hp w ((ordered_perm words).mem_iff.mp hw)) (ordered_pairwise words)
    (fun _ _ => List.nil_prefix)

theorem chunks_prefix {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input) : (chunks words).flatten <+: input := by
  simpa only [List.nil_append,chunks] using differences_prefix input [] (ordered words) List.nil_prefix
    (fun w hw => hp w ((ordered_perm words).mem_iff.mp hw)) (ordered_pairwise words)
    (fun _ _ => List.nil_prefix)

theorem storage_bound {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input) :
    ((chunks words).map List.length).sum ≤ input.length := by
  simpa only [List.length_flatten] using (chunks_prefix hp).length_le

private theorem lookup_idxOf (w : List Char) (ws : List (List Char)) (hw : w ∈ ws) :
    ws[ws.idxOf w]? = some w := by
  induction ws with
  | nil => simp at hw
  | cons a ws ih =>
    by_cases ha : a = w
    · subst a; simp
    · have hm : w ∈ ws := (List.mem_cons.mp hw).resolve_left (fun h => ha h.symm)
      simpa [List.idxOf_cons,show (a == w) = false from beq_eq_false_iff_ne.mpr ha] using ih hm

theorem views_lookup (parts : List (List Char)) (k : Nat) (hk : k ≤ parts.length) :
    (views parts)[k]? = some (parts.take k).flatten := by
  rw [views,List.getElem?_scanl,if_pos hk]
  congr 1
  simpa using (List.foldl_append_eq_append (l := parts.take k) (f := id) (l' := ([] : List Char)))

theorem rank_correct {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input) {w : List Char} (hw : w ∈ words) :
    (views (chunks words)).idxOf w ≤ words.length ∧
      ((chunks words).take ((views (chunks words)).idxOf w)).flatten = w := by
  have hm : w ∈ views (chunks words) := by
    rw [views_eq hp]; exact List.mem_cons_of_mem _ ((ordered_perm words).mem_iff.mpr hw)
  have hk := List.idxOf_lt_length_of_mem hm
  have hlen : (views (chunks words)).length = words.length + 1 := by
    simp [views,List.length_scanl,chunks_length]
  have hb : (views (chunks words)).idxOf w ≤ words.length := by omega
  refine ⟨hb,?_⟩
  have hv := views_lookup (chunks words) _ (by simpa [chunks_length] using hb)
  rw [lookup_idxOf w _ hm] at hv
  exact (Option.some.inj hv).symm

theorem ranks_length (words : List (List Char)) : (ranks words).length = words.length := by
  simp [ranks]

theorem ranks_bounded {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input) : ∀ k ∈ ranks words, k ≤ words.length := by
  intro k hk
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hk
  exact (rank_correct hp hw).1

theorem reconstruct {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input) :
    (ranks words).map (fun k => ((chunks words).take k).flatten) = words := by
  simp only [ranks,List.map_map]
  exact (List.map_congr_left (fun w hw => (rank_correct hp hw).2)).trans (List.map_id _)

theorem ranks_mem_controls {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input) : ranks words ∈ controls words.length words.length :=
  (mem_controls _ _ _).mpr ⟨ranks_length words,ranks_bounded hp⟩

/-- All successful Par captures are prefixes of one common caller input. -/
theorem par_prefixes {g : MGrammar} {s : Strategy} {input : List Char} {args vals : List MExp}
    (h : DerivesArgsPar g s input args vals) :
    ∃ words : List (List Char), vals = words.map MExp.lit ∧ words.length = args.length ∧
      ∀ w ∈ words, w <+: input := by
  induction args generalizing vals with
  | nil => cases h; exact ⟨[],rfl,rfl,by simp⟩
  | cons a args ih =>
    cases h with
    | cons _ _ _ w rest _ vs _ hp ht =>
      obtain ⟨words,hv,hlen,hw⟩ := ih ht
      refine ⟨w::words,by simp [hv],by simp [hlen],?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨rest,hp.symm⟩
      · exact hw b hb

/-- Arbitrarily many, arbitrarily long Par captures have a fixed-arity
disjoint representation, with finite rank control and no information loss.
The literal Seq argument list here depends on the evaluated values. -/
theorem par_representation {g : MGrammar} {s : Strategy} {input : List Char} {args vals : List MExp}
    (h : DerivesArgsPar g s input args vals) :
    ∃ (parts : List (List Char)) (control : List Nat) (rest : List Char),
      parts.length = args.length ∧ control.length = args.length ∧
      (∀ k ∈ control, k ≤ args.length) ∧ input = parts.flatten ++ rest ∧
      vals = (control.map (fun k => (parts.take k).flatten)).map MExp.lit ∧
      DerivesArgsSeq g s input (parts.map MExp.lit) (parts.map MExp.lit) rest := by
  obtain ⟨words,hv,hlen,hp⟩ := par_prefixes h
  obtain ⟨rest,hr⟩ := chunks_prefix hp
  refine ⟨chunks words,ranks words,rest,(chunks_length words).trans hlen,
    (ranks_length words).trans hlen,?_,hr.symm,?_,?_⟩
  · simpa only [hlen] using ranks_bounded hp
  · rw [reconstruct hp]; exact hv
  · exact (SequentialCaptures.forward_iff g s (chunks words) input rest _).mpr ⟨rfl,hr.symm⟩

end Shallot.MacroPeg.CBV.CommonOriginCaptures
