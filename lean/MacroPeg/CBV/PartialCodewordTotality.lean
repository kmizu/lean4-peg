import MacroPeg.CBV.PartialCodewordPreflight

/-! Total lexical entry computations. Empty-star continuations remain
partial; only the generated capture and its checker are proved total. -/
namespace Shallot.MacroPeg.CBV.PartialCodewordTotality
open PartialCodewordCapture (runA argument look)
open RuntimeShiftFilter (scanner)
open ClockFreezing (Table)

theorem literal_total (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (w : List Char) (p : Nat) :
    ∃ r, evV g x s T E (.lit w) p=some r := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => exact ⟨none,by simp [evV,hs]⟩
  | some rest => exact ⟨some rest.length,by simp [evV,hs]⟩

theorem param_total (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (k p : Nat) :
    ∃ r, evV g x s T E (.param k) p=some r := by
  cases he : E[k]? with
  | none => exact ⟨none,by simp [evV,he]⟩
  | some w => simpa only [evV,he] using literal_total g x s T [] w p

private theorem seq_total (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (a b : MExp) (p : Nat) (hp : p≤x.length)
    (ha : ∃ r, evV g x s T E a p=some r)
    (hb : ∀ q, q≤x.length → ∃ r, evV g x s T E b q=some r) :
    ∃ r, evV g x s T E (.seq a b) p=some r := by
  obtain ⟨r,hr⟩ := ha
  cases r with
  | none => exact ⟨none,evV_seq_fail hr⟩
  | some q =>
    obtain ⟨r,hr'⟩ := hb q (evV_ok hT _ p hp q hr)
    exact ⟨r,by rw [evV_seq_ok hr]; exact hr'⟩

private theorem negative_total (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a : MExp) (p : Nat)
    (ha : ∃ r, evV g x s T E a p=some r) :
    ∃ r, evV g x s T E (.notP a) p=some r := by
  obtain ⟨r,hr⟩ := ha
  cases r with
  | none => exact ⟨some p,evV_not_fail hr⟩
  | some q => exact ⟨none,evV_not_ok hr⟩

private theorem star_total (n : Nat) (f : Nat → Res)
    (ht : ∀ p, p≤n → ∃ r, f p=some r)
    (hs : ∀ p q, p≤n → f p=some (some q) → q<p) :
    ∀ p, p≤n → ∃ q, evStar f p=some (some q) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp
    obtain ⟨r,hr⟩ := ht p hp
    cases r with
    | none => exact ⟨p,evStar_fail hr⟩
    | some q =>
      have hq := hs p q hp hr
      obtain ⟨r,hr'⟩ := ih q hq (by omega)
      exact ⟨r,by rw [evStar_ok hr hq]; exact hr'⟩

private theorem hash_strict (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E (.lit ['#']) p=some (some q)) : q<p := by
  cases hs : Shallot.stripPrefix? ['#'] (sfx x p) with
  | none => simp [evV,hs] at h
  | some rest =>
    have he : rest.length=q := by simpa only [evV,hs,Option.some.injEq] using h
    have hh := congrArg List.length ((CBVtoCBN.stripPrefix_exact _ _ _).mp hs)
    rw [length_sfx x hp,List.length_append,List.length_singleton] at hh
    omega

private theorem literal_le (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (w : List Char) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E (.lit w) p=some (some q)) : q≤p := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [evV,hs] at h
  | some rest =>
    have he : rest.length=q := by simpa only [evV,hs,Option.some.injEq] using h
    have hh := congrArg List.length ((CBVtoCBN.stripPrefix_exact _ _ _).mp hs)
    rw [length_sfx x hp,List.length_append] at hh
    omega

private theorem look_le (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a : MExp) (p q : Nat)
    (h : evV g x s T E (look a) p=some (some q)) : q≤p := by
  change evV g x s T E (.andP a) p=_ at h
  rw [CallLookahead.evV_peek] at h
  cases ha : evV g x s T E a p with
  | none => simp [CallLookahead.peek,ha] at h
  | some r => cases r with
    | none => simp [CallLookahead.peek,ha] at h
    | some z => have he : p=q := by simpa [CallLookahead.peek,ha] using h
                omega

private theorem seq_strict_left (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (a b : MExp) (p q : Nat)
    (hp : p≤x.length)
    (ha : ∀ j, evV g x s T E a p=some (some j) → j<p)
    (hb : ∀ j q, j≤x.length → evV g x s T E b j=some (some q) → q≤j)
    (h : evV g x s T E (.seq a b) p=some (some q)) : q<p := by
  cases hr : evV g x s T E a p with
  | none => rw [evV_seq_none hr] at h; cases h
  | some r => cases r with
    | none => rw [evV_seq_fail hr] at h; cases h
    | some j =>
      rw [evV_seq_ok hr] at h
      have hj := ha j hr
      have hq := hb j q (evV_ok hT a p hp j hr) h
      omega

/-- Every real a-run evaluation succeeds, including the empty run. -/
theorem run_total (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    ∃ q, evV g x s T E runA p=some (some q) := by
  exact ⟨_,NestedScannerArguments.scan_eval g x s T E ['a'] p hp⟩

/-- The full scanner either fails or strictly consumes at least its #. -/
theorem scanner_total_strict (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    (∃ r, evV g x s T E scanner p=some r) ∧
      ∀ q, evV g x s T E scanner p=some (some q) → q<p := by
  obtain ⟨j,hj⟩ := run_total g x s T E p hp
  have hle : j≤p := by
    have hh := hj
    rw [runA,NestedScannerArguments.scan_eval g x s T E ['a'] p hp] at hh
    have he := Option.some.inj (Option.some.inj hh)
    have hb' := congrArg List.length (List.takeWhile_append_dropWhile (p := NestedScannerArguments.accepts ['a']) (l := sfx x p))
    rw [List.length_append,length_sfx x hp] at hb'
    omega
  have hb := evV_ok hT runA p hp j hj
  constructor
  · obtain ⟨r,hr⟩ := literal_total g x s T E ['#'] j
    exact ⟨r,by change evV g x s T E (.seq runA (.lit ['#'])) p=_; rw [evV_seq_ok hj]; exact hr⟩
  · intro q h
    change evV g x s T E (.seq runA (.lit ['#'])) p=_ at h
    rw [evV_seq_ok hj] at h
    have hh := hash_strict g x s T E j q hb h
    omega

/-- The concrete original argument is total on every input and position.
Its successful repetitions consume a #, so it cannot loop empty. -/
theorem argument_total (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    ∃ q, evV g x s T E argument p=some (some q) := by
  let f := fun q => evV g x s T E (.seq scanner (look scanner)) q
  have ht : ∀ q, q≤x.length → ∃ r, f q=some r := by
    intro q hq
    apply seq_total g x s T hT E scanner (look scanner) q hq
    · exact (scanner_total_strict g x s T hT E q hq).1
    · intro j hj
      exact negative_total g x s T E _ j
        (negative_total g x s T E _ j (scanner_total_strict g x s T hT E j hj).1)
  have hs : ∀ p q, p≤x.length → f p=some (some q) → q<p := by
    intro p q hp h
    exact seq_strict_left g x s T hT E scanner (look scanner) p q hp
      (scanner_total_strict g x s T hT E p hp).2
      (fun j q _ hh => look_le g x s T E scanner j q hh) h
  obtain ⟨j,hj⟩ := star_total x.length f ht hs p hp
  have hjle := evStar_le p j hj
  obtain ⟨q,hq⟩ := run_total g x s T E j (by omega)
  refine ⟨q,?_⟩
  change evV g x s T E (.seq (.star (.seq scanner (look scanner))) runA) p=_
  change evV g x s T E (.star (.seq scanner (look scanner))) p=_ at hj
  rw [evV_seq_ok hj]
  exact hq

/-- The checker itself is total for every held word. Its # prefix forces
strict progress even when the held word is empty. -/
theorem checker_total (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (u : List Char) (p : Nat) (hp : p≤x.length) :
    ∃ r, evV g x s T [u] PartialCodewordPreflight.checkBody p=some r := by
  let b := MExp.seq (.param 0) (look (.lit ['#']))
  let f := fun q => evV g x s T [u] (.seq (.lit ['#']) b) q
  have hb : ∀ q, q≤x.length → ∃ r, evV g x s T [u] b q=some r := by
    intro q hq
    apply seq_total g x s T hT [u] _ _ q hq (param_total g x s T [u] 0 q)
    intro j _
    exact negative_total g x s T [u] _ j
      (negative_total g x s T [u] _ j (literal_total g x s T [u] ['#'] j))
  have ht : ∀ q, q≤x.length → ∃ r, f q=some r := by
    intro q hq
    exact seq_total g x s T hT [u] _ b q hq (literal_total g x s T [u] ['#'] q) hb
  have hs : ∀ p q, p≤x.length → f p=some (some q) → q<p := by
    intro p q hp h
    exact seq_strict_left g x s T hT [u] (.lit ['#']) b p q hp
      (fun j hj => hash_strict g x s T [u] p j hp hj) (by
        intro j q hj hh
        cases hv : evV g x s T [u] (.param 0) j with
        | none => rw [evV_seq_none hv] at hh; cases hh
        | some r => cases r with
          | none => rw [evV_seq_fail hv] at hh; cases hh
          | some z =>
            rw [evV_seq_ok hv] at hh
            have hz : z≤j := literal_le g x s T [] u j z hj hv
            have hq := look_le g x s T [u] (.lit ['#']) z q hh
            omega) h
  obtain ⟨j,hj⟩ := star_total x.length f ht hs p hp
  have hjle := evStar_le p j hj
  change ∃ r, evV g x s T [u] (.seq (.star (.seq (.lit ['#']) b))
    (.seq (.lit ['#']) (.seq (.notP scanner) (.param 0)))) p=_
  change evV g x s T [u] (.star (.seq (.lit ['#']) b)) p=_ at hj
  rw [evV_seq_ok hj]
  apply seq_total g x s T hT [u] _ _ j (by omega) (literal_total g x s T [u] ['#'] j)
  intro q hq
  apply seq_total g x s T hT [u] _ _ q hq
  · exact negative_total g x s T [u] scanner q (scanner_total_strict g x s T hT [u] q hq).1
  · intro r _; exact param_total g x s T [u] 0 r

theorem argument_pure : ParserPrefixFusion.Pure argument := by
  simp [argument,runA,look,scanner,NestedScannerArguments.scan,
    NestedScannerArguments.choice,MExp.failAlways,ParserPrefixFusion.Pure]

/-- Capture evaluation uses no rules or retained values, at any clock. -/
theorem argument_context (g g' : MGrammar) (x : List Char) (s s' : Strategy)
    (T T' : Table) (E E' : List (List Char)) (p : Nat) :
    evV g x s T E argument p=evV g' x s' T' E' argument p :=
  ParserPrefixFusion.pure_eval g g' x s s' T T' E E' argument argument_pure p

/-- Once the actual capture is selected, the initial source replay always
returns finite failure or success. Continuations are not evaluated here. -/
theorem prefix_total (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (w : List Char) (p : Nat) (hp : p≤x.length) :
    ∃ r, evV g x s T [w] (.seq scanner (.param 0)) p=some r :=
  seq_total g x s T hT [w] scanner (.param 0) p hp
    (scanner_total_strict g x s T hT [w] p hp).1
    (fun q _ => param_total g x s T [w] 0 q)

/-- The generated physical preflight is total at every positive ordinary
clock. Its user continuation and user rows are irrelevant to this fact. -/
theorem preflight_total (g : MGrammar) (x : List Char) (m p : Nat)
    (E : List (List Char)) (hp : p≤x.length)
    (rule : ruleAtM g.rules 0=some ⟨1,PartialCodewordPreflight.checkBody⟩) :
    ∃ r, evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      (.call 0 [runA]) p=some r := by
  obtain ⟨j,hj⟩ := run_total g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E p hp
  have hbound := evV_ok (tblV_ok g x .callByValueSeq (m+1)) runA p hp j hj
  rw [evV_call_seq rule rfl]
  simp only [evSeqArgs,hj]
  rw [valAt_tblV_succ rule _ hbound]
  exact checker_total g x .callByValueSeq (tblV g x .callByValueSeq m)
    (tblV_ok g x .callByValueSeq m) (pre x p j) j hbound

/-- All-input finite failure correspondence before the continuation,
for the original captured value and the actual generated preflight. -/
theorem preflight_failure_iff (g g' : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m m' p j : Nat) (E E' : List (List Char)) (hp : p≤x.length)
    (rule : ruleAtM g'.rules 0=some ⟨1,PartialCodewordPreflight.checkBody⟩)
    (ha : evV g x .callByValuePar (tblV g x .callByValuePar m) E argument p=some (some j)) :
    evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
      (.call 0 [runA]) p=some none ↔
    evV g x .callByValuePar (tblV g x .callByValuePar m) [pre x p j]
      (.seq scanner (.param 0)) p=some none := by
  constructor
  · intro hfail
    obtain ⟨r,hr⟩ := prefix_total g x .callByValuePar _ (tblV_ok g x .callByValuePar m) _ p hp
    cases r with
    | none => exact hr
    | some q =>
      have hv := PartialCodewordPreflight.source_to_preflight g g' hg x m m' p j q E E' hp rule ha hr
      rw [hfail] at hv
      cases hv
  · intro hfail
    obtain ⟨r,hr⟩ := preflight_total g' x m' p E' hp rule
    cases r with
    | none => exact hr
    | some q =>
      obtain ⟨j',ha',hv⟩ := PartialCodewordPreflight.preflight_to_source g g' x m m' p q E E' hp rule hr
      have he : j'=j := Option.some.inj (Option.some.inj (ha'.symm.trans ha))
      subst j'
      rw [hfail] at hv
      cases hv

/-- Clock zero remains undefined at a real checker call. Positive-clock
preflight totality must not be incorrectly extended to this seed. -/
theorem preflight_zero (g : MGrammar) (x : List Char) (p : Nat)
    (E : List (List Char)) (hp : p≤x.length)
    (rule : ruleAtM g.rules 0=some ⟨1,PartialCodewordPreflight.checkBody⟩) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq 0) E
      (.call 0 [runA]) p=none := by
  obtain ⟨j,hj⟩ := run_total g x .callByValueSeq (tblV g x .callByValueSeq 0) E p hp
  rw [evV_call_seq rule rfl]
  simp only [evSeqArgs,hj]
  simp only [tblV,valAt_nil]

end Shallot.MacroPeg.CBV.PartialCodewordTotality
