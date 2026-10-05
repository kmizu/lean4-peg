import Complexity.RedTmpl
import Complexity.TmplLM
import Complexity.StepSem

/-!
# Well-formedness and smallness of `redTmpl M`
-/

namespace Complexity

/-- Well-formed, small, and looping only over counters in `L`. -/
def WfG (Z : Nat) (L : List Nat) (t : Tmpl) : Prop :=
  t.WF 4 ∧ t.Small Z ∧ ∀ i ∈ t.loops, i ∈ L

def WfCond (Z : Nat) (c : Cond) : Prop := c.WF 4 ∧ c.Small Z
def WfPOK (Z : Nat) (ps : List Part) : Prop := ∀ p ∈ ps, p.WF 4 ∧ p.Small Z

section
variable {Z : Nat} {L L' : List Nat}

theorem WfG.mono {t : Tmpl} (h : WfG Z L t) (hs : ∀ i, i ∈ L → i ∈ L') : WfG Z L' t :=
  ⟨h.1, h.2.1, fun i hi => hs i (h.2.2 i hi)⟩

theorem wfg_nil : WfG Z L .nil := ⟨trivial, trivial, by simp [Tmpl.loops]⟩

theorem wfg_tok {t : Nat} (h : t < 16) : WfG Z L (.tok t) := ⟨trivial, h, by simp [Tmpl.loops]⟩

theorem wfg_name {ps : List Part} (h : WfPOK Z ps) : WfG Z L (.name ps) :=
  ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2, by simp [Tmpl.loops]⟩

theorem wfg_seq {a b : Tmpl} (ha : WfG Z L a) (hb : WfG Z L b) : WfG Z L (.seq a b) := by
  refine ⟨⟨ha.1, hb.1⟩, ⟨ha.2.1, hb.2.1⟩, ?_⟩
  intro i hi
  simp only [Tmpl.loops, List.mem_append] at hi
  rcases hi with hi | hi
  · exact ha.2.2 i hi
  · exact hb.2.2 i hi

theorem wfg_seqs : ∀ {ts : List Tmpl}, (∀ t ∈ ts, WfG Z L t) → WfG Z L (Tmpl.seqs ts)
  | [], _ => wfg_nil
  | t :: ts, h => wfg_seq (h t (by simp)) (wfg_seqs (fun u hu => h u (by simp [hu])))

theorem wfg_ite {c : Cond} {a b : Tmpl} (hc : WfCond Z c) (ha : WfG Z L a) (hb : WfG Z L b) :
    WfG Z L (.ite c a b) := by
  refine ⟨⟨hc.1, ha.1, hb.1⟩, ⟨hc.2, ha.2.1, hb.2.1⟩, ?_⟩
  intro i hi
  simp only [Tmpl.loops, List.mem_append] at hi
  rcases hi with hi | hi
  · exact ha.2.2 i hi
  · exact hb.2.2 i hi

theorem wfg_forR {i : Nat} {b : Bound} {body : Tmpl} (hi : i < 4) (hL : i ∉ L)
    (hb : match b with | .const n => n ≤ Z | _ => True) (h : WfG Z L body) :
    WfG Z (i :: L) (.forR i b body) := by
  refine ⟨⟨hi, fun hm => hL (h.2.2 i hm), h.1⟩, ⟨hb, h.2.1⟩, ?_⟩
  intro j hj
  simp only [Tmpl.loops, List.mem_cons] at hj
  rcases hj with hj | hj
  · simp [hj]
  · exact List.mem_cons_of_mem _ (h.2.2 j hj)

/-- A loop over a loop-free body. -/
theorem wfg_loop {i : Nat} {b : Bound} {body : Tmpl} (hi : i < 4) (hiL : i ∈ L)
    (hb : match b with | .const n => n ≤ Z | _ => True) (h : WfG Z [] body) :
    WfG Z L (.forR i b body) :=
  (wfg_forR hi (by simp) hb h).mono (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj; exact hiL)

/-! ### Conditions and parts -/

theorem wfcond_and {c d : Cond} (h : WfCond Z c) (h' : WfCond Z d) : WfCond Z (.and c d) :=
  ⟨⟨h.1, h'.1⟩, ⟨h.2, h'.2⟩⟩
theorem wfcond_or {c d : Cond} (h : WfCond Z c) (h' : WfCond Z d) : WfCond Z (.or c d) :=
  ⟨⟨h.1, h'.1⟩, ⟨h.2, h'.2⟩⟩
theorem wfcond_tt : WfCond Z .tt := ⟨trivial, trivial⟩
theorem wfcond_eqc {i n : Nat} (hi : i < 4) (hn : n ≤ Z) : WfCond Z (.eqc i n) := ⟨hi, hn⟩

theorem WfPOK_nil : WfPOK Z [] := by intro p hp; simp at hp
theorem WfPOK_cons {p : Part} {ps : List Part} (hp : p.WF 4 ∧ p.Small Z) (h : WfPOK Z ps) : WfPOK Z (p :: ps) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact h q hq
theorem WfPOK_append {a b : List Part} (ha : WfPOK Z a) (hb : WfPOK Z b) : WfPOK Z (a ++ b) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact ha q hq
  · exact hb q hq

theorem WfPOK_const {n : Nat} (h : n ≤ Z) (ps : List Part) (hps : WfPOK Z ps) : WfPOK Z (.const n :: ps) :=
  WfPOK_cons ⟨trivial, h⟩ hps
theorem WfPOK_ctr {i : Nat} (hi : i < 4) (ps : List Part) (hps : WfPOK Z ps) : WfPOK Z (.ctr i :: ps) :=
  WfPOK_cons ⟨hi, trivial⟩ hps
theorem WfPOK_rev {i c : Nat} (hi : i < 4) (hc : c ≤ Z) (ps : List Part) (hps : WfPOK Z ps) :
    WfPOK Z (.rev i c :: ps) :=
  WfPOK_cons ⟨hi, hc⟩ hps

/-! ### Combinators -/

theorem wfg_var {ps : List Part} (h : WfPOK Z ps) : WfG Z L (T.var ps) :=
  wfg_seq (wfg_tok (by decide)) (wfg_name h)

theorem wfg_not {a : Tmpl} (h : WfG Z L a) : WfG Z L (T.not a) := wfg_seq h (wfg_tok (by decide))

theorem wfg_and {a b : Tmpl} (ha : WfG Z L a) (hb : WfG Z L b) : WfG Z L (T.and a b) := by
  unfold T.and
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact wfg_tok (by decide)

theorem wfg_or {a b : Tmpl} (ha : WfG Z L a) (hb : WfG Z L b) : WfG Z L (T.or a b) := by
  unfold T.or
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact wfg_tok (by decide)

theorem wfg_iff {a b : Tmpl} (ha : WfG Z L a) (hb : WfG Z L b) : WfG Z L (T.iff a b) :=
  wfg_or (wfg_and ha hb) (wfg_and (wfg_not ha) (wfg_not hb))

theorem wfg_bigAndL {ts : List Tmpl} (h : ∀ t ∈ ts, WfG Z L t) : WfG Z L (T.bigAndL ts) := by
  unfold T.bigAndL
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at ht
  rcases ht with (ht | rfl) | ⟨u, _, rfl⟩
  · exact h t ht
  · exact wfg_tok (by decide)
  · exact wfg_tok (by decide)

theorem wfg_bigOrL {ts : List Tmpl} (h : ∀ t ∈ ts, WfG Z L t) : WfG Z L (T.bigOrL ts) := by
  unfold T.bigOrL
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at ht
  rcases ht with (ht | rfl) | ⟨u, _, rfl⟩
  · exact h t ht
  · exact wfg_tok (by decide)
  · exact wfg_tok (by decide)

theorem wfg_bigAndF {i : Nat} {b : Bound} {c : Cond} {body : Tmpl} (hi : i < 4) (hiL : i ∈ L)
    (hb : match b with | .const n => n ≤ Z | _ => True) (hc : WfCond Z c) (h : WfG Z [] body) :
    WfG Z L (T.bigAndF i b c body) := by
  unfold T.bigAndF
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact wfg_loop hi hiL hb (wfg_ite hc h wfg_nil)
  · exact wfg_tok (by decide)
  · exact wfg_loop hi hiL hb (wfg_ite hc (wfg_tok (by decide)) wfg_nil)

theorem wfg_bigOrF {i : Nat} {b : Bound} {c : Cond} {body : Tmpl} (hi : i < 4) (hiL : i ∈ L)
    (hb : match b with | .const n => n ≤ Z | _ => True) (hc : WfCond Z c) (h : WfG Z [] body) :
    WfG Z L (T.bigOrF i b c body) := by
  unfold T.bigOrF
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact wfg_loop hi hiL hb (wfg_ite hc h wfg_nil)
  · exact wfg_tok (by decide)
  · exact wfg_loop hi hiL hb (wfg_ite hc (wfg_tok (by decide)) wfg_nil)

theorem wf_pairsOf_mem {α : Type} {p : α × α} : ∀ {vs : List α}, p ∈ pairsOf vs → p.1 ∈ vs ∧ p.2 ∈ vs
  | [], h => by simp [pairsOf] at h
  | x :: xs, h => by
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · exact ⟨by simp, by simp [hy]⟩
    · have := wf_pairsOf_mem h
      exact ⟨by simp [this.1], by simp [this.2]⟩

end

/-! ### Pieces -/

section Pieces
variable {k : Nat} (M : TM k) {Z : Nat} (hZ : M.nq + M.na + k + 16 ≤ Z)
include hZ

theorem WfPOK_c0 (q : Nat) (hq : q < M.nq) : WfPOK Z [.const 0, .const q] :=
  WfPOK_const (by omega) _ (WfPOK_const (by omega) _ WfPOK_nil)

theorem WfPOK_c1 (i c : Nat) (hi : i < k) (hc : c < 4) : WfPOK Z [.const 1, .const i, .ctr c] :=
  WfPOK_const (by omega) _ (WfPOK_const (by omega) _ (WfPOK_ctr hc _ WfPOK_nil))

theorem WfPOK_c2 (i c s : Nat) (hi : i < k) (hc : c < 4) (hs : s < M.na) :
    WfPOK Z [.const 2, .const i, .ctr c, .const s] :=
  WfPOK_const (by omega) _ (WfPOK_const (by omega) _ (WfPOK_ctr hc _ (WfPOK_const (by omega) _ WfPOK_nil)))

theorem wfg_block (body : List Part → Tmpl) (hb : ∀ v, WfPOK Z v → WfG Z [] (body v)) {L : List Nat}
    (h1 : 1 ∈ L) : ∀ t ∈ T.block M body, WfG Z L t := by
  intro t ht
  unfold T.block at ht
  simp only [List.mem_append, List.mem_map, List.mem_range] at ht
  rcases ht with (⟨q, hq, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · exact (hb _ (WfPOK_c0 M hZ q hq)).mono (by simp)
  · exact wfg_loop (by omega) h1 trivial (hb _ (WfPOK_c1 M hZ i 1 hi (by omega)))
  · refine wfg_loop (by omega) h1 trivial ?_
    refine wfg_seqs ?_
    intro u hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
    exact hb _ (WfPOK_c2 M hZ i 1 s hi (by omega) (List.mem_range.mp hs))

theorem wfg_bigAndBlock (body : List Part → Tmpl) (hb : ∀ v, WfPOK Z v → WfG Z [] (body v)) {L : List Nat}
    (h1 : 1 ∈ L) : WfG Z L (T.bigAndBlock M body) := by
  unfold T.bigAndBlock
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with (ht | rfl) | ht
  · exact wfg_block M hZ body hb h1 t ht
  · exact wfg_tok (by decide)
  · exact wfg_block M hZ _ (fun _ _ => wfg_tok (by decide)) h1 t ht

theorem wfg_initT (tag : List Part) (htag : WfPOK Z tag) {L : List Nat} (h1 : 1 ∈ L) :
    WfG Z L (initT M tag) := by
  unfold initT
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ht
  have hv : ∀ v, WfPOK Z v → WfG Z L (T.var (tag ++ v)) := fun v hv => wfg_var (WfPOK_append htag hv)
  have hn : ∀ v, WfPOK Z v → WfG Z L (T.not (T.var (tag ++ v))) := fun v hv0 => wfg_not (hv v hv0)
  rcases ht with (((⟨q, hq, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | rfl) | ht
  · split
    · exact hv _ (WfPOK_c0 M hZ q hq)
    · exact hn _ (WfPOK_c0 M hZ q hq)
  · have hp := WfPOK_c1 M hZ i 1 hi (by omega)
    refine wfg_loop (by omega) h1 trivial ?_
    exact wfg_ite (wfcond_eqc (by omega) (by omega)) (wfg_var (WfPOK_append htag hp)) (wfg_not (wfg_var (WfPOK_append htag hp)))
  · refine wfg_loop (by omega) h1 trivial (wfg_seqs ?_)
    intro u hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
    have hp := WfPOK_c2 M hZ i 1 s hi (by omega) (List.mem_range.mp hs)
    refine wfg_ite ?_ (wfg_var (WfPOK_append htag hp)) (wfg_not (wfg_var (WfPOK_append htag hp)))
    unfold initCellCond
    repeat' split
    all_goals simp [WfCond, Cond.WF, Cond.Small]
  · exact wfg_tok (by decide)
  · exact wfg_block M hZ _ (fun _ _ => wfg_tok (by decide)) h1 t ht

theorem wfg_eqT (b b' : List Part) (hb : WfPOK Z b) (hb' : WfPOK Z b') {L : List Nat} (h1 : 1 ∈ L) :
    WfG Z L (eqT M b b') :=
  wfg_bigAndBlock M hZ _ (fun v hv => wfg_iff (wfg_var (WfPOK_append hb hv)) (wfg_var (WfPOK_append hb' hv))) h1

theorem wfg_accT (b : List Part) (hb : WfPOK Z b) {L : List Nat} : WfG Z L (accT b) :=
  wfg_var (WfPOK_append hb (WfPOK_c0 M hZ 0 (by have := M.three_le_nq; omega)))

omit hZ in
theorem wfg_exOneL (vs : List (List Part)) (h : ∀ v ∈ vs, WfPOK Z v) {L : List Nat} : WfG Z L (exOneL vs) := by
  unfold exOneL
  refine wfg_and (wfg_bigOrL ?_) (wfg_bigAndL ?_)
  · intro t ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    exact wfg_var (h v hv)
  · intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    have := wf_pairsOf_mem hp
    exact wfg_not (wfg_and (wfg_var (h _ this.1)) (wfg_var (h _ this.2)))

omit hZ in
theorem wfg_loop12 {body : Tmpl} (h : WfG Z [] body) {L : List Nat} (h1 : 1 ∈ L) (h2 : 2 ∈ L) :
    WfG Z L (.forR 1 .S (.forR 2 .S body)) :=
  (wfg_forR (L := [2]) (by omega) (by simp) trivial (wfg_loop (by omega) (by simp) trivial h)).mono (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact h1
    · exact h2)

theorem wfg_exOneHead (b : List Part) (hb : WfPOK Z b) (i : Nat) (hi : i < k) {L : List Nat}
    (h1 : 1 ∈ L) (h2 : 2 ∈ L) : WfG Z L (exOneHead b i) := by
  have p1 := WfPOK_append hb (WfPOK_c1 M hZ i 1 hi (by omega))
  have p2 := WfPOK_append hb (WfPOK_c1 M hZ i 2 hi (by omega))
  have hc : WfCond Z (.lt 1 2) := by simp [WfCond, Cond.WF, Cond.Small]
  unfold exOneHead
  refine wfg_and (wfg_bigOrF (by omega) h1 trivial wfcond_tt (wfg_var p1)) (wfg_seqs ?_)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact wfg_loop12 (wfg_ite hc (wfg_not (wfg_and (wfg_var p1) (wfg_var p2))) wfg_nil) h1 h2
  · exact wfg_tok (by decide)
  · exact wfg_loop12 (wfg_ite hc (wfg_tok (by decide)) wfg_nil) h1 h2

theorem wfg_wfT (b : List Part) (hb : WfPOK Z b) {L : List Nat} (h1 : 1 ∈ L) (h2 : 2 ∈ L) :
    WfG Z L (wfT M b) := by
  unfold wfT
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_append, List.mem_map, List.mem_singleton, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with ((((rfl | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · exact wfg_exOneL _ (by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      exact WfPOK_append hb (WfPOK_c0 M hZ q (List.mem_range.mp hq))) 
  · exact wfg_exOneHead M hZ b hb i hi h1 h2
  · refine wfg_loop (by omega) h1 trivial (wfg_exOneL _ ?_)
    intro v hv
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
    exact WfPOK_append hb (WfPOK_c2 M hZ i 1 s hi (by omega) (List.mem_range.mp hs))
  · exact wfg_tok (by decide)
  · exact wfg_tok (by decide)
  · exact wfg_tok (by decide)
  · exact wfg_loop (by omega) h1 trivial (wfg_tok (by decide))

theorem wfg_readT (b : List Part) (hb : WfPOK Z b) (i s : Nat) (hi : i < k) (hs : s < M.na) {L : List Nat}
    (h3 : 3 ∈ L) : WfG Z L (readT b i s) :=
  wfg_bigOrF (by omega) h3 trivial wfcond_tt
    (wfg_and (wfg_var (WfPOK_append hb (WfPOK_c1 M hZ i 3 hi (by omega))))
      (wfg_var (WfPOK_append hb (WfPOK_c2 M hZ i 3 s hi (by omega) hs))))

theorem wfg_combT (b : List Part) (hb : WfPOK Z b) (q : Nat) (r : Fin k → Nat) (hq : q < M.nq)
    (hr : ∀ i, r i < M.na) {L : List Nat} (h3 : 3 ∈ L) : WfG Z L (combT b q r) := by
  unfold combT
  refine wfg_and (wfg_var (WfPOK_append hb (WfPOK_c0 M hZ q hq))) (wfg_bigAndL ?_)
  intro t ht
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
  exact wfg_readT M hZ b hb i.val (r i) i.isLt (hr i) h3

theorem wfg_combs (b : List Part) (hb : WfPOK Z b) (f : Nat × (Fin k → Nat) → Bool) {L : List Nat}
    (h3 : 3 ∈ L) : ∀ t ∈ ((combos M).filter f).map (fun p => combT b p.1 p.2), WfG Z L t := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  have := (mem_combos M p).mp (List.mem_filter.mp hp).1
  exact wfg_combT M hZ b hb p.1 p.2 this.1 this.2 h3

theorem wfg_stateBitsT (b b' : List Part) (hb : WfPOK Z b) (hb' : WfPOK Z b') {L : List Nat}
    (h3 : 3 ∈ L) : ∀ t ∈ stateBitsT M b b', WfG Z L t := by
  intro t ht
  unfold stateBitsT at ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact wfg_iff (wfg_var (WfPOK_append hb' (WfPOK_c0 M hZ q (List.mem_range.mp hq))))
    (wfg_bigOrL (wfg_combs M hZ b hb _ h3))

omit hZ in
theorem wfcond_moveCond (m : Move) : WfCond Z (moveCond m) := by
  cases m <;> simp [moveCond, WfCond, Cond.WF, Cond.Small]

theorem wfg_headBitT (b b' : List Part) (hb : WfPOK Z b) (hb' : WfPOK Z b') (i : Fin k) {L : List Nat}
    (h2 : 2 ∈ L) (h3 : 3 ∈ L) : WfG Z L (headBitT M b b' i) := by
  unfold headBitT
  refine wfg_iff (wfg_var (WfPOK_append hb' (WfPOK_c1 M hZ i.val 1 i.isLt (by omega)))) (wfg_bigOrL ?_)
  intro t ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  have := (mem_combos M p).mp hp
  exact wfg_and (wfg_combT M hZ b hb p.1 p.2 this.1 this.2 h3)
    (wfg_bigOrF (by omega) h2 trivial (wfcond_moveCond _)
      (wfg_var (WfPOK_append hb (WfPOK_c1 M hZ i.val 2 i.isLt (by omega)))))

theorem wfg_cellBitT (b b' : List Part) (hb : WfPOK Z b) (hb' : WfPOK Z b') (i : Fin k) (s : Nat)
    (hs : s < M.na) {L : List Nat} (h3 : 3 ∈ L) : WfG Z L (cellBitT M b b' i s) := by
  unfold cellBitT
  have e1 := WfPOK_append hb (WfPOK_c1 M hZ i.val 1 i.isLt (by omega))
  have e2 := WfPOK_append hb (WfPOK_c2 M hZ i.val 1 s i.isLt (by omega) hs)
  exact wfg_iff (wfg_var (WfPOK_append hb' (WfPOK_c2 M hZ i.val 1 s i.isLt (by omega) hs)))
    (wfg_or (wfg_and (wfg_not (wfg_var e1)) (wfg_var e2))
      (wfg_and (wfg_var e1) (wfg_bigOrL (wfg_combs M hZ b hb _ h3))))

theorem wfg_stepT (b b' : List Part) (hb : WfPOK Z b) (hb' : WfPOK Z b') {L : List Nat}
    (h1 : 1 ∈ L) (h2 : 2 ∈ L) (h3 : 3 ∈ L) : WfG Z L (stepT M b b') := by
  unfold stepT
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_append, List.mem_map, List.mem_singleton, List.mem_range, List.mem_finRange,
    true_and] at ht
  rcases ht with (((((ht | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl) | ⟨q, hq, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact wfg_stateBitsT M hZ b b' hb hb' h3 t (by unfold stateBitsT; exact ht)
  · refine (wfg_forR (L := [2, 3]) (by omega) (by simp) trivial
      (wfg_headBitT M hZ b b' hb hb' i (by simp) (by simp))).mono ?_
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> assumption
  · refine (wfg_forR (L := [3]) (by omega) (by simp) trivial (wfg_seqs ?_)).mono ?_
    · intro u hu
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
      exact wfg_cellBitT M hZ b b' hb hb' i s (List.mem_range.mp hs) (by simp)
    · intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl <;> assumption
  · exact wfg_tok (by decide)
  · exact wfg_tok (by decide)
  · exact wfg_loop (by omega) h1 trivial (wfg_tok (by decide))
  · exact wfg_loop (by omega) h1 trivial (wfg_seqs (by
      intro u hu
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hu
      exact wfg_tok (by decide)))

theorem wfg_guardT (X Y Mi A B : List Part) (hX : WfPOK Z X) (hY : WfPOK Z Y) (hMi : WfPOK Z Mi)
    (hA : WfPOK Z A) (hB : WfPOK Z B) {L : List Nat} (h1 : 1 ∈ L) : WfG Z L (guardT M X Y Mi A B) :=
  wfg_or (wfg_and (wfg_eqT M hZ _ _ hA hX h1) (wfg_eqT M hZ _ _ hB hMi h1))
    (wfg_and (wfg_eqT M hZ _ _ hA hMi h1) (wfg_eqT M hZ _ _ hB hY h1))

theorem wfPOK_tagX : WfPOK Z tagX :=
  WfPOK_const (by omega) _ (WfPOK_const (by omega) _ WfPOK_nil)
theorem wfPOK_tagY : WfPOK Z tagY :=
  WfPOK_const (by omega) _ (WfPOK_const (by omega) _ WfPOK_nil)
theorem wfPOK_tagL (i : Nat) (hi : i ≤ 2) : WfPOK Z (tagL i) :=
  WfPOK_rev (by omega) (by omega) _ (WfPOK_const (by omega) _ WfPOK_nil)
theorem wfPOK_tagP (i : Nat) (hi : i ≤ 2) : WfPOK Z (tagP i) :=
  WfPOK_rev (by omega) (by omega) _ (WfPOK_const (by omega) _ WfPOK_nil)

theorem wfg_levelT {L : List Nat} (h1 : 1 ∈ L) (h2 : 2 ∈ L) : WfG Z L (levelT M) := by
  unfold levelT
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact wfg_wfT M hZ _ (wfPOK_tagL M hZ 0 (by omega)) h1 h2
  · exact wfg_ite (wfcond_eqc (by omega) (by omega))
      (wfg_guardT M hZ _ _ _ _ _ (wfPOK_tagX M hZ) (wfPOK_tagY M hZ) (wfPOK_tagL M hZ 0 (by omega))
        (wfPOK_tagL M hZ 1 (by omega)) (wfPOK_tagL M hZ 2 (by omega)) h1)
      (wfg_guardT M hZ _ _ _ _ _ (wfPOK_tagP M hZ 1 (by omega)) (wfPOK_tagP M hZ 2 (by omega))
        (wfPOK_tagL M hZ 0 (by omega)) (wfPOK_tagL M hZ 1 (by omega)) (wfPOK_tagL M hZ 2 (by omega)) h1)
  · exact wfg_tok (by decide)

theorem wfg_baseT {L : List Nat} (h1 : 1 ∈ L) (h2 : 2 ∈ L) (h3 : 3 ∈ L) : WfG Z L (baseT M) := by
  have p1 : WfPOK Z [.const 1, .const 1] := WfPOK_const (by omega) _ (WfPOK_const (by omega) _ WfPOK_nil)
  have p2 : WfPOK Z [.const 1, .const 2] := WfPOK_const (by omega) _ (WfPOK_const (by omega) _ WfPOK_nil)
  exact wfg_or (wfg_eqT M hZ _ _ p1 p2 h1) (wfg_stepT M hZ _ _ p1 p2 h1 h2 h3)

theorem wfg_sideT {L : List Nat} (h1 : 1 ∈ L) (h2 : 2 ∈ L) : WfG Z L (sideT M) :=
  wfg_and (wfg_initT M hZ _ (wfPOK_tagX M hZ) h1)
    (wfg_and (wfg_wfT M hZ _ (wfPOK_tagY M hZ) h1 h2) (wfg_accT M hZ _ (wfPOK_tagY M hZ)))

theorem wfg_matrixT : WfG Z [0, 1, 2, 3] (matrixT M) := by
  unfold matrixT
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact wfg_sideT M hZ (by simp) (by simp)
  · exact (wfg_forR (L := [1, 2]) (by omega) (by simp) trivial (wfg_levelT M hZ (by simp) (by simp))).mono
      (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
  · exact wfg_baseT M hZ (by simp) (by simp) (by simp)
  · exact wfg_loop (by omega) (by simp) trivial (wfg_seqs (by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact wfg_tok (by decide)))
  · exact wfg_tok (by decide)

theorem wfg_quantBlockT (kind : Nat) (hk : kind < 16) (tag : List Part) (htag : WfPOK Z tag) {L : List Nat}
    (h1 : 1 ∈ L) : WfG Z L (quantBlockT M kind tag) :=
  wfg_seqs (wfg_block M hZ _ (fun v hv => wfg_seq (wfg_tok hk) (wfg_name (WfPOK_append htag hv))) h1)

theorem wfg_prefixT : WfG Z [0, 1] (prefixT M) := by
  unfold prefixT
  refine wfg_seqs ?_
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact wfg_quantBlockT M hZ _ (by decide) _ (wfPOK_tagX M hZ) (by simp)
  · exact wfg_quantBlockT M hZ _ (by decide) _ (wfPOK_tagY M hZ) (by simp)
  · refine (wfg_forR (L := [1]) (by omega) (by simp) trivial (wfg_seqs ?_)).mono ?_
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · exact wfg_quantBlockT M hZ _ (by decide) _ (wfPOK_tagL M hZ 0 (by omega)) (by simp)
      · exact wfg_quantBlockT M hZ _ (by decide) _ (wfPOK_tagL M hZ 1 (by omega)) (by simp)
      · exact wfg_quantBlockT M hZ _ (by decide) _ (wfPOK_tagL M hZ 2 (by omega)) (by simp)
    · intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega

theorem wfg_redTmpl : WfG Z [0, 1, 2, 3] (redTmpl M) :=
  wfg_seq ((wfg_prefixT M hZ).mono (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega))
    (wfg_matrixT M hZ)

end Pieces

theorem redTmpl_WF {k : Nat} (M : TM k) : (redTmpl M).WF 4 :=
  (wfg_redTmpl M (Z := M.nq + M.na + k + 16) (Nat.le_refl _)).1

theorem redTmpl_small {k : Nat} (M : TM k) (Z : Nat) (hZ : M.nq + M.na + k + 16 ≤ Z) : (redTmpl M).Small Z :=
  (wfg_redTmpl M hZ).2.1

end Complexity
