import MacroPeg.CBV.SequentialStackCodec

namespace Shallot.MacroPeg.CBV.SequentialStackCodecBound

open SequentialStack SequentialStackPayload SequentialStackCodec CBVtoCBN

theorem env_length (E : CaptureEnv) : (writeEnv E).length = 1 + 2 * E.length := by
  induction E with
  | nil => rfl
  | cons span E ih =>
    simp only [writeEnv, writeList, List.length_cons, List.flatMap_cons, List.length_append,
      writePair, List.length_nil] at ih ⊢
    omega

theorem exprs_length (ns : List CompileNode) (es : List MExp) :
    (writeExprs ns es).length = 1 + es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [writeExprs, writeList, List.length_cons, List.flatMap_cons, List.length_append,
      writeExpr, List.length_nil] at ih ⊢
    omega

theorem value_length {n A kind v} (h : ValueTyped n A kind v) : (writeValue v).length ≤ 4 + 2 * A := by
  cases h with
  | expr r hr =>
    cases r with
    | none => simp [writeValue, writeRes]; omega
    | some r => cases r <;> simp [writeValue, writeRes] <;> omega
  | args r k hk hr =>
    cases r with
    | none => simp [writeValue, writeArgsRes]; omega
    | some r =>
      cases r with
      | none => simp [writeValue, writeArgsRes]; omega
      | some Wq =>
        obtain ⟨W, q⟩ := Wq
        have hh := (hr W q rfl).1.2
        simp only [writeValue, List.length_cons, writeArgsRes, List.length_append, env_length,
          List.length_nil]
        omega

theorem task_length (ns : List CompileNode) {n A M task kind} (h : TaskTyped n A M task kind) :
    (writeTask ns task).length ≤ 6 + 3 * A := by
  cases h with
  | expr m E e p hm hE hp =>
    have hh := hE.2
    simp only [writeTask, List.length_append, List.length_cons, List.length_nil, writeExpr, env_length]
    omega
  | args m E es p hm hE hp hlen =>
    have hh := hE.2
    simp only [writeTask, List.length_append, List.length_cons, List.length_nil, env_length, exprs_length]
    omega
  | query m i E p hm hE hp =>
    have hh := hE.2
    simp only [writeTask, List.length_append, List.length_cons, List.length_nil, env_length]
    omega
  | value hv =>
    have hh := value_length hv
    simp only [writeTask, List.length_cons]
    omega

theorem frame_length (ns : List CompileNode) {g n A M f kind out} (h : FrameTyped g n A M f kind out) :
    (writeFrame ns f).length ≤ 6 + 3 * A := by
  cases h with
  | seq m E b hm hE =>
    have hh := hE.2
    simp only [writeFrame, List.length_append, List.length_cons, List.length_nil, writeExpr, env_length]
    omega
  | alt m E b p hm hE hp =>
    have hh := hE.2
    simp only [writeFrame, List.length_append, List.length_cons, List.length_nil, writeExpr, env_length]
    omega
  | notP p hp => simp [writeFrame]; omega
  | star m E a p hm hE hp =>
    have hh := hE.2
    simp only [writeFrame, List.length_append, List.length_cons, List.length_nil, writeExpr, env_length]
    omega
  | argHead m E es p hm hE hp hlen =>
    have hh := hE.2
    simp only [writeFrame, List.length_append, List.length_cons, List.length_nil, env_length, exprs_length]
    omega
  | argCons span k hs hk => cases span; simp [writeFrame]; omega
  | call m i rule hm hr ha => simp [writeFrame]; omega

theorem frames_length (ns : List CompileNode) {g n A M kind final K}
    (h : StackTyped g n A M kind K final) : ∀ f ∈ K, (writeFrame ns f).length ≤ 6 + 3 * A := by
  induction h with
  | nil => intro f hf; cases hf
  | cons hhead htail ih =>
    intro f hf
    rcases List.mem_cons.mp hf with he | hf
    · subst f; exact frame_length ns hhead
    · exact ih f hf

theorem encode_length (ns : List CompileNode) {g n A M final c} (h : Typed g n A M final c) :
    (encode ns c).length ≤ (c.stack.length + 1) * (7 + 3 * A) := by
  obtain ⟨kind, ht, hstack⟩ := h
  have hh := task_length ns ht
  have hs := sum_le_length_mul (fun f => (writeFrame ns f).length) (6 + 3 * A) c.stack
    (frames_length ns hstack)
  simp only [encode, writeList, List.length_append, List.length_cons, List.length_flatMap]
  rw [show 7 + 3 * A = (6 + 3 * A) + 1 by omega, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- This counts the actual natural-number stream, including all tags and
length headers, rather than an abstract count of selected fields. -/
theorem reachable_length (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (encode (compilerNodes g e) c).length ≤
      (SequentialStackRank.initialCap g x e + 1) * (7 + 3 * arityBudget g) := by
  have hh := encode_length (compilerNodes g e) (reachable_typed g x e c h)
  have hs := SequentialStackRank.reachable_stack_bound g x e c h
  exact Nat.le_trans hh (Nat.mul_le_mul_right _ (by omega))

def Bounded (B : Nat) (code : List Nat) : Prop := ∀ v ∈ code, v ≤ B

theorem Bounded.append {B : Nat} {left right : List Nat} (hl : Bounded B left) (hr : Bounded B right) :
    Bounded B (left ++ right) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hl v hv
  · exact hr v hv

theorem Bounded.cons {B v : Nat} {rest : List Nat} (hv : v ≤ B) (hr : Bounded B rest) :
    Bounded B (v :: rest) := by
  intro w hw
  rcases List.mem_cons.mp hw with he | hw
  · subst w; exact hv
  · exact hr w hw

theorem bounded_list {α : Type} {B : Nat} (writer : α → List Nat) (as : List α)
    (hlen : as.length ≤ B) (h : ∀ a ∈ as, Bounded B (writer a)) : Bounded B (writeList writer as) := by
  apply Bounded.cons hlen
  intro v hv
  obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hv
  exact h a ha v hv

theorem env_bounded {n A B : Nat} {E : CaptureEnv} (hE : EnvOK n A E)
    (hn : n ≤ B) (ha : A ≤ B) : Bounded B (writeEnv E) := by
  apply bounded_list writePair E (by have hh := hE.2; omega)
  intro span hspan
  have hh := hE.1 span hspan
  simp [Bounded, writePair]
  omega

theorem expr_bounded (ns : List CompileNode) (e : MExp) (B : Nat) (hp : (SequentialStackPool.exprPool ns).length ≤ B) :
    Bounded B (writeExpr ns e) := by
  simp only [Bounded, writeExpr, List.mem_singleton, forall_eq]
  exact Nat.le_trans List.idxOf_le_length hp

theorem exprs_bounded (ns : List CompileNode) (es : List MExp) (B : Nat)
    (hp : (SequentialStackPool.exprPool ns).length ≤ B) (hlen : es.length ≤ B) :
    Bounded B (writeExprs ns es) :=
  bounded_list _ _ hlen (fun e _ => expr_bounded ns e B hp)

theorem res_bounded {n B : Nat} {r : Res} (hr : OkR n r) (hn : n ≤ B) (hb : 8 ≤ B) :
    Bounded B (writeRes r) := by
  cases r with
  | none => simp [Bounded, writeRes]
  | some r =>
    cases r with
    | none => simp [Bounded, writeRes]; omega
    | some q => have hh := hr q rfl; simp [Bounded, writeRes]; omega

theorem value_bounded {n A B kind v} (h : ValueTyped n A kind v)
    (hn : n ≤ B) (ha : A ≤ B) (hb : 8 ≤ B) : Bounded B (writeValue v) := by
  cases h with
  | expr r hr => exact Bounded.cons (Nat.zero_le _) (res_bounded hr hn hb)
  | args r k hk hr =>
    cases r with
    | none => simp [Bounded, writeValue, writeArgsRes]; omega
    | some r =>
      cases r with
      | none => simp [Bounded, writeValue, writeArgsRes]; omega
      | some Wq =>
        obtain ⟨W, q⟩ := Wq
        obtain ⟨hW, hq, hlen⟩ := hr W q rfl
        apply Bounded.cons (by omega)
        apply Bounded.append (left := [2, q])
        · simp [Bounded]; omega
        · exact env_bounded hW hn ha

theorem task_bounded (ns : List CompileNode) {g n A M B D task kind}
    (h : TaskTyped n A M task kind) (hc : SequentialStackCode.TaskCode g D task)
    (hn : n ≤ B) (ha : A ≤ B) (hm : M ≤ B) (hp : (SequentialStackPool.exprPool ns).length ≤ B)
    (hR : g.rules.length ≤ B) (hb : 8 ≤ B) : Bounded B (writeTask ns task) := by
  cases h with
  | expr m E e p hm' hE hp' =>
    apply Bounded.append (left := [0, m, p])
    · simp [Bounded]; omega
    · exact (expr_bounded ns e B hp).append (env_bounded hE hn ha)
  | args m E es p hm' hE hp' hlen =>
    apply Bounded.append (left := [1, m, p])
    · simp [Bounded]; omega
    · exact (env_bounded hE hn ha).append (exprs_bounded ns es B hp (by omega))
  | query m i E p hm' hE hp' =>
    apply Bounded.append (left := [2, m, i, p])
    · change i < g.rules.length at hc
      simp [Bounded]; omega
    · exact env_bounded hE hn ha
  | value hv => exact Bounded.cons (by omega) (value_bounded hv hn ha hb)

theorem frame_bounded (ns : List CompileNode) {g n A M B f kind out}
    (h : FrameTyped g n A M f kind out)
    (hn : n ≤ B) (ha : A ≤ B) (hm : M ≤ B) (hp : (SequentialStackPool.exprPool ns).length ≤ B)
    (hR : g.rules.length ≤ B) (hb : 8 ≤ B) : Bounded B (writeFrame ns f) := by
  cases h with
  | seq m E b hm' hE =>
    apply Bounded.append (left := [0, m])
    · simp [Bounded]; omega
    · exact (expr_bounded ns b B hp).append (env_bounded hE hn ha)
  | alt m E b p hm' hE hp' =>
    apply Bounded.append (left := [1, m, p])
    · simp [Bounded]; omega
    · exact (expr_bounded ns b B hp).append (env_bounded hE hn ha)
  | notP p hp' => simp [Bounded, writeFrame]; omega
  | star m E a p hm' hE hp' =>
    apply Bounded.append (left := [3, m, p])
    · simp [Bounded]; omega
    · exact (expr_bounded ns a B hp).append (env_bounded hE hn ha)
  | argHead m E es p hm' hE hp' hlen =>
    apply Bounded.append (left := [4, m, p])
    · simp [Bounded]; omega
    · exact (env_bounded hE hn ha).append (exprs_bounded ns es B hp (by omega))
  | argCons span k hs hk =>
    simp [Bounded, writeFrame]
    omega
  | call m i rule hm' hr harity =>
    have hi := ruleAtM_lt hr
    simp [Bounded, writeFrame]
    omega

theorem frames_bounded (ns : List CompileNode) {g n A M B kind final K}
    (h : StackTyped g n A M kind K final)
    (hn : n ≤ B) (ha : A ≤ B) (hm : M ≤ B) (hp : (SequentialStackPool.exprPool ns).length ≤ B)
    (hR : g.rules.length ≤ B) (hb : 8 ≤ B) : ∀ f ∈ K, Bounded B (writeFrame ns f) := by
  induction h with
  | nil => intro f hf; cases hf
  | cons hhead htail ih =>
    intro f hf
    rcases List.mem_cons.mp hf with he | hf
    · subst f; exact frame_bounded ns hhead hn ha hm hp hR hb
    · exact ih f hf

noncomputable def numberBound (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  SequentialStackRank.initialCap g x e + SequentialClock.positionClock g x.length + x.length +
    arityBudget g + (SequentialStackPool.exprPool (compilerNodes g e)).length + g.rules.length + 8

/-- Every tag, length header, code identifier and numeric field in the
actual stream is bounded, including the stack's length header. -/
theorem reachable_numbers (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    Bounded (numberBound g x e) (encode (compilerNodes g e) c) := by
  obtain ⟨kind, ht, hstack⟩ := reachable_typed g x e c h
  have hc := SequentialStackCode.reachable_code g x e c h
  have hs := SequentialStackRank.reachable_stack_bound g x e c h
  apply Bounded.append
  · exact task_bounded _ ht hc.1 (by unfold numberBound; omega) (by unfold numberBound; omega)
      (by unfold numberBound; omega) (by unfold numberBound; omega)
      (by unfold numberBound; omega) (by unfold numberBound; omega)
  · apply bounded_list _ _ (by unfold numberBound; omega)
    exact frames_bounded _ hstack (by unfold numberBound; omega) (by unfold numberBound; omega)
      (by unfold numberBound; omega) (by unfold numberBound; omega)
      (by unfold numberBound; omega) (by unfold numberBound; omega)

end Shallot.MacroPeg.CBV.SequentialStackCodecBound
