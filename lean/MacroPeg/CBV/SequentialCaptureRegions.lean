import MacroPeg.CBV.SequentialStackPayload

/-! Capture-region accounting for the actual sequential transition machine.
Successful argument values partition one consumed interval, and active
environments lie before the current cursor. This does not yet bound total
retained character storage across duplicated continuation environments. -/
namespace Shallot.MacroPeg.CBV.SequentialCaptureRegions
open SequentialStack SequentialStackPayload

def Past (E : CaptureEnv) (p : Nat) : Prop := ∀ span ∈ E, p ≤ span.2

theorem Past.mono {E : CaptureEnv} {p q : Nat} (h : Past E p) (hq : q ≤ p) : Past E q :=
  fun span hm => Nat.le_trans hq (h span hm)

inductive Window : Nat → Nat → CaptureEnv → Prop where
  | nil (p : Nat) : Window p p []
  | cons {p j q : Nat} {W : CaptureEnv} (hj : j ≤ p) (tail : Window j q W) :
      Window p q ((p,j)::W)

theorem Window.descending {p q : Nat} {W : CaptureEnv} (h : Window p q W) : q ≤ p := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hj _ ih => omega

theorem Window.past {p q : Nat} {W : CaptureEnv} (h : Window p q W) : Past W q := by
  induction h with
  | nil => intro span hm; cases hm
  | cons hj ht ih =>
    intro span hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ht.descending
    · exact ih span hm

theorem Window.upper {p q : Nat} {W : CaptureEnv} (h : Window p q W) : ∀ span ∈ W, span.1 ≤ p := by
  induction h with
  | nil => intro span hm; cases hm
  | cons hj ht ih =>
    intro span hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih span hm) hj

def weight (E : CaptureEnv) : Nat := (E.map (fun span => span.1-span.2)).sum

theorem Window.weight {p q : Nat} {W : CaptureEnv} (h : Window p q W) : weight W = p-q := by
  induction h with
  | nil => simp [SequentialCaptureRegions.weight]
  | cons hj ht ih =>
    have hq := ht.descending
    simp only [SequentialCaptureRegions.weight,List.map_cons,List.sum_cons] at ih ⊢
    omega

theorem Window.valid {p q n : Nat} {W : CaptureEnv} (h : Window p q W) (hp : p ≤ n) :
    SequentialSpanRecompute.ValidEnv n W := by
  induction h with
  | nil => intro span hm; cases hm
  | cons hj ht ih =>
    intro span hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hj,hp⟩
    · exact ih (Nat.le_trans hj hp) span hm

/-- The numeric conservation law is also exact for the captured character
words used by the grammar semantics, not just for span metadata. -/
theorem Window.decoded_weight {p q : Nat} {W : CaptureEnv} (h : Window p q W)
    (x : List Char) (hp : p ≤ x.length) :
    ((SequentialSpanRecompute.decodeEnv x W).map List.length).sum = p-q := by
  induction h with
  | nil => simp [SequentialSpanRecompute.decodeEnv]
  | @cons p j q W hj ht ih =>
    have hword : (pre x p j).length = p-j := by
      simp only [pre,List.length_take,length_sfx x hp]
      exact Nat.min_eq_left (Nat.sub_le _ _)
    have htail := ih (Nat.le_trans hj hp)
    change (pre x p j).length + ((SequentialSpanRecompute.decodeEnv x W).map List.length).sum = _
    rw [hword,htail]
    have hq := ht.descending
    omega

/-- New argument captures and an older environment occupy disjoint regions,
even if the captured word values happen to be equal. -/
theorem old_new_order {p q : Nat} {E W : CaptureEnv} (hE : Past E p) (hW : Window p q W) :
    ∀ old ∈ E, ∀ fresh ∈ W, fresh.1 ≤ old.2 := by
  intro old ho fresh hf
  exact Nat.le_trans (hW.upper fresh hf) (hE old ho)

inductive Kind where
  | expr (bound : Nat)
  | args (start : Nat)

def Kind.bound : Kind → Nat
  | .expr p | .args p => p

inductive ScopedValue : Kind → SequentialStack.Value → Prop where
  | expr {p : Nat} {r : Res} (h : OkR p r) : ScopedValue (.expr p) (.expr r)
  | args {p : Nat} {r : ArgsResult}
      (h : ∀ W q, r = some (some (W,q)) → Window p q W) : ScopedValue (.args p) (.args r)

inductive ScopedTask : Task → Kind → Prop where
  | expr {m E e p cap} (hp : p ≤ cap) (hE : Past E p) : ScopedTask (.expr m E e p) (.expr cap)
  | args {m E es p} (hE : Past E p) : ScopedTask (.args m E es p) (.args p)
  | query {m i E p cap} (hp : p ≤ cap) (hE : Past E p) : ScopedTask (.query m i E p) (.expr cap)
  | value {v k} (h : ScopedValue k v) : ScopedTask (.value v) k

inductive ScopedFrame : Frame → Kind → Kind → Prop where
  | seq {m E b p cap} (hp : p ≤ cap) (hE : Past E p) :
      ScopedFrame (.seq m E b) (.expr p) (.expr cap)
  | alt {m E b p cap} (hp : p ≤ cap) (hE : Past E p) :
      ScopedFrame (.alt m E b p) (.expr p) (.expr cap)
  | notP {p cap} (hp : p ≤ cap) : ScopedFrame (.notP p) (.expr p) (.expr cap)
  | star {m E a p cap} (hp : p ≤ cap) (hE : Past E p) :
      ScopedFrame (.star m E a p) (.expr p) (.expr cap)
  | argHead {m E es p} (hE : Past E p) : ScopedFrame (.argHead m E es p) (.expr p) (.args p)
  | argCons {p q} (hq : q ≤ p) : ScopedFrame (.argCons (p,q)) (.args q) (.args p)
  | call {m i p cap} (hp : p ≤ cap) : ScopedFrame (.call m i) (.args p) (.expr cap)

inductive ScopedStack : Kind → List Frame → Kind → Prop where
  | nil (k) : ScopedStack k [] k
  | cons {k k' final f K} (head : ScopedFrame f k k') (tail : ScopedStack k' K final) :
      ScopedStack k (f::K) final

def Scoped (final : Kind) (c : Config) : Prop :=
  ∃ k, ScopedTask c.task k ∧ ScopedStack k c.stack final

private theorem result_mono {p q : Nat} {r : Res} (h : OkR p r) (hp : p ≤ q) : OkR q r :=
  fun j hj => Nat.le_trans (h j hj) hp

private theorem matchCount_descending : ∀ k source target q,
    SequentialSpanRecompute.matchCount k source target = some q → q ≤ target.length
  | 0, _, target, q, h => by cases h; exact Nat.le_refl _
  | _+1, [], _, _, h => by cases h
  | _+1, _::_, [], _, h => by cases h
  | k+1, c::source, d::target, q, h => by
    simp only [SequentialSpanRecompute.matchCount] at h
    split at h
    · have hh := matchCount_descending k source target q h; simp; omega
    · cases h

theorem atom_descending (x : List Char) (E : CaptureEnv) (e : MExp) (p : Nat) : OkR p (atom x E e p) := by
  have hlen : (sfx x p).length ≤ p := by simp only [sfx,List.length_drop]; omega
  cases e with
  | eps | dbg _ | lam _ _ => exact okR_ok (Nat.le_refl _)
  | invoke _ _ _ => exact okR_none _
  | call _ _ | callParam _ _ | seq _ _ | alt _ _ | notP _ | star _ => exact okR_fail _
  | lit w =>
    simp only [atom]
    split
    · rename_i rest he
      exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ he) hlen)
    · exact okR_fail _
  | any =>
    simp only [atom]
    split
    · rename_i c rest he
      have hh := hlen; rw [he] at hh; exact okR_ok (by simp at hh; omega)
    · exact okR_fail _
  | chr c | range c _ =>
    simp only [atom]
    split
    · rename_i d rest he
      have hh := hlen; rw [he] at hh
      split
      · exact okR_ok (by simp at hh; omega)
      · exact okR_fail _
    · exact okR_fail _
  | param k =>
    simp only [atom]
    split
    · rename_i span he
      intro q hq
      simp only [SequentialSpanRecompute.matchSpan,Option.some.injEq] at hq
      exact Nat.le_trans (matchCount_descending _ _ _ _ hq) hlen
    · exact okR_fail _

theorem return_scoped (g : MGrammar) (x : List Char)
    {v : SequentialStack.Value} {kind out final : Kind} {f : Frame} {K : List Frame} {next : Config}
    (hv : ScopedValue kind v) (hf : ScopedFrame f kind out) (ht : ScopedStack out K final)
    (hs : step g x ⟨.value v,f::K⟩ = some next) : Scoped final next := by
  cases hf with
  | @seq m E b p cap hp hE =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none =>
        cases hs
        exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none =>
          cases hs
          exact ⟨_,.value (.expr (okR_fail _)),ht⟩
        | some q =>
          cases hs
          exact ⟨_,.expr (Nat.le_trans (hr q rfl) hp) (hE.mono (hr q rfl)),ht⟩
  | @alt m E b p cap hp hE =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.expr hp hE,ht⟩
        | some q => cases hs; exact ⟨_,.value (.expr (okR_ok (Nat.le_trans (hr q rfl) hp))),ht⟩
  | @notP p cap hp =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.expr (okR_ok hp)),ht⟩
        | some q => cases hs; exact ⟨_,.value (.expr (okR_fail _)),ht⟩
  | @star m E a p cap hp hE =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.expr (okR_ok hp)),ht⟩
        | some q =>
          by_cases hq : q<p
          · simp only [step,if_pos hq] at hs
            cases hs
            exact ⟨_,.expr (by omega) (hE.mono (by omega)),ht⟩
          · simp only [step,if_neg hq] at hs
            cases hs
            exact ⟨_,.value (.expr (okR_none _)),ht⟩
  | @argHead m E es p hE =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.args (by intro W q he; cases he)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.args (by intro W q he; cases he)),ht⟩
        | some q =>
          have hq := hr q rfl
          simp only [step,Nat.min_eq_left hq] at hs
          cases hs
          exact ⟨_,.args (hE.mono hq),.cons (.argCons hq) ht⟩
  | @argCons p j hj =>
    cases hv with
    | @args _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.args (by intro W q he; cases he)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.args (by intro W q he; cases he)),ht⟩
        | some Wq =>
          obtain ⟨W,q⟩ := Wq
          cases hs
          refine ⟨_,.value (.args ?_),ht⟩
          intro V r he
          cases he
          exact .cons hj (hr W q rfl)
  | @call m i p cap hp =>
    cases hv with
    | @args _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.expr (okR_fail _)),ht⟩
        | some Wq =>
          obtain ⟨W,q⟩ := Wq
          cases hs
          have hW := hr W q rfl
          exact ⟨_,.query (Nat.le_trans hW.descending hp) hW.past,ht⟩

theorem step_scoped (g : MGrammar) (x : List Char) {final : Kind} {c next : Config}
    (h : Scoped final c) (hs : step g x c = some next) : Scoped final next := by
  obtain ⟨task,K⟩ := c
  obtain ⟨kind,hTask,hStack⟩ := h
  cases hTask with
  | @expr m E e p cap hp hE =>
    cases e with
    | seq a b =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _) hE,.cons (.seq hp hE) hStack⟩
    | alt a b =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _) hE,.cons (.alt hp hE) hStack⟩
    | notP a =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _) hE,.cons (.notP hp) hStack⟩
    | star a =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _) hE,.cons (.star hp hE) hStack⟩
    | call i args =>
      cases hr : ruleAtM g.rules i with
      | none =>
        simp only [step,hr] at hs
        cases hs
        exact ⟨_,.value (.expr (okR_fail _)),hStack⟩
      | some rule =>
        by_cases ha : rule.arity=args.length
        · simp only [step,hr,if_pos ha] at hs
          cases hs
          exact ⟨_,.args hE,.cons (.call hp) hStack⟩
        · simp only [step,hr,if_neg ha] at hs
          cases hs
          exact ⟨_,.value (.expr (okR_fail _)),hStack⟩
    | eps | any | chr _ | range _ _ | lit _ | param _ | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ =>
      cases hs
      exact ⟨_,.value (.expr (result_mono (atom_descending x E _ p) hp)),hStack⟩
  | @args m E es p hE =>
    cases es with
    | nil =>
      cases hs
      refine ⟨_,.value (.args ?_),hStack⟩
      intro W q he
      cases he
      exact .nil p
    | cons a args =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _) hE,.cons (.argHead hE) hStack⟩
  | @query m i E p cap hp hE =>
    cases m with
    | zero => cases hs; exact ⟨_,.value (.expr (okR_none _)),hStack⟩
    | succ m =>
      by_cases hn : p≤x.length
      · cases hr : ruleAtM g.rules i with
        | none =>
          simp only [step,if_pos hn,hr] at hs
          cases hs
          exact ⟨_,.value (.expr (okR_none _)),hStack⟩
        | some rule =>
          simp only [step,if_pos hn,hr] at hs
          cases hs
          exact ⟨_,.expr hp hE,hStack⟩
      · simp only [step,if_neg hn] at hs
        cases hs
        exact ⟨_,.value (.expr (okR_none _)),hStack⟩
  | @value v k hv =>
    cases hStack with
    | nil => cases v <;> simp [step] at hs
    | cons hf ht => exact return_scoped g x hv hf ht hs

theorem runs_scoped (g : MGrammar) (x : List Char) {final : Kind} {a b : Config}
    (h : Runs g x a b) (ha : Scoped final a) : Scoped final b := by
  induction h with
  | refl => exact ha
  | cons hs ht ih => exact ih (step_scoped g x ha hs)

theorem initial_scoped (g : MGrammar) (x : List Char) (e : MExp) :
    Scoped (.expr x.length) (initial g x e) :=
  ⟨_,.expr (Nat.le_refl _) (by intro span hm; cases hm),.nil _⟩

/-- The scope certificate follows the existing unmodified transition function;
it introduces neither hidden runtime fields nor a new abstract execution. -/
theorem reachable_scoped (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : Scoped (.expr x.length) c :=
  runs_scoped g x h (initial_scoped g x e)

theorem ScopedFrame.bound_mono {f : Frame} {kind out : Kind} (h : ScopedFrame f kind out) :
    kind.bound ≤ out.bound := by
  cases h <;> simp only [Kind.bound] <;> omega

theorem ScopedFrame.past {f : Frame} {kind out : Kind} (h : ScopedFrame f kind out) :
    Past (frameCaptures f) kind.bound := by
  cases h with
  | seq _ hE | alt _ hE | star _ hE | argHead hE => exact hE
  | notP _ | call _ => intro span hm; cases hm
  | argCons hq => intro span hm; rcases List.mem_cons.mp hm with rfl | hm; exact Nat.le_refl _; cases hm

theorem ScopedStack.bound_mono {kind final : Kind} {K : List Frame} (h : ScopedStack kind K final) :
    kind.bound ≤ final.bound := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hf _ ih => exact Nat.le_trans hf.bound_mono ih

theorem ScopedStack.past {kind final : Kind} {K : List Frame} (h : ScopedStack kind K final) :
    ∀ f ∈ K, Past (frameCaptures f) kind.bound := by
  induction h with
  | nil => intro f hm; cases hm
  | cons hf ht ih =>
    intro f hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hf.past
    · exact (ih f hm).mono hf.bound_mono

theorem ScopedValue.position_bound {kind : Kind} {v : SequentialStack.Value} (h : ScopedValue kind v) :
    taskPosition (.value v) ≤ kind.bound := by
  cases h with
  | @expr p r hr =>
    cases r with
    | none => exact Nat.zero_le _
    | some result => cases result with
      | none => exact Nat.zero_le _
      | some q => exact hr q rfl
  | @args p r hr =>
    cases r with
    | none => exact Nat.zero_le _
    | some result => cases result with
      | none => exact Nat.zero_le _
      | some Wq => obtain ⟨W,q⟩ := Wq; exact (hr W q rfl).descending

theorem ScopedValue.past {kind : Kind} {v : SequentialStack.Value} (h : ScopedValue kind v) :
    Past (taskCaptures (.value v)) (taskPosition (.value v)) := by
  cases h with
  | expr _ => intro span hm; cases hm
  | @args p r hr =>
    cases r with
    | none => intro span hm; cases hm
    | some result => cases result with
      | none => intro span hm; cases hm
      | some Wq => obtain ⟨W,q⟩ := Wq; exact (hr W q rfl).past

theorem ScopedTask.position_bound {kind : Kind} {task : Task} (h : ScopedTask task kind) :
    taskPosition task ≤ kind.bound := by
  cases h with
  | expr hp _ | query hp _ => exact hp
  | args _ => exact Nat.le_refl _
  | value hv => exact hv.position_bound

theorem ScopedTask.past {kind : Kind} {task : Task} (h : ScopedTask task kind) :
    Past (taskCaptures task) (taskPosition task) := by
  cases h with
  | expr _ hE | args hE | query _ hE => exact hE
  | value hv => exact hv.past

/-- Every capture retained in any live continuation is physically before the
current cursor. Failure/undefined tasks use the existing zero-position sentinel. -/
theorem reachable_past (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    Past (taskCaptures c.task) (taskPosition c.task) ∧
      ∀ f ∈ c.stack, Past (frameCaptures f) (taskPosition c.task) := by
  obtain ⟨kind,ht,hs⟩ := reachable_scoped g x e c h
  exact ⟨ht.past,fun f hf => (hs.past f hf).mono ht.position_bound⟩

/-- A successful returned argument tuple is one contiguous consumed window.
Its fresh intervals lie after every older capture retained anywhere in the
continuation stack, not merely after the current caller's local environment. -/
theorem reachable_arguments (g : MGrammar) (x : List Char) (e : MExp) (W : CaptureEnv)
    (q : Nat) (K : List Frame)
    (h : Runs g x (initial g x e) ⟨.value (.args (some (some (W,q)))),K⟩) :
    ∃ p, p ≤ x.length ∧ Window p q W ∧ weight W=p-q ∧
      ∀ f ∈ K, ∀ old ∈ frameCaptures f, ∀ fresh ∈ W, fresh.1 ≤ old.2 := by
  obtain ⟨kind,ht,hs⟩ := reachable_scoped g x e _ h
  cases ht with
  | value hv => cases hv with
    | @args p _ hr =>
      have hW := hr W q rfl
      exact ⟨p,hs.bound_mono,hW,hW.weight,fun f hf => old_new_order (hs.past f hf) hW⟩

theorem reachable_decoded_arguments (g : MGrammar) (x : List Char) (e : MExp) (W : CaptureEnv)
    (q : Nat) (K : List Frame)
    (h : Runs g x (initial g x e) ⟨.value (.args (some (some (W,q)))),K⟩) :
    ∃ p, q ≤ p ∧ p ≤ x.length ∧
      ((SequentialSpanRecompute.decodeEnv x W).map List.length).sum = p-q ∧
      ∀ f ∈ K, ∀ old ∈ frameCaptures f, ∀ fresh ∈ W, fresh.1 ≤ old.2 := by
  obtain ⟨p,hp,hW,_,hsep⟩ := reachable_arguments g x e W q K h
  exact ⟨p,hW.descending,hp,hW.decoded_weight x hp,hsep⟩

end Shallot.MacroPeg.CBV.SequentialCaptureRegions
