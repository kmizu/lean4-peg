import MacroPeg.CBV.FinitePrefixControl
import MacroPeg.CBV.AlphabetCaptureProfiles

namespace Shallot.MacroPeg.CBV.GuardedFinitePrefix
open FinitePrefixControl (Prefix raw outputs literal_append success_word)
open GuardedReplayControl (Expr render)
open ClockFreezing (Table)

abbrev Words (n : Nat) := List Char → GuardedReplayControl.Expr n

def look {n : Nat} (e : GuardedReplayControl.Expr n) : GuardedReplayControl.Expr n := .notP (.notP e)
def guard {n : Nat} (a b : GuardedReplayControl.Expr n) : GuardedReplayControl.Expr n := .seq (look a) b
def choose {n : Nat} (test yes no : GuardedReplayControl.Expr n) : GuardedReplayControl.Expr n :=
  .alt (guard test yes) (guard (.notP test) no)

def compile {n : Nat} (read finish : Words n) : Prefix → List Char → (List Char → GuardedReplayControl.Expr n) → GuardedReplayControl.Expr n
  | .lit w,u,K => guard (read (u++w)) (K (u++w))
  | .query positive,u,K => guard (if positive then finish u else .notP (finish u)) (K u)
  | .seq a b,u,K => compile read finish a u (fun v => compile read finish b v K)
  | .alt a b,u,K => choose (compile read finish a u read)
      (compile read finish a u K) (compile read finish b u K)
  | .notP a,u,K => guard (.notP (compile read finish a u read)) (K u)

def readCheck {n : Nat} (read : Words n) (u : List Char) : Bool :=
  match read u with
  | .literalQuery _ _ q L => decide ((L q).getD []=u)
  | _ => false

def finishCheck {n : Nat} (finish : Words n) (u : List Char) : Bool :=
  match finish u with
  | .replayQuery => decide (u=[])
  | .shift q R => decide ((R q).getD []=u)
  | _ => false

def checkAt {n : Nat} (read finish : Words n) : Prefix → List Char → Bool
  | .lit w,u => readCheck read u && readCheck read (u++w)
  | .query _,u => readCheck read u && finishCheck finish u
  | .seq a b,u => checkAt read finish a u && (outputs a).all (fun v => checkAt read finish b (u++v))
  | .alt a b,u => checkAt read finish a u && checkAt read finish b u
  | .notP a,u => readCheck read u && checkAt read finish a u

theorem read_sound {n : Nat} (read : Words n) (u : List Char) (h : readCheck read u=true) :
    render (read u)=.andP (.lit u) := by
  unfold readCheck at h
  cases he : read u <;> simp only [he] at h <;> try contradiction
  rename_i alphabet a q L
  have hu := of_decide_eq_true h
  simp [render,hu]

theorem finish_sound {n : Nat} (finish : Words n) (u : List Char) (h : finishCheck finish u=true)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (render (finish u)) p=
      evV g x s T E (.seq (.lit u) (.andP (.param 0))) p := by
  unfold finishCheck at h
  cases he : finish u <;> simp only [he] at h <;> try contradiction
  case replayQuery =>
    have hu := of_decide_eq_true h
    subst u
    simp [render,evV,Shallot.stripPrefix?,length_sfx x hp]
  case shift q R =>
    have hu := of_decide_eq_true h
    simp [render,GuardedReplayIteration.step,hu]

theorem guard_eval {n : Nat} (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p : Nat) (a b : GuardedReplayControl.Expr n) :
    evV g x s T E (render (guard a b)) p=
      match evV g x s T E (render a) p with
      | some (some _) => evV g x s T E (render b) p
      | other => other := by
  change evV g x s T E (.seq (.andP (render a)) (render b)) p=_
  change (match evV g x s T E (.andP (render a)) p with
    | some (some q) => evV g x s T E (render b) q | other => other)=_
  rw [CallLookahead.evV_peek]
  cases evV g x s T E (render a) p with
  | none => rfl
  | some v => cases v <;> rfl

theorem not_eval {n : Nat} (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p : Nat) (a : GuardedReplayControl.Expr n) :
    evV g x s T E (render (.notP a)) p=
      GuardedReplayControl.notValue p (evV g x s T E (render a) p) := rfl

theorem choose_eval {n : Nat} (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p : Nat) (test yes no : GuardedReplayControl.Expr n) :
    evV g x s T E (render (choose test yes no)) p=
      match evV g x s T E (render test) p with
      | none => none | some none => evV g x s T E (render no) p
      | some (some _) => evV g x s T E (render yes) p := by
  change (match evV g x s T E (render (guard test yes)) p with
    | some none => evV g x s T E (render (guard (.notP test) no)) p | other => other)=_
  rw [guard_eval,guard_eval]
  rw [not_eval]
  change ReplayFallbackFusion.orElse _ _ = _
  cases ht : evV g x s T E (render test) p with
  | none => simp [ReplayFallbackFusion.orElse]
  | some v => cases v with
    | none => simp [GuardedReplayControl.notValue,ReplayFallbackFusion.orElse]
    | some q =>
      cases hy : evV g x s T E (render yes) p with
      | none => simp [ReplayFallbackFusion.orElse]
      | some v => cases v <;> simp [GuardedReplayControl.notValue,ReplayFallbackFusion.orElse]

theorem output_checked {n : Nat} (read finish : Words n) :
    ∀ e u, checkAt read finish e u=true → ∀ v∈outputs e, readCheck read (u++v)=true
  | .lit w,u,h,v,hv => by
    have he : v=w := by simpa [outputs] using hv
    subst v; exact (Bool.and_eq_true_iff.mp h).2
  | .query _,u,h,v,hv | .notP _,u,h,v,hv => by
    have he : v=[] := by simpa [outputs] using hv
    subst v; simpa using (Bool.and_eq_true_iff.mp h).1
  | .alt a b,u,h,v,hv => by
    rcases List.mem_append.mp hv with hv | hv
    · exact output_checked read finish a u (Bool.and_eq_true_iff.mp h).1 v hv
    · exact output_checked read finish b u (Bool.and_eq_true_iff.mp h).2 v hv
  | .seq a b,u,h,v,hv => by
    obtain ⟨v1,h1,h2⟩ := List.mem_flatMap.mp hv
    obtain ⟨v2,hv2,rfl⟩ := List.mem_map.mp h2
    have hb := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) v1 h1
    simpa [List.append_assoc] using output_checked read finish b (u++v1) hb v2 hv2

private theorem query_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (positive : Bool) (e : MExp) (p : Nat) :
    evV g x s T E (PrefixCaptureQuery.query positive e) p=
      match evV g x s T E e p with
      | none => none | some none => if positive then some none else some (some p)
      | some (some _) => if positive then some (some p) else some none := by
  cases positive
  · cases hv : evV g x s T E e p with
    | none => simp [PrefixCaptureQuery.query,evV,hv]
    | some v => cases v <;> simp [PrefixCaptureQuery.query,evV,hv]
  · change evV g x s T E (.andP e) p=_
    rw [CallLookahead.evV_peek]
    cases evV g x s T E e p with
    | none => rfl
    | some v => cases v <;> rfl

/-- The continuation is committed after prefix success. Its failure or
undefinedness is never treated as failure of a prefix alternative. -/
theorem compile_eval {n : Nat} (read finish : Words n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    ∀ e u, checkAt read finish e u=true → ∀ q, q≤x.length →
    evV g x s T E (.lit u) p=some (some q) → ∀ K (kont : Nat → Res),
    (∀ v∈outputs e, ∀ r, evV g x s T E (.lit (u++v)) p=some (some r) →
      evV g x s T E (render (K (u++v))) p=kont r) →
    evV g x s T E (render (compile read finish e u K)) p=
      match evV g x s T E (raw e) q with | some (some r) => kont r | other => other
  | .lit w,u,h,q,hq,hu,K,kont,hK => by
    have hr := read_sound read (u++w) (Bool.and_eq_true_iff.mp h).2
    rw [compile,guard_eval,hr,CallLookahead.evV_peek,literal_append g x s T E u w p q hu]
    simp only [raw]
    cases hv : evV g x s T E (.lit w) q with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some r => exact hK w (by simp [outputs]) r ((literal_append g x s T E u w p q hu).trans hv)
  | .query positive,u,h,q,hq,hu,K,kont,hK => by
    have hc := finish_sound finish u (Bool.and_eq_true_iff.mp h).2 g x s T E p hp
    rw [evV_seq_ok hu] at hc
    have hk := hK [] (by simp [outputs]) q (by simpa using hu)
    simp only [List.append_nil] at hk
    simp only [compile,guard_eval,raw,query_eval]
    rw [CallLookahead.evV_peek] at hc
    cases positive <;> simp only [Bool.false_eq_true,ite_false,ite_true,not_eval,hc]
    all_goals cases hv : evV g x s T E (.param 0) q with
    | none => simp only [CallLookahead.peek,GuardedReplayControl.notValue]
    | some v => cases v <;> simp only [CallLookahead.peek,GuardedReplayControl.notValue,hk]
  | .seq a b,u,h,q,hq,hu,K,kont,hK => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp only [compile]
    rw [compile_eval read finish g x s T E p hp a u ha q hq hu _
      (fun j => match evV g x s T E (raw b) j with | some (some r) => kont r | other => other)]
    · simp only [raw,evV]
      cases evV g x s T E (raw a) q with
      | none => rfl
      | some v => cases v <;> rfl
    · intro v hv j hj
      have hjbound := (SequenceArguments.success_prefix g x s T E (.lit (u++v)) True.intro p j
        hp hj).1
      apply compile_eval read finish g x s T E p hp b (u++v) ((List.all_eq_true.mp hb) v hv) j hjbound hj K kont
      intro w hw r hr
      have hm : v++w∈outputs (.seq a b) := List.mem_flatMap.mpr ⟨v,hv,List.mem_map.mpr ⟨w,hw,rfl⟩⟩
      simpa [List.append_assoc] using hK (v++w) hm r (by simpa [List.append_assoc] using hr)
  | .alt a b,u,h,q,hq,hu,K,kont,hK => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    have ht := compile_eval read finish g x s T E p hp a u ha q hq hu
      read (fun _ => some (some p)) (by
        intro v hv r hr
        rw [read_sound read _ (output_checked read finish a u ha v hv),CallLookahead.evV_peek,hr]
        rfl)
    rw [compile,choose_eval,ht]
    cases hv : evV g x s T E (raw a) q with
    | none => rw [raw,evV_alt_none hv]
    | some v => cases v with
      | none =>
        rw [raw,evV_alt_fail hv]
        exact compile_eval read finish g x s T E p hp b u hb q hq hu K kont
          (fun v hv => hK v (List.mem_append_right _ hv))
      | some r =>
        rw [raw,evV_alt_ok hv]
        have hh := compile_eval read finish g x s T E p hp a u ha q hq hu K kont
          (fun v hv => hK v (List.mem_append_left _ hv))
        simpa [hv] using hh
  | .notP a,u,h,q,hq,hu,K,kont,hK => by
    have ha := (Bool.and_eq_true_iff.mp h).2
    have ht := compile_eval read finish g x s T E p hp a u ha q hq hu
      read (fun _ => some (some p)) (by
        intro v hv r hr
        rw [read_sound read _ (output_checked read finish a u ha v hv),CallLookahead.evV_peek,hr]
        rfl)
    have hk := hK [] (by simp [outputs]) q (by simpa using hu)
    simp only [List.append_nil] at hk
    rw [compile,guard_eval]
    simp only [render,evV,ht]
    cases hv : evV g x s T E (raw a) q with
    | none => simp [raw,evV,hv]
    | some v => cases v <;> simp [raw,evV,hv,hk]


def atom {n : Nat} (read finish : Words n) (e : Prefix) := compile read finish e [] finish

def atomCheck {n : Nat} (read finish : Words n) (e : Prefix) : Bool :=
  checkAt read finish e [] && (outputs e).all (finishCheck finish)

theorem atom_eval {n : Nat} (read finish : Words n) (e : Prefix)
    (hc : atomCheck read finish e=true) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (render (atom read finish e)) p=
      evV g x s T E (.seq (raw e) (.andP (.param 0))) p := by
  obtain ⟨hc,hf⟩ := Bool.and_eq_true_iff.mp hc
  unfold atom
  rw [compile_eval read finish g x s T E p hp e [] hc p hp
    (by simp [evV,Shallot.stripPrefix?,length_sfx x hp]) finish
    (fun r => evV g x s T E (.andP (.param 0)) r)]
  · rfl
  · intro v hv r hr
    simpa only [List.nil_append] using
      (finish_sound finish v ((List.all_eq_true.mp hf) v hv) g x s T E p hp).trans
        (evV_seq_ok (by simpa only [List.nil_append] using hr))

/-- Finite dependent consuming atoms may occur anywhere inside PEG control,
including an unbounded greedy loop. Each atom ends with a retained query. -/
inductive Control (n : Nat) where
  | finite (e : Prefix)
  | ready (e : GuardedReplayControl.Expr n)
  | seq (a b : Control n)
  | alt (a b : Control n)
  | notP (a : Control n)
  | star (a : Control n)

def original {n : Nat} : Control n → MExp
  | .finite e => .seq (raw e) (.andP (.param 0))
  | .ready c => render c
  | .seq a b => .seq (original a) (original b)
  | .alt a b => .alt (original a) (original b)
  | .notP a => .notP (original a)
  | .star a => .star (original a)

def normalize {n : Nat} (read finish : Words n) : Control n → GuardedReplayControl.Expr n
  | .finite e => atom read finish e
  | .ready c => c
  | .seq a b => .seq (normalize read finish a) (normalize read finish b)
  | .alt a b => .alt (normalize read finish a) (normalize read finish b)
  | .notP a => .notP (normalize read finish a)
  | .star a => .star (normalize read finish a)

def controlCheck {n : Nat} (read finish : Words n) : Control n → Bool
  | .finite e => atomCheck read finish e
  | .ready _ => true
  | .seq a b | .alt a b => controlCheck read finish a && controlCheck read finish b
  | .notP a | .star a => controlCheck read finish a

theorem original_firstOrder {n : Nat} : ∀ e : Control n, (original e).FirstOrder
  | .finite e => ⟨FinitePrefixControl.raw_firstOrder e,True.intro⟩
  | .ready c => GuardedReplayControl.render_firstOrder c
  | .seq a b | .alt a b => ⟨original_firstOrder a,original_firstOrder b⟩
  | .notP a | .star a => original_firstOrder a

private theorem render_bound {n : Nat} (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (e : GuardedReplayControl.Expr n) (p q : Nat)
    (hp : p≤x.length) (h : evV g x s T E (render e) p=some (some q)) : q≤x.length := by
  have he := GuardedReplayControl.render_independent g ⟨[]⟩ x s .callByValuePar T (fun _ _ => []) E e p
  have hT : SoundTV ⟨[]⟩ x .callByValuePar (fun _ _ => []) := by
    intro i r W hi
    cases i <;> cases hi
  exact (DependentCaptureFilter.success_prefix (by decide) hT E (render e)
    (GuardedReplayControl.render_firstOrder e) p q hp (he.symm.trans h)).1

/-- Equality is table-independent, so normalization preserves actual
recursive evaluations without assuming successful capture annotations. -/
theorem normalize_eval {n : Nat} (read finish : Words n) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : Table) (E : List (List Char)) : ∀ e,
    controlCheck read finish e=true → ∀ p, p≤x.length →
    evV g x s T E (original e) p=evV g x s T E (render (normalize read finish e)) p
  | .finite e,h,p,hp => (atom_eval read finish e h g x s T E p hp).symm
  | .ready _,_,_,_ => rfl
  | .seq a b,h,p,hp => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp only [original,normalize,render,evV]
    rw [normalize_eval read finish g x s T E a ha p hp]
    cases hv : evV g x s T E (render (normalize read finish a)) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q =>
        exact normalize_eval read finish g x s T E b hb q
          (render_bound g x s T E _ p q hp hv)
  | .alt a b,h,p,hp => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp only [original,normalize,render,evV,
      normalize_eval read finish g x s T E a ha p hp,normalize_eval read finish g x s T E b hb p hp]
  | .notP a,h,p,hp => by
    simp only [original,normalize,render,evV,normalize_eval read finish g x s T E a h p hp]
  | .star a,h,p,hp => by
    simp only [original,normalize,render,evV_star]
    exact evStar_congr p (fun q hq => normalize_eval read finish g x s T E a h q (Nat.le_trans hq hp))


open RecursiveScannerProductCompiler (Arg Entries sourceExpr sourceHeader helpers offset)
open RecursiveCaptureProfiles (scopeCheck)
open StatefulScanner (Machine)

def entries {n : Nat} (read finish : Words n) (controls : Nat → Control n) : Entries n :=
  fun i => .aligned (normalize read finish (controls i))

def rules {n : Nat} (M : Machine n) (controls : Nat → Control n) (bodies : List Arg) : List MRule :=
  bodies.zipIdx.map (fun (b,i) => ⟨1,.seq (.seq (original (controls i)) (.param 0)) (sourceExpr M b)⟩)

def source {n : Nat} (M : Machine n) (controls : Nat → Control n) (bodies : List Arg) : MGrammar :=
  ⟨helpers M++rules M controls bodies⟩

def check {n : Nat} (M : Machine n) (read finish : Words n) (controls : Nat → Control n)
    (bodies : List Arg) (alphabet : List Char) : Bool :=
  bodies.zipIdx.all (fun (_,i) => controlCheck read finish (controls i)) &&
    AlphabetCaptureProfiles.check M (entries read finish controls) bodies alphabet

theorem source_firstOrder {n : Nat} (M : Machine n) (controls : Nat → Control n) (bodies : List Arg) :
    (source M controls bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact RecursiveScannerProductCompiler.helpers_firstOrder M r hr
  · obtain ⟨⟨b,i⟩,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨original_firstOrder _,True.intro⟩,RecursiveScannerProductCompiler.sourceExpr_firstOrder M b⟩

theorem source_rule {n : Nat} (M : Machine n) (controls : Nat → Control n) (bodies : List Arg)
    (i : Nat) (b : Arg) (hi : bodies[i]?=some b) :
    ruleAtM (source M controls bodies).rules (offset M+i)=
      some ⟨1,.seq (.seq (original (controls i)) (.param 0)) (sourceExpr M b)⟩ := by
  simp only [source,offset,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,rules,List.getElem?_map,List.getElem?_zipIdx,hi,Option.map_some,Nat.zero_add]

theorem related {n : Nat} (M : Machine n) (read finish : Words n) (controls : Nat → Control n)
    (bodies : List Arg) (alphabet : List Char) (h : check M read finish controls bodies alphabet=true) :
    SemanticBodyRewrite.Related (source M controls bodies)
      (RecursiveScannerProductCompiler.source M (entries read finish controls) bodies) .callByValuePar := by
  intro i
  unfold source RecursiveScannerProductCompiler.source rules RecursiveScannerProductCompiler.sourceRules
  simp only [ruleAtM_eq_getElem?]
  by_cases hi : i<(helpers M).length
  · simp only [List.getElem?_append_left hi]
    cases (helpers M)[i]? with
    | none => trivial
    | some r => exact ⟨rfl,fun _ _ _ _ _ => rfl⟩
  · have hi' : (helpers M).length≤i := by omega
    simp only [List.getElem?_append_right hi',List.getElem?_map]
    cases hb : bodies.zipIdx[i-(helpers M).length]? with
    | none => trivial
    | some bi =>
      obtain ⟨b,j⟩ := bi
      have hc := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1) (b,j) (List.mem_of_getElem? hb)
      refine ⟨rfl,?_⟩
      intro x T E p hp
      change evV _ x _ T E (.seq (.seq (original (controls j)) (.param 0)) (sourceExpr M b)) p=
        evV _ x _ T E (.seq (.seq (render (normalize read finish (controls j))) (.param 0)) (sourceExpr M b)) p
      simp only [evV,normalize_eval read finish _ x .callByValuePar T E _ hc p hp]

theorem observations_iff {n : Nat} (M : Machine n) (read finish : Words n) (controls : Nat → Control n)
    (bodies : List Arg) (alphabet : List Char) (h : check M read finish controls bodies alphabet=true)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source M controls bodies) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (RecursiveScannerProductCompiler.target M (entries read finish controls) bodies) .callByValueSeq
        (RecursiveScannerProductCompiler.plain M bodies [] e) x rest :=
  (SemanticBodyRewrite.observations (related M read finish controls bodies alphabet h)
    (source_firstOrder M controls bodies)
    (RecursiveScannerProductCompiler.source_firstOrder M _ bodies) (by decide) _
    (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e) x rest).trans
      (AlphabetCaptureProfiles.observations_iff M _ bodies alphabet (Bool.and_eq_true_iff.mp h).2 e he ha x rest)

theorem language_translation {n : Nat} (M : Machine n) (read finish : Words n) (controls : Nat → Control n)
    (bodies : List Arg) (alphabet : List Char) (h : check M read finish controls bodies alphabet=true)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source M controls bodies) .callByValuePar (sourceExpr M e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder M _ _,
    RecursiveScannerProductCompiler.plain_firstOrder M _ [] _,
    fun x => observations_iff M read finish controls bodies alphabet h e he ha x (some [])⟩

theorem defined_iff {n : Nat} (M : Machine n) (read finish : Words n) (controls : Nat → Control n)
    (bodies : List Arg) (alphabet : List Char) (h : check M read finish controls bodies alphabet=true)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M controls bodies) x .callByValuePar (tblV (source M controls bodies) x .callByValuePar k)
      [] (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (RecursiveScannerProductCompiler.target M (entries read finish controls) bodies) x .callByValueSeq
      (tblV (RecursiveScannerProductCompiler.target M (entries read finish controls) bodies) x .callByValueSeq k)
      [] (RecursiveScannerProductCompiler.plain M bodies [] e) x.length=some v) := by
  have hc := AlphabetCaptureProfiles.defined_iff M (entries read finish controls) bodies alphabet
    (Bool.and_eq_true_iff.mp h).2 e he ha x v
  have hp := fun k => SemanticBodyRewrite.physical (related M read finish controls bodies alphabet h)
    x k [] (sourceExpr M e) x.length
  constructor
  · rintro ⟨k,hk⟩
    exact hc.mp ⟨k,(hp k).symm.trans hk⟩
  · intro ht
    obtain ⟨k,hk⟩ := hc.mpr ht
    exact ⟨k,(hp k).trans hk⟩

theorem undefined_iff {n : Nat} (M : Machine n) (read finish : Words n) (controls : Nat → Control n)
    (bodies : List Arg) (alphabet : List Char) (h : check M read finish controls bodies alphabet=true)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true)
    (x : List Char) :
    (∀ k, evV (source M controls bodies) x .callByValuePar (tblV (source M controls bodies) x .callByValuePar k)
      [] (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (RecursiveScannerProductCompiler.target M (entries read finish controls) bodies) x .callByValueSeq
      (tblV (RecursiveScannerProductCompiler.target M (entries read finish controls) bodies) x .callByValueSeq k)
      [] (RecursiveScannerProductCompiler.plain M bodies [] e) x.length=none) := by
  constructor
  · intro hs k
    cases hv : evV (RecursiveScannerProductCompiler.target M (entries read finish controls) bodies) x .callByValueSeq
        (tblV (RecursiveScannerProductCompiler.target M (entries read finish controls) bodies) x .callByValueSeq k)
        [] (RecursiveScannerProductCompiler.plain M bodies [] e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff M read finish controls bodies alphabet h e he ha x v).mpr ⟨k,hv⟩
      rw [hs j] at hj
      cases hj
  · intro ht k
    cases hv : evV (source M controls bodies) x .callByValuePar
        (tblV (source M controls bodies) x .callByValuePar k) [] (sourceExpr M e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff M read finish controls bodies alphabet h e he ha x v).mp ⟨k,hv⟩
      rw [ht j] at hj
      cases hj

end Shallot.MacroPeg.CBV.GuardedFinitePrefix
