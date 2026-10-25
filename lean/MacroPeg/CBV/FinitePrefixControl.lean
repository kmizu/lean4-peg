import MacroPeg.CBV.AutomaticOriginControl

namespace Shallot.MacroPeg.CBV.FinitePrefixControl
open ReplayControlFusion (Plan)
open ScannerOriginControl (Part sourceLeaf)
open RecursiveScannerProductCompiler (Arg Entry)
open StatefulScanner (Machine)

/-- Consuming leaves are literal words. Retained-value predicates, sequence,
priority choice, and negation may be nested at arbitrary finite depth. -/
inductive Prefix where
  | lit : List Char → Prefix
  | query : Bool → Prefix
  | seq : Prefix → Prefix → Prefix
  | alt : Prefix → Prefix → Prefix
  | notP : Prefix → Prefix

def raw : Prefix → MExp
  | .lit w => .lit w
  | .query positive => PrefixCaptureQuery.query positive (.param 0)
  | .seq a b => .seq (raw a) (raw b)
  | .alt a b => .alt (raw a) (raw b)
  | .notP a => .notP (raw a)

def outputs : Prefix → List (List Char)
  | .lit w => [w]
  | .query _ | .notP _ => [[]]
  | .seq a b => (outputs a).flatMap (fun u => (outputs b).map (u++·))
  | .alt a b => outputs a++outputs b

def choose (test yes no : Plan) : Plan := .alt (.guard test yes) (.guard (.notP test) no)

theorem choose_eval (L : Nat → Res) (p : Nat) (test yes no : Plan) :
    (choose test yes no).eval L p = match test.eval L p with
    | none => none | some none => no.eval L p | some (some _) => yes.eval L p := by
  cases ht : test.eval L p with
  | none => simp [choose,Plan.eval,ht,ReplayFallbackFusion.orElse]
  | some v => cases v with
    | none => simp [choose,Plan.eval,ht,ReplayFallbackFusion.orElse]
    | some q =>
      cases hy : yes.eval L p with
      | none => simp [choose,Plan.eval,ht,hy,ReplayFallbackFusion.orElse]
      | some v => cases v <;> simp [choose,Plan.eval,ht,hy,ReplayFallbackFusion.orElse]

def compile (read copy : List Char → Nat) : Prefix → List Char → (List Char → Plan) → Plan
  | .lit w,u,K => .guard (.leaf (read (u++w))) (K (u++w))
  | .query positive,u,K => .guard (if positive then .leaf (copy u) else .notP (.leaf (copy u))) (K u)
  | .seq a b,u,K => compile read copy a u (fun v => compile read copy b v K)
  | .alt a b,u,K => choose (compile read copy a u (fun v => .leaf (read v)))
      (compile read copy a u K) (compile read copy b u K)
  | .notP a,u,K => .guard (.notP (compile read copy a u (fun v => .leaf (read v)))) (K u)

def readCheck {n : Nat} (parts : List (Part n)) (read : List Char → Nat) (u : List Char) : Bool :=
  match parts[read u]? with
  | some r => r.closed && match r.body with | .lit v => decide (v=u) | _ => false
  | none => false

def copyCheck {n : Nat} (parts : List (Part n)) (copy : List Char → Nat) (u : List Char) : Bool :=
  match parts[copy u]? with
  | some r => !r.closed && match r.entry,r.body with
    | .shift q R,.lit [] => decide ((R q).getD []=u)
    | .replay,.lit [] => decide (u=[])
    | _,_ => false
  | none => false

def checkAt {n : Nat} (parts : List (Part n)) (read copy : List Char → Nat) : Prefix → List Char → Bool
  | .lit w,u => readCheck parts read u && readCheck parts read (u++w)
  | .query _,u => readCheck parts read u && copyCheck parts copy u
  | .seq a b,u => checkAt parts read copy a u && (outputs a).all (fun v => checkAt parts read copy b (u++v))
  | .alt a b,u => checkAt parts read copy a u && checkAt parts read copy b u
  | .notP a,u => readCheck parts read u && checkAt parts read copy a u

theorem read_sound {n : Nat} (M : Machine n) (parts : List (Part n)) (read : List Char → Nat)
    (u : List Char) (h : readCheck parts read u=true) : sourceLeaf M parts (read u)=.lit u := by
  unfold readCheck at h
  cases hr : parts[read u]? with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h
    obtain ⟨hc,hb⟩ := Bool.and_eq_true_iff.mp h
    cases he : r.body <;> simp [he] at hb
    rename_i v
    subst v
    simp [sourceLeaf,hr,hc,he,RecursiveScannerProductCompiler.sourceExpr]

theorem copy_sound {n : Nat} (M : Machine n) (parts : List (Part n)) (copy : List Char → Nat)
    (u : List Char) (h : copyCheck parts copy u=true) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (sourceLeaf M parts (copy u)) p=evV g x s T E (.seq (.lit u) (.param 0)) p := by
  unfold copyCheck at h
  cases hr : parts[copy u]? with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h
    obtain ⟨hc,hb⟩ := Bool.and_eq_true_iff.mp h
    have hclosed : r.closed=false := by simpa using hc
    cases he : r.entry <;> cases hd : r.body <;> simp only [he,hd] at hb
    all_goals try contradiction
    case replay.lit w =>
      cases w with
      | cons _ _ => simp at hb
      | nil =>
        have hu : u=[] := of_decide_eq_true hb
        subst u
        simp only [sourceLeaf,hr,hclosed,Bool.false_eq_true,ite_false,he,hd,RecursiveScannerProductCompiler.sourceHeader,RecursiveScannerProductCompiler.sourceExpr]
        rw [PrefixCaptureQuery.word_empty _ _ _ _ _ (.param 0) True.intro]
        rw [WordArguments.word_eval g x s T E (.seq (.lit []) (.param 0)) ⟨True.intro,True.intro⟩ p,
          WordArguments.word_eval g x s T E (.param 0) True.intro p]
        simp [WordArguments.value]
    case shift.lit q R w =>
      cases w with
      | cons _ _ => simp at hb
      | nil =>
        have hu := of_decide_eq_true hb
        simp only [sourceLeaf,hr,hclosed,Bool.false_eq_true,ite_false,he,hd,RecursiveScannerProductCompiler.sourceHeader,RecursiveScannerProductCompiler.sourceExpr,hu]
        exact PrefixCaptureQuery.word_empty g x s T E (.seq (.lit u) (.param 0)) ⟨True.intro,True.intro⟩ p

theorem literal_append (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (u v : List Char) (p q : Nat)
    (hu : evV g x s T E (.lit u) p=some (some q)) :
    evV g x s T E (.lit (u++v)) p=evV g x s T E (.lit v) q := by
  rw [←CaptureViews.sequence_literals g x s T E u v p,evV_seq_ok hu]

private theorem query_position (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (e : MExp) (positive : Bool) (p q : Nat)
    (h : evV g x s T E (PrefixCaptureQuery.query positive e) p=some (some q)) : q=p := by
  cases positive with
  | false =>
    cases hv : evV g x s T E e p with
    | none => simp [PrefixCaptureQuery.query,evV,hv] at h
    | some v => cases v with
      | none => simpa [PrefixCaptureQuery.query,evV,hv] using h.symm
      | some r => simp [PrefixCaptureQuery.query,evV,hv] at h
  | true =>
    change evV g x s T E (.andP e) p=_ at h
    rw [CallLookahead.evV_peek] at h
    cases hv : evV g x s T E e p with
    | none => simp [hv,CallLookahead.peek] at h
    | some v => cases v with
      | none => simp [hv,CallLookahead.peek] at h
      | some r => simpa [hv,CallLookahead.peek] using h.symm

/-- Successful bounded consumption determines one of finitely many exact
literal endpoints. Predicate outcomes still depend on the full old capture. -/
theorem success_word (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) : ∀ e p q, p≤x.length → evV g x s T E (raw e) p=some (some q) →
      ∃ w∈outputs e, evV g x s T E (.lit w) p=some (some q)
  | .lit w,p,q,_,h => ⟨w,by simp [outputs],h⟩
  | .query positive,p,q,hp,h => by
    have he := query_position g x s T E (.param 0) positive p q h
    subst q
    exact ⟨[],by simp [outputs],by simp [evV,Shallot.stripPrefix?,length_sfx x hp]⟩
  | .notP a,p,q,hp,h => by
    have he := query_position g x s T E (raw a) false p q h
    subst q
    exact ⟨[],by simp [outputs],by simp [evV,Shallot.stripPrefix?,length_sfx x hp]⟩
  | .seq a b,p,q,hp,h => by
    cases ha : evV g x s T E (raw a) p with
    | none => rw [raw,evV_seq_none ha] at h; cases h
    | some r => cases r with
      | none => rw [raw,evV_seq_fail ha] at h; cases h
      | some j =>
        rw [raw,evV_seq_ok ha] at h
        obtain ⟨u,hu,huv⟩ := success_word g x s T E a p j hp ha
        have hj := (SequenceArguments.success_prefix g x s T E (.lit u) True.intro p j hp huv).1
        obtain ⟨v,hv,hvv⟩ := success_word g x s T E b j q hj h
        exact ⟨u++v,List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv,rfl⟩⟩,
          (literal_append g x s T E u v p j huv).trans hvv⟩
  | .alt a b,p,q,hp,h => by
    cases ha : evV g x s T E (raw a) p with
    | none => rw [raw,evV_alt_none ha] at h; cases h
    | some r => cases r with
      | none =>
        rw [raw,evV_alt_fail ha] at h
        obtain ⟨v,hv,he⟩ := success_word g x s T E b p q hp h
        exact ⟨v,List.mem_append_right _ hv,he⟩
      | some j =>
        rw [raw,evV_alt_ok ha] at h
        obtain ⟨v,hv,he⟩ := success_word g x s T E a p q hp (ha.trans h)
        exact ⟨v,List.mem_append_left _ hv,he⟩

theorem output_checked {n : Nat} (parts : List (Part n)) (read copy : List Char → Nat) :
    ∀ e u, checkAt parts read copy e u=true → ∀ v∈outputs e, readCheck parts read (u++v)=true
  | .lit w,u,h,v,hv => by
    have he : v=w := by simpa [outputs] using hv
    subst v; exact (Bool.and_eq_true_iff.mp h).2
  | .query _,u,h,v,hv | .notP _,u,h,v,hv => by
    have he : v=[] := by simpa [outputs] using hv
    subst v; simpa using (Bool.and_eq_true_iff.mp h).1
  | .alt a b,u,h,v,hv => by
    rcases List.mem_append.mp hv with hv | hv
    · exact output_checked parts read copy a u (Bool.and_eq_true_iff.mp h).1 v hv
    · exact output_checked parts read copy b u (Bool.and_eq_true_iff.mp h).2 v hv
  | .seq a b,u,h,v,hv => by
    obtain ⟨v1,h1,h2⟩ := List.mem_flatMap.mp hv
    obtain ⟨v2,hv2,rfl⟩ := List.mem_map.mp h2
    have hb := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) v1 h1
    simpa [List.append_assoc] using output_checked parts read copy b (u++v1) hb v2 hv2

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
theorem compile_eval {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    ∀ e u, checkAt parts read copy e u=true → ∀ q, q≤x.length →
    evV g x s T E (.lit u) p=some (some q) → ∀ K (kont : Nat → Res),
    (∀ v∈outputs e, ∀ r, evV g x s T E (.lit (u++v)) p=some (some r) →
      (K (u++v)).eval (fun j => evV g x s T E (sourceLeaf M parts j) p) p=kont r) →
    (compile read copy e u K).eval (fun j => evV g x s T E (sourceLeaf M parts j) p) p=
      match evV g x s T E (raw e) q with | some (some r) => kont r | other => other
  | .lit w,u,h,q,hq,hu,K,kont,hK => by
    have hr := read_sound M parts read (u++w) (Bool.and_eq_true_iff.mp h).2
    simp only [raw,compile,Plan.eval,hr,literal_append g x s T E u w p q hu]
    cases hv : evV g x s T E (.lit w) q with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some r => exact hK w (by simp [outputs]) r ((literal_append g x s T E u w p q hu).trans hv)
  | .query positive,u,h,q,hq,hu,K,kont,hK => by
    have hc := copy_sound M parts copy u (Bool.and_eq_true_iff.mp h).2 g x s T E p
    rw [evV_seq_ok hu] at hc
    have hk := hK [] (by simp [outputs]) q (by simpa using hu)
    simp only [List.append_nil] at hk
    simp only [compile,Plan.eval,raw,query_eval]
    cases positive <;>
      cases hv : evV g x s T E (.param 0) q with
      | none => simp only [Bool.false_eq_true,ite_false,ite_true,Plan.eval,hc,hv]
      | some v => cases v <;> simp only [Bool.false_eq_true,ite_false,ite_true,Plan.eval,hc,hv,hk]
  | .seq a b,u,h,q,hq,hu,K,kont,hK => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp only [compile]
    rw [compile_eval M parts read copy g x s T E p hp a u ha q hq hu _
      (fun j => match evV g x s T E (raw b) j with | some (some r) => kont r | other => other)]
    · simp only [raw,evV]
      cases evV g x s T E (raw a) q with
      | none => rfl
      | some v => cases v <;> rfl
    · intro v hv j hj
      have hjbound := (SequenceArguments.success_prefix g x s T E (.lit (u++v)) True.intro p j
        hp hj).1
      apply compile_eval M parts read copy g x s T E p hp b (u++v) ((List.all_eq_true.mp hb) v hv) j hjbound hj K kont
      intro w hw r hr
      have hm : v++w∈outputs (.seq a b) := List.mem_flatMap.mpr ⟨v,hv,List.mem_map.mpr ⟨w,hw,rfl⟩⟩
      simpa [List.append_assoc] using hK (v++w) hm r (by simpa [List.append_assoc] using hr)
  | .alt a b,u,h,q,hq,hu,K,kont,hK => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    have ht := compile_eval M parts read copy g x s T E p hp a u ha q hq hu
      (fun v => .leaf (read v)) (fun r => some (some r)) (by
        intro v hv r hr
        simpa only [Plan.eval,read_sound M parts read _ (output_checked parts read copy a u ha v hv)] using hr)
    simp only [compile,choose_eval]
    rw [ht]
    cases hv : evV g x s T E (raw a) q with
    | none => rw [raw,evV_alt_none hv]
    | some v => cases v with
      | none =>
        rw [raw,evV_alt_fail hv]
        exact compile_eval M parts read copy g x s T E p hp b u hb q hq hu K kont
          (fun v hv => hK v (List.mem_append_right _ hv))
      | some r =>
        rw [raw,evV_alt_ok hv]
        have hh := compile_eval M parts read copy g x s T E p hp a u ha q hq hu K kont
          (fun v hv => hK v (List.mem_append_left _ hv))
        simpa [hv] using hh
  | .notP a,u,h,q,hq,hu,K,kont,hK => by
    have ha := (Bool.and_eq_true_iff.mp h).2
    have ht := compile_eval M parts read copy g x s T E p hp a u ha q hq hu
      (fun v => .leaf (read v)) (fun r => some (some r)) (by
        intro v hv r hr
        simpa only [Plan.eval,read_sound M parts read _ (output_checked parts read copy a u ha v hv)] using hr)
    have hk := hK [] (by simp [outputs]) q (by simpa using hu)
    simp only [List.append_nil] at hk
    simp only [compile,Plan.eval,ht]
    cases hv : evV g x s T E (raw a) q with
    | none => simp [raw,evV,hv]
    | some v => cases v <;> simp [raw,evV,hv,hk]

def plan (read copy : List Char → Nat) (e : Prefix) : Plan :=
  compile read copy e [] (fun v => .leaf (read v))

theorem body_eval {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (e : Prefix) (h : checkAt parts read copy e []=true) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (raw e) p=evV g x s T E ((plan read copy e).exp (sourceLeaf M parts)) p := by
  rw [Plan.exp_eval]
  have hc := compile_eval M parts read copy g x s T E p hp e [] h p hp
    (by simp [evV,Shallot.stripPrefix?,length_sfx x hp]) (fun v => .leaf (read v)) (fun r => some (some r)) (by
      intro v hv r hr
      simpa only [Plan.eval,read_sound M parts read _ (output_checked parts read copy e [] h v hv)] using hr)
  change _=(compile read copy e [] (fun v => .leaf (read v))).eval _ p
  rw [hc]
  cases evV g x s T E (raw e) p with
  | none => rfl
  | some v => cases v <;> rfl

def plans (read copy : List Char → Nat) (bodies : List Prefix) : List Plan := bodies.map (plan read copy)

def source {n : Nat} (M : Machine n) (bodies : List Prefix) : MGrammar :=
  ⟨RecursiveScannerProductCompiler.helpers M++bodies.map (fun b => ⟨1,raw b⟩)⟩

def check {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Prefix) : Bool :=
  bodies.all (fun b => checkAt parts read copy b []) &&
    AutomaticOriginControl.check M parts (plans read copy bodies)

theorem raw_firstOrder : ∀ e, (raw e).FirstOrder
  | .lit _ => True.intro
  | .query positive => by cases positive <;> trivial
  | .seq a b | .alt a b => ⟨raw_firstOrder a,raw_firstOrder b⟩
  | .notP a => raw_firstOrder a

theorem source_firstOrder {n : Nat} (M : Machine n) (bodies : List Prefix) : (source M bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact RecursiveScannerProductCompiler.helpers_firstOrder M r hr
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact raw_firstOrder b

theorem source_rule {n : Nat} (M : Machine n) (bodies : List Prefix) (i : Nat) (b : Prefix)
    (hi : bodies[i]?=some b) :
    ruleAtM (source M bodies).rules (RecursiveScannerProductCompiler.offset M+i)=some ⟨1,raw b⟩ := by
  simp [source,RecursiveScannerProductCompiler.offset,ruleAtM_eq_getElem?,
    List.getElem?_append_right (by omega : (RecursiveScannerProductCompiler.helpers M).length≤(RecursiveScannerProductCompiler.helpers M).length+i),hi]

theorem related {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Prefix) (h : check M parts read copy bodies=true) :
    SemanticBodyRewrite.Related (source M bodies)
      (ScannerOriginControl.original M parts (plans read copy bodies)) .callByValuePar := by
  intro i
  unfold source ScannerOriginControl.original ScannerOriginControl.rules plans
  simp only [ruleAtM_eq_getElem?,List.map_map]
  by_cases hi : i<(RecursiveScannerProductCompiler.helpers M).length
  · simp only [List.getElem?_append_left hi]
    cases (RecursiveScannerProductCompiler.helpers M)[i]? with
    | none => trivial
    | some r => exact ⟨rfl,fun _ _ _ _ _ => rfl⟩
  · have hi' : (RecursiveScannerProductCompiler.helpers M).length≤i := by omega
    simp only [List.getElem?_append_right hi',List.getElem?_map]
    cases hb : bodies[i-(RecursiveScannerProductCompiler.helpers M).length]? with
    | none => trivial
    | some b =>
      exact ⟨rfl,fun x T E p hp => body_eval M parts read copy b
        ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1) b (List.mem_of_getElem? hb)) _ x .callByValuePar T E p hp⟩

theorem observations_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Prefix) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source M bodies) .callByValuePar (RecursiveScannerProductCompiler.sourceExpr M e) x rest ↔
      SObs (ScannerOriginControl.target M parts (plans read copy bodies)) .callByValueSeq
        (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x rest :=
  (SemanticBodyRewrite.observations (related M parts read copy bodies h) (source_firstOrder M bodies)
    (ScannerOriginControl.original_firstOrder M parts _) (by decide) _
    (RecursiveScannerProductCompiler.sourceExpr_firstOrder M e) x rest).trans
      (AutomaticOriginControl.observations_iff M parts _ (Bool.and_eq_true_iff.mp h).2 e he x rest)

theorem language_translation {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Prefix) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source M bodies) .callByValuePar (RecursiveScannerProductCompiler.sourceExpr M e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  ⟨_,_,RecursiveScannerProductCompiler.target_firstOrder M _ _,
    RecursiveScannerProductCompiler.plain_firstOrder M _ [] _,
    fun x => observations_iff M parts read copy bodies h e he x (some [])⟩

theorem defined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Prefix) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M bodies) x .callByValuePar (tblV (source M bodies) x .callByValuePar k)
      [] (RecursiveScannerProductCompiler.sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq
      (tblV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq k) []
      (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x.length=some v) := by
  have ha := (Bool.and_eq_true_iff.mp h).2
  obtain ⟨hH,hC,hB,hRoot⟩ := AutomaticOriginControl.certificates M parts _ ha e he
  have hc := ScannerOriginControl.defined_iff M parts _ (Bool.and_eq_true_iff.mp ha).1 e he _ _ _ hH hC hB hRoot x v
  have hp := fun k => SemanticBodyRewrite.physical (related M parts read copy bodies h) x k []
    (RecursiveScannerProductCompiler.sourceExpr M e) x.length
  constructor
  · rintro ⟨k,hk⟩
    exact hc.mp ⟨k,(hp k).symm.trans hk⟩
  · intro ht
    obtain ⟨k,hk⟩ := hc.mpr ht
    exact ⟨k,(hp k).trans hk⟩

theorem undefined_iff {n : Nat} (M : Machine n) (parts : List (Part n)) (read copy : List Char → Nat)
    (bodies : List Prefix) (h : check M parts read copy bodies=true) (e : Arg)
    (he : ScannerOriginControl.scopeCheck (plans read copy bodies) e=true) (x : List Char) :
    (∀ k, evV (source M bodies) x .callByValuePar (tblV (source M bodies) x .callByValuePar k)
      [] (RecursiveScannerProductCompiler.sourceExpr M e) x.length=none) ↔
    (∀ k, evV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq
      (tblV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq k) []
      (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x.length=none) := by
  constructor
  · intro hs k
    cases hv : evV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq
        (tblV (ScannerOriginControl.target M parts (plans read copy bodies)) x .callByValueSeq k) []
        (ScannerOriginControl.targetExpr M parts (plans read copy bodies) e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff M parts read copy bodies h e he x v).mpr ⟨k,hv⟩
      rw [hs j] at hj
      cases hj
  · intro ht k
    cases hv : evV (source M bodies) x .callByValuePar (tblV (source M bodies) x .callByValuePar k)
        [] (RecursiveScannerProductCompiler.sourceExpr M e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff M parts read copy bodies h e he x v).mp ⟨k,hv⟩
      rw [ht j] at hj
      cases hj

end Shallot.MacroPeg.CBV.FinitePrefixControl
