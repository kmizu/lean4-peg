import MacroPeg.CBV.CopyBodyControl

namespace Shallot.MacroPeg.CBV.CopyBodyEvaluation
open CopyBodyControl
open DelimiterTemplate (Part)
open ClockFreezing (Table)

def partsRun (d : Char) (W : List (List Char)) (history : List Nat) (x : List Char) :=
  DelimiterTemplate.run d W (DelimitedWordPattern.sourceParts d history) x
def step (d : Char) (W : List (List Char)) (i : Nat) (x : List Char) := partsRun d W [i] x
def run (d : Char) (W : List (List Char)) (e : Body) (x : List Char) := CopyBodyControl.eval (step d W) e x
def query (d : Char) (W : List (List Char)) (x : List Char) (history : List Nat) := (partsRun d W history x).isSome

theorem sourceParts_append (d : Char) : ∀ h k,
    DelimitedWordPattern.sourceParts d (h++k)=DelimitedWordPattern.sourceParts d h++DelimitedWordPattern.sourceParts d k
  | [],_ => rfl
  | i::h,k => by simp only [List.cons_append,DelimitedWordPattern.sourceParts,sourceParts_append d h k]

theorem run_append (d : Char) (W : List (List Char)) : ∀ a b x,
    DelimiterTemplate.run d W (a++b) x=(DelimiterTemplate.run d W a x).bind (DelimiterTemplate.run d W b)
  | [],_,_ => rfl
  | p::ps,b,x => by
    simp only [List.cons_append,DelimiterTemplate.run,Option.bind_assoc]
    exact congrArg (fun f => (DelimiterTemplate.action d W p x).bind f) (funext (fun y => run_append d W ps b y))

theorem parts_append (d : Char) (W : List (List Char)) (a b : List Nat) (x : List Char) :
    partsRun d W (a++b) x=(partsRun d W a x).bind (partsRun d W b) := by
  exact (congrArg (fun ps => DelimiterTemplate.run d W ps x) (sourceParts_append d a b)).trans (run_append d W _ _ x)

theorem parts_suffix (d : Char) (W : List (List Char)) (h : List Nat) (x rest : List Char)
    (hh : partsRun d W h x=some rest) : ∃ headPart, x=headPart++rest := by
  have hs : ∀ ps x rest, DelimiterTemplate.run d W ps x=some rest → ∃ headPart, x=headPart++rest := by
    intro ps
    induction ps with
    | nil =>
      intro x rest hh
      have he : x=rest := by simpa [DelimiterTemplate.run] using hh
      exact ⟨[],he⟩
    | cons p ps ih =>
      intro x rest hh
      cases ha : DelimiterTemplate.action d W p x with
      | none => simp [DelimiterTemplate.run,ha] at hh
      | some y => exact suffix_trans (DelimiterTemplate.action_suffix d W p x y ha) (ih y rest (by simpa [DelimiterTemplate.run,ha] using hh))
  exact hs _ x rest hh

theorem run_suffix (d : Char) (W : List (List Char)) (e : Body) (x rest : List Char)
    (hr : run d W e x=some (some rest)) : ∃ headPart, x=headPart++rest :=
  eval_preserves (step d W) (fun y => ∃ headPart, x=headPart++y)
    (fun i a b ha hb => suffix_trans ha (parts_suffix d W [i] a b hb)) e x ⟨[],rfl⟩ rest hr

theorem history_related (d : Char) (W : List (List Char)) (x : List Char) (e : Body) (h : List Nat) (rest : List Char)
    (hh : partsRun d W h x=some rest) :
    Related (fun h rest => partsRun d W h x=some rest)
      (CopyBodyControl.eval (historyStep (query d W x)) e h) (run d W e rest) := by
  apply eval_related (fun h rest => partsRun d W h x=some rest) _ _ _ e h rest hh
  intro i h rest hh
  have he : partsRun d W (h++[i]) x=step d W i rest := by rw [parts_append,hh]; rfl
  cases hs : step d W i rest with
  | none =>
    have hq : query d W x (h++[i])=false := by simp [query,he,hs]
    simp only [historyStep,hq,if_false]
    exact .fail
  | some tail =>
    have hq : query d W x (h++[i])=true := by simp [query,he,hs]
    simp only [historyStep,hq,if_true]
    exact .ok (h++[i]) tail (he.trans hs)

def resolve (d : Char) (W : List (List Char)) (x : List Char) : Result (List Nat) → Res
  | none => none | some none => some none | some (some h) => some ((partsRun d W h x).map List.length)

theorem resolve_related (d : Char) (W : List (List Char)) (x : List Char)
    (a : Result (List Nat)) (b : Result (List Char))
    (h : Related (fun hist rest => partsRun d W hist x=some rest) a b) :
    resolve d W x a=b.map (Option.map List.length) := by
  cases h with
  | undef => rfl
  | fail => rfl
  | ok a b hr => simp [resolve,hr]

theorem normalized_run (d : Char) (W : List (List Char)) (x : List Char) (e : Body) :
    resolve d W x ((normalized e).eval (query d W x))=(run d W e x).map (Option.map List.length) := by
  rw [normalized_eval]
  exact resolve_related d W x _ _ (history_related d W x e [] x rfl)

/-- The original body executes on the real retained tuple, at any table;
zero-width nullable repetition keeps its actual undefined result. -/
theorem physical (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (hT : OkTV x.length T)
    (W : List (List Char)) (d : Char) (arity : Nat) : ∀ e, check arity e=true → ∀ p, p≤x.length →
    evV g x s T W (render d e) p=(run d W e (sfx x p)).map (Option.map List.length)
  | .eps,_,p,hp => by simp [render,evV,run,CopyBodyControl.eval,length_sfx x hp]
  | .fail,_,p,_ => by simp [render,MExp.failAlways,evV,run,CopyBodyControl.eval]
  | .segment i,_,p,hp => by
    rw [render,DelimiterTemplate.compile_eval g x s T W d _ p hp]
    rfl
  | .seq a b,hc,p,hp => by
    have hh := physical g x s T hT W d arity a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases ha : CopyBodyControl.eval (step d W) a (sfx x p) with
    | none =>
      have hh : evV g x s T W (render d a) p=none := by simpa only [run,ha,Option.map_none] using hh
      rw [render,evV_seq_none hh]; simp [run,CopyBodyControl.eval,chain,ha]
    | some v => cases v with
      | none =>
        have hh : evV g x s T W (render d a) p=some none := by simpa only [run,ha,Option.map_some,Option.map_none] using hh
        rw [render,evV_seq_fail hh]; simp [run,CopyBodyControl.eval,chain,ha]
      | some rest =>
        have hh : evV g x s T W (render d a) p=some (some rest.length) := by simpa only [run,ha,Option.map_some] using hh
        have hq := evV_ok hT (render d a) p hp rest.length hh
        have hs : sfx x rest.length=rest := sfx_suffix (suffix_trans (sfx_is_suffix x p) (run_suffix d W a (sfx x p) rest ha)).choose_spec
        rw [render,evV_seq_ok hh,physical g x s T hT W d arity b (Bool.and_eq_true_iff.mp hc).2 rest.length hq,hs]
        simp [run,CopyBodyControl.eval,chain,ha]
  | .alt a b,hc,p,hp => by
    have hh := physical g x s T hT W d arity a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases ha : CopyBodyControl.eval (step d W) a (sfx x p) with
    | none =>
      have hh : evV g x s T W (render d a) p=none := by simpa only [run,ha,Option.map_none] using hh
      rw [render,evV_alt_none hh]; simp [run,CopyBodyControl.eval,choice,ha]
    | some v => cases v with
      | none =>
        have hh : evV g x s T W (render d a) p=some none := by simpa only [run,ha,Option.map_some,Option.map_none] using hh
        rw [render,evV_alt_fail hh,physical g x s T hT W d arity b (Bool.and_eq_true_iff.mp hc).2 p hp]
        simp [run,CopyBodyControl.eval,choice,ha]
      | some rest =>
        have hh : evV g x s T W (render d a) p=some (some rest.length) := by simpa only [run,ha,Option.map_some] using hh
        rw [render,evV_alt_ok hh]; simp [run,CopyBodyControl.eval,choice,ha]
  | .notP a,hc,p,hp => by
    have hh := physical g x s T hT W d arity a hc p hp
    cases ha : CopyBodyControl.eval (step d W) a (sfx x p) with
    | none => simp [render,evV,hh,run,ha,CopyBodyControl.eval,negative]
    | some v => cases v with
      | none => simp [render,evV,hh,run,ha,CopyBodyControl.eval,negative,length_sfx x hp]
      | some rest => simp [render,evV,hh,run,ha,CopyBodyControl.eval,negative]
  | .star a,hc,p,hp => by
    have hh := physical g x s T hT W d arity a (Bool.and_eq_true_iff.mp hc).2 p hp
    cases ha : CopyBodyControl.eval (step d W) a (sfx x p) with
    | none =>
      have hh : evV g x s T W (render d a) p=none := by simpa only [run,ha,Option.map_none] using hh
      rw [render,evV_star,evStar_none hh]; simp [run,CopyBodyControl.eval,repeatZero,ha]
    | some v => cases v with
      | none =>
        have hh : evV g x s T W (render d a) p=some none := by simpa only [run,ha,Option.map_some,Option.map_none] using hh
        rw [render,evV_star,evStar_fail hh]; simp [run,CopyBodyControl.eval,repeatZero,ha,length_sfx x hp]
      | some rest =>
        have hr := eval_zero (step d W) a (Bool.and_eq_true_iff.mp hc).1 (sfx x p) rest ha
        subst rest
        have hh : evV g x s T W (render d a) p=some (some p) := by simpa only [run,ha,Option.map_some,length_sfx x hp] using hh
        rw [render,evV_star,evStar_stuck hh (Nat.lt_irrefl _)]
        simp [run,CopyBodyControl.eval,repeatZero,ha]

end Shallot.MacroPeg.CBV.CopyBodyEvaluation
