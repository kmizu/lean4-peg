import MacroPeg.CBV.RecapturedCopyTransfer

/-! Control after a fixed retained-word period. A period is represented
by its complete real captured block; following control may consume
different amounts on different iterations and may itself be partial. -/
namespace Shallot.MacroPeg.CBV.CopyPeriodControl
open DelimiterTemplate DelimitedWordPattern ClockFreezing

inductive Tail where
  | eps | any | chr (c : Char) | range (lo hi : Char) | lit (w : List Char)
  | block | helper (i : Nat)
  | seq (a b : Tail) | alt (a b : Tail) | notP (a : Tail) | star (a : Tail)
  deriving Repr

def render (P : MExp) : Tail → MExp
  | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
  | .block => P | .helper i => .call i []
  | .seq a b => .seq (render P a) (render P b)
  | .alt a b => .alt (render P a) (render P b)
  | .notP a => .notP (render P a) | .star a => .star (render P a)

def check (helpers : Nat) : Tail → Bool
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .block => true
  | .helper i => decide (i<helpers)
  | .seq a b | .alt a b => check helpers a && check helpers b
  | .notP a | .star a => check helpers a

theorem firstOrder (P : MExp) (hP : P.FirstOrder) : ∀ e, (render P e).FirstOrder
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .helper _ => True.intro
  | .block => hP
  | .seq a b | .alt a b => ⟨firstOrder P hP a,firstOrder P hP b⟩
  | .notP a | .star a => firstOrder P hP a

theorem physical (bodies : List MExp) (g h : MGrammar)
    (hb : RecursiveParserStability.Valid bodies)
    (hg : RecursiveParserStability.Installed bodies g) (hh : RecursiveParserStability.Installed bodies h)
    (x : List Char) (k : Nat) (W : List (List Char)) (d : Char) (js : List Nat)
    (hs : ∀ i∈js, i<W.length) :
    ∀ e, check bodies.length e=true → ∀ p, p≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar k) W (render (compile d (sourceParts d js)) e) p=
        evV h x .callByValueSeq (tblV h x .callByValueSeq k) [encode d W js] (render (.param 0) e) p
  | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ => rfl
  | .block,_,p,hp => by
    rw [render,RecapturedCopyBlock.step_literal g x .callByValuePar _ W d js hs p hp]
    rfl
  | .helper i,hc,p,hp => by
    have hi : i<bodies.length := of_decide_eq_true hc
    have hr := List.getElem?_eq_getElem hi
    simp only [render]
    rw [evV_call_par (hg i bodies[i] hr) rfl (by decide),evPar_nil,
      evV_call_seq (hh i bodies[i] hr) rfl,evSeq_nil]
    exact congrArg (fun row => valAt row p) (RecursiveParserStability.helper_rows_eq hb hg hh x _ _ k i hi [] [])
  | .seq a b,hc,p,hp => by
    simp only [render]
    have ha := physical bodies g h hb hg hh x k W d js hs a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases hv : evV g x .callByValuePar (tblV g x .callByValuePar k) W (render (compile d (sourceParts d js)) a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some r => cases r with
      | none => rw [evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact physical bodies g h hb hg hh x k W d js hs b (Bool.and_eq_true_iff.mp hc).2 q
          (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
  | .alt a b,hc,p,hp => by
    simp only [render]
    have ha := physical bodies g h hb hg hh x k W d js hs a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases hv : evV g x .callByValuePar (tblV g x .callByValuePar k) W (render (compile d (sourceParts d js)) a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some r => cases r with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact physical bodies g h hb hg hh x k W d js hs b (Bool.and_eq_true_iff.mp hc).2 p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .notP a,hc,p,hp => by
    simp only [render,evV,physical bodies g h hb hg hh x k W d js hs a hc p hp]
  | .star a,hc,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => physical bodies g h hb hg hh x k W d js hs a hc q (by omega))

def sourceBody (d : Char) (js : List Nat) (tail : Tail) : MExp :=
  .star (.seq (compile d (sourceParts d js)) (render (compile d (sourceParts d js)) tail))
def probeBody (tail : Tail) : MExp := render (.param 0) tail
def runBody (tail : Tail) : MExp :=
  .seq (probeBody tail) (.star (.seq (.param 0) (probeBody tail)))

theorem iteration (bodies : List MExp) (g h : MGrammar) (hb : RecursiveParserStability.Valid bodies)
    (hg : RecursiveParserStability.Installed bodies g) (hh : RecursiveParserStability.Installed bodies h)
    (x : List Char) (k : Nat) (W : List (List Char)) (d : Char) (js : List Nat)
    (hs : ∀ i∈js, i<W.length) (tail : Tail) (hc : check bodies.length tail=true)
    (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) W (sourceBody d js tail) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [encode d W js]
        (.star (.seq (.param 0) (probeBody tail))) p := by
  rw [sourceBody,evV_star,evV_star]
  apply evStar_congr p
  intro q hq
  have hbound : q≤x.length := by omega
  have he : evV g x .callByValuePar (tblV g x .callByValuePar k) W (compile d (sourceParts d js)) q=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [encode d W js] (.param 0) q := by
    rw [RecapturedCopyBlock.step_literal g x .callByValuePar _ W d js hs q hbound]
    rfl
  cases hv : evV g x .callByValuePar (tblV g x .callByValuePar k) W (compile d (sourceParts d js)) q with
  | none => rw [evV_seq_none hv,evV_seq_none (he.symm.trans hv)]
  | some r => cases r with
    | none => rw [evV_seq_fail hv,evV_seq_fail (he.symm.trans hv)]
    | some r =>
      rw [evV_seq_ok hv,evV_seq_ok (he.symm.trans hv)]
      exact physical bodies g h hb hg hh x k W d js hs tail hc r (evV_ok (tblV_ok _ _ _ k) _ q hbound r hv)

theorem skeleton_env (d : Char) (E : List (List Char)) : ∀ js y,
    run d E (RecapturedCopyBlock.skeleton d js) y=run d [] (RecapturedCopyBlock.skeleton d js) y
  | [],_ => rfl
  | _::js,y => by
    simp only [RecapturedCopyBlock.skeleton,run,action]
    exact congrArg (fun f => (Shallot.stripPrefix? [d] (y.dropWhile (pred d))).bind f)
      (funext (skeleton_env d E js))

theorem entry (h : MGrammar) (address : Nat) (body : MExp)
    (hr : ruleAtM h.rules address=some ⟨1,body⟩)
    (x : List Char) (E W : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (d : Char) (js : List Nat) (hs : ∀ i∈js, i<W.length)
    (hf : ∀ i, (hi : i<W.length) → DelimitedCopyProjection.Free d W[i])
    (rest : List Char) (hfirst : run d W (sourceParts d js) (sfx x p)=some rest) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
      (.call address [compile d (RecapturedCopyBlock.skeleton d js)]) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [encode d W js] body rest.length := by
  let B := encode d W js
  have hx : sfx x p=B++rest :=
    (CBVtoCBN.stripPrefix_exact _ _ _).mp ((RecapturedCopyBlock.source_run d W js hs _).symm.trans hfirst)
  have hscan : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
      (compile d (RecapturedCopyBlock.skeleton d js)) p=some (some rest.length) := by
    rw [compile_eval h x .callByValueSeq _ E d _ p hp,skeleton_env,hx,
      RecapturedCopyBlock.skeleton_run d W hf js hs rest]
    rfl
  have hq := evV_ok (tblV_ok h x .callByValueSeq (k+1)) _ p hp _ hscan
  have hpre : pre x p rest.length=B := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  rw [evV_call_seq hr rfl,evSeq_cons_ok hscan,evSeq_nil]
  change valAt (tblV h x .callByValueSeq (k+1) address [pre x p rest.length]) rest.length=_
  rw [hpre,valAt_tblV_succ hr [B] hq]

end Shallot.MacroPeg.CBV.CopyPeriodControl
