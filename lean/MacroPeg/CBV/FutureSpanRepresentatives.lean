import MacroPeg.CBV.SequentialSpanRecompute
import MacroPeg.CBV.FutureCaptureViews

/-! Represent live retained words by actual copies wholly inside the remaining
input. A missing copy is a failure tag, never an empty successful word.
The search is explicit; no cost bound or grammar-level relocation is claimed. -/
namespace Shallot.MacroPeg.CBV.FutureSpanRepresentatives

abbrev Span := Nat × Nat
abbrev Slots := List (Option Span)
open SequentialSpanRecompute (ValidEnv decodeEnv)

def probe (x : List Char) (span : Span) (p : Nat) : Option Nat :=
  SequentialSpanRecompute.matchCount (span.1-span.2) (sfx x span.1) (sfx x p)

def search (x : List Char) (span : Span) : List Nat → Option Span
  | [] => none
  | p :: ps => match probe x span p with
    | some q => some (p,q)
    | none => search x span ps

def locate (x : List Char) (bound : Nat) (span : Span) : Option Span :=
  search x span (List.range (bound+1))

theorem probe_eq (x : List Char) (span : Span) (p : Nat) (ha : span.1≤x.length) :
    probe x span p = (Shallot.stripPrefix? (pre x span.1 span.2) (sfx x p)).map List.length := by
  exact Option.some.inj (SequentialSpanRecompute.matchSpan_eq x span.1 span.2 p ha)

private theorem search_some (x : List Char) (span : Span) : ∀ ps p q,
    search x span ps=some (p,q) → p∈ps ∧ probe x span p=some q
  | [], _, _, h => by cases h
  | a::ps, p, q, h => by
    cases hp : probe x span a with
    | none =>
      have ht := search_some x span ps p q (by simpa [search,hp] using h)
      exact ⟨List.mem_cons_of_mem a ht.1,ht.2⟩
    | some b =>
      simp only [search,hp,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨by simp,hp⟩

private theorem search_none (x : List Char) (span : Span) : ∀ ps,
    search x span ps=none ↔ ∀ p∈ps, probe x span p=none
  | [] => by simp [search]
  | a::ps => by
    cases hp : probe x span a <;> simp [search,hp,search_none x span ps]

theorem locate_some {x : List Char} {bound : Nat} {span : Span} {p q : Nat}
    (hb : bound≤x.length) (ha : span.1≤x.length) (h : locate x bound span=some (p,q)) :
    p≤bound ∧ q≤p ∧ pre x p q=pre x span.1 span.2 := by
  obtain ⟨hm,hprobe⟩ := search_some x span _ p q h
  have hp : p≤bound := by have := List.mem_range.mp hm; omega
  rw [probe_eq x span p ha] at hprobe
  cases hs : Shallot.stripPrefix? (pre x span.1 span.2) (sfx x p) with
  | none => simp [hs] at hprobe
  | some rest =>
    have hr : rest.length=q := by simpa [hs] using hprobe
    have hsplit := (CBVtoCBN.stripPrefix_exact _ _ _).mp hs
    have hlen := congrArg List.length hsplit
    rw [length_sfx x (Nat.le_trans hp hb),List.length_append,hr] at hlen
    have hq : q≤p := by omega
    have hx : ∃ prefix0, x=prefix0++rest := by
      obtain ⟨prefix0,hx⟩ := sfx_is_suffix x p
      exact ⟨prefix0++pre x span.1 span.2,by rw [List.append_assoc,← hsplit]; exact hx⟩
    have hrx : sfx x q=rest := by rw [← hr]; exact sfx_suffix hx.choose_spec
    have hw : pre x span.1 span.2=pre x p q :=
      (CBVtoCBN.pre_literal_iff x span.1 span.2 p q (Nat.le_trans hp hb) hq).mp (by rw [hrx]; exact hs)
    exact ⟨hp,hq,hw.symm⟩

theorem locate_none {x : List Char} {bound : Nat} {span : Span}
    (ha : span.1≤x.length) : locate x bound span=none ↔
      ∀ p, p≤bound → Shallot.stripPrefix? (pre x span.1 span.2) (sfx x p)=none := by
  rw [locate,search_none]
  constructor
  · intro h p hp
    have hh := h p (List.mem_range.mpr (by omega))
    rw [probe_eq x span p ha] at hh
    cases hs : Shallot.stripPrefix? (pre x span.1 span.2) (sfx x p) <;> simp_all
  · intro h p hp
    rw [probe_eq x span p ha,h p (by have := List.mem_range.mp hp; omega)]
    rfl

def normalize (x : List Char) (bound : Nat) (E : SequentialSpanRecompute.Env) : Slots :=
  E.map (locate x bound)

def environment (slots : Slots) : SequentialSpanRecompute.Env := slots.map (·.getD (0,0))

def views (slots : Slots) : List MExp :=
  slots.mapIdx (fun k span => if span.isSome then .param k else MExp.failAlways)

theorem environment_length (x : List Char) (bound : Nat) (E : SequentialSpanRecompute.Env) :
    (environment (normalize x bound E)).length=E.length := by simp [environment,normalize]

theorem environment_valid {x : List Char} {bound : Nat} {E : SequentialSpanRecompute.Env}
    (hb : bound≤x.length) (hE : ValidEnv x.length E) :
    ValidEnv bound (environment (normalize x bound E)) := by
  intro span hs
  obtain ⟨slot,hslot,rfl⟩ := List.mem_map.mp hs
  obtain ⟨old,hold,hslot⟩ := List.mem_map.mp hslot
  cases slot with
  | none => exact ⟨Nat.le_refl _,Nat.zero_le _⟩
  | some live =>
    have hl := locate_some hb (hE old hold).2 hslot
    exact ⟨hl.2.1,hl.1⟩

private theorem argAt_get : ∀ (P : List MExp) k, argAt P k=P[k]?
  | [],_ => rfl
  | _::_,0 => rfl
  | _::P,k+1 => argAt_get P k

theorem views_lookup (slots : Slots) (k : Nat) :
    argAt (views slots) k = (slots[k]?).map (fun span => if span.isSome then .param k else MExp.failAlways) := by
  simp [argAt_get,views,List.getElem?_mapIdx]

theorem parameter_view {x : List Char} {bound : Nat} {E : SequentialSpanRecompute.Env}
    (hb : bound≤x.length) (hE : ValidEnv x.length E)
    (g : MGrammar) (s : Strategy) (T : SequentialClock.Table) (k p : Nat) (hp : p≤bound) :
    evV g x s T (decodeEnv x (environment (normalize x bound E)))
        (MExp.subst (views (normalize x bound E)) (.param k)) p =
      evV g x s T (decodeEnv x E) (.param k) p := by
  have hn : (normalize x bound E)[k]? = E[k]?.map (locate x bound) := by simp [normalize]
  have he : (decodeEnv x (environment (normalize x bound E)))[k]? =
      ((normalize x bound E)[k]?).map (fun slot => pre x (slot.getD (0,0)).1 (slot.getD (0,0)).2) := by
    simp [decodeEnv,environment,List.getElem?_map,Function.comp_def]
  cases hs : E[k]? with
  | none => simp [MExp.subst,views_lookup,hn,hs,evV,decodeEnv,MExp.failAlways]
  | some old =>
    have ha := (hE old (List.mem_of_getElem? hs)).2
    cases hl : locate x bound old with
    | none =>
      have hd := (locate_none ha).mp hl p hp
      simp [MExp.subst,views_lookup,hn,hs,hl,evV,decodeEnv,MExp.failAlways,hd]
    | some live =>
      have hw := (locate_some hb ha hl).2.2
      simp only [MExp.subst,views_lookup,hn,hs,Option.map_some,hl,Option.isSome_some,
        if_true]
      simp only [evV]
      rw [he]
      simp [hn,hs,hl,decodeEnv,hw]

/-- The body code depends only on a finite Boolean mask, not on input words
or the numerical positions chosen to represent them. -/
def maskViews (mask : List Bool) : List MExp :=
  mask.mapIdx (fun k live => if live then .param k else MExp.failAlways)

theorem views_mask (slots : Slots) :
    views slots = maskViews (slots.map Option.isSome) := by
  apply List.ext_getElem?
  intro k
  simp [views,maskViews,List.getElem?_mapIdx,Function.comp_def]

def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (masks n).map (false :: ·) ++ (masks n).map (true :: ·)

theorem masks_length (n : Nat) : (masks n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [masks,ih,Nat.pow_succ]; omega

theorem mem_masks (mask : List Bool) : mask ∈ masks mask.length := by
  induction mask with
  | nil => simp [masks]
  | cons b bs ih => cases b <;> simp [masks,ih]

def variants (arity : Nat) (e : MExp) : List MExp :=
  (masks arity).map (fun mask => MExp.subst (maskViews mask) e)

theorem variants_length (arity : Nat) (e : MExp) :
    (variants arity e).length = 2^arity := by simp [variants,masks_length]

theorem body_variant (x : List Char) (bound : Nat) (E : SequentialSpanRecompute.Env) (e : MExp) :
    MExp.subst (views (normalize x bound E)) e ∈ variants E.length e := by
  rw [views_mask]
  apply List.mem_map.mpr
  refine ⟨(normalize x bound E).map Option.isSome, ?_, rfl⟩
  have h := mem_masks ((normalize x bound E).map Option.isSome)
  simpa [normalize] using h

/-- One finite body variant, determined solely by the live/dead mask,
executes at the unchanged entry position using future-only span values. -/
theorem expression {g : MGrammar} {x : List Char} {s : Strategy} {T : SequentialClock.Table}
    (hs : s≠.callByName) (hT : SoundTV g x s T) {bound : Nat} (hb : bound≤x.length)
    (E : SequentialSpanRecompute.Env) (hE : ValidEnv x.length E)
    (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤bound) :
    evV g x s T (decodeEnv x (environment (normalize x bound E)))
      (MExp.subst (views (normalize x bound E)) e) p = evV g x s T (decodeEnv x E) e p :=
  FutureCaptureViews.evV_rebind hs hT hb _ _
    (fun k q hq => parameter_view hb hE g s T k q hq) e he p hp

end Shallot.MacroPeg.CBV.FutureSpanRepresentatives
