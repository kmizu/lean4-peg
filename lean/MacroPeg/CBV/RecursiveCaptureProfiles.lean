import MacroPeg.CBV.RecursiveScannerProductCorrespondence

namespace Shallot.MacroPeg.CBV.RecursiveCaptureProfiles
open RecursiveScannerProductCompiler
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles compose compose_correct profile_mem)
open StatefulScanner (Machine)

abbrev Summary := Nat → List Nat → List (List Nat)

def product (A B : List (List Nat)) : List (List Nat) :=
  A.flatMap (fun P => B.map (compose P))

theorem product_mem (D : RegularCaptureProduct.Machine) (hD : D.Valid)
    (A B : List (List Nat)) (u v : List Char)
    (hu : profile D u∈A) (hv : profile D v∈B) : profile D (u++v)∈product A B := by
  rw [←compose_correct D hD]
  exact List.mem_flatMap.mpr ⟨_,hu,List.mem_map.mpr ⟨_,hv,rfl⟩⟩

/-- Iteration proposes a finite monoid closure; an executable closure test
validates it. Soundness does not assume convergence of the iteration. -/
def grow (A C : List (List Nat)) : List (List Nat) := (C++product A C).eraseDups

def rounds (A : List (List Nat)) : Nat → List (List Nat) → List (List Nat)
  | 0,C => C
  | k+1,C => grow A (rounds A k C)

def closureCheck (D : RegularCaptureProduct.Machine) (A C : List (List Nat)) : Bool :=
  C.contains (profile D []) && A.all (fun P => C.all (fun Q => C.contains (compose P Q)))

def closure (D : RegularCaptureProduct.Machine) (A : List (List Nat)) : List (List Nat) :=
  let C := rounds A (profiles D).length [profile D []]
  if closureCheck D A C then C else profiles D

theorem closure_nil (D : RegularCaptureProduct.Machine) (hD : D.Valid) (A : List (List Nat)) :
    profile D []∈closure D A := by
  dsimp only [closure]
  split
  · exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp ‹closureCheck D A _=true›).1
  · exact profile_mem D hD []

theorem closure_append (D : RegularCaptureProduct.Machine) (hD : D.Valid)
    (A : List (List Nat)) (u v : List Char)
    (hu : profile D u∈A) (hv : profile D v∈closure D A) : profile D (u++v)∈closure D A := by
  dsimp only [closure] at hv ⊢
  split at hv
  · rename_i hc
    rw [if_pos hc]
    rw [←compose_correct D hD]
    exact List.contains_iff_mem.mp
      ((List.all_eq_true.mp ((Bool.and_eq_true_iff.mp hc).2)) _ hu |> fun h =>
        (List.all_eq_true.mp h) _ hv)
  · rename_i hc
    rw [if_neg hc]
    exact profile_mem D hD (u++v)

/-- A summary records possible output profiles for each user and actual
argument profile. Queries retain their real computation and output identity.
Stars include every finite iteration, without fixing an action per operand. -/
def effects {n : Nat} (M : Machine n) (C : Summary) (S : List (List Nat)) : Arg → List (List Nat)
  | .lit w => [profile (observer M) w]
  | .param i => match S[i]? with | none => [] | some P => [P]
  | .user i a => (effects M C S a).flatMap (C i)
  | .seq a b => product (effects M C S a) (effects M C S b)
  | .alt a b => effects M C S a ++ effects M C S b
  | .notP _ => [profile (observer M) []]
  | .star a => closure (observer M) (effects M C S a)

/-- Actual recursive rows are the induction hypothesis; finite grammar
closure below will derive them, rather than taking them as a final input. -/
def Rows {n : Nat} (M : Machine n) (bodies : List Arg) (C : Summary)
    (x : List Char) (T : ClockFreezing.Table) : Prop :=
  ∀ i b, bodies[i]?=some b → ∀ v p q, p≤x.length →
    valAt (T (offset M+i) [v]) p=some (some q) →
    q≤p ∧ ∃ w, profile (observer M) w∈C i (profile (observer M) v) ∧
      sfx x p=w++sfx x q

private theorem literal_shape (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (w : List Char) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T E (.lit w) p=some (some q)) :
    q≤p ∧ sfx x p=w++sfx x q := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [evV,hs] at hv
  | some rest =>
    have hq : rest.length=q := by simpa only [evV,hs,Option.some.injEq] using hv
    have hh := (CBVtoCBN.stripPrefix_exact w (sfx x p) rest).mp hs
    have hr : sfx x rest.length=rest :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨w,hh⟩).choose_spec
    have hl := congrArg List.length hh
    rw [length_sfx x hp,List.length_append] at hl
    exact ⟨by omega,by rw [←hq,hr]; exact hh⟩

def Scoped (bodies : List Arg) : Arg → Prop
  | .user i a => i<bodies.length ∧ Scoped bodies a
  | .seq a b | .alt a b => Scoped bodies a ∧ Scoped bodies b
  | .notP a | .star a => Scoped bodies a
  | _ => True

theorem output_shape {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (C : Summary) (x : List Char) (T : ClockFreezing.Table) (hRows : Rows M bodies C x T)
    (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E) :
    ∀ e, Scoped bodies e → ∀ p q, p≤x.length →
      evV (source M entries bodies) x .callByValuePar T E (sourceExpr M e) p=some (some q) →
      q≤p ∧ ∃ w, profile (observer M) w∈effects M C S e ∧ sfx x p=w++sfx x q
  | .lit w, _, p, q, hp, h => by
    obtain ⟨hq,hs⟩ := literal_shape _ x .callByValuePar T E w p q hp h
    exact ⟨hq,w,by simp [effects],hs⟩
  | .param i, _, p, q, hp, h => by
    cases hw : E[i]? with
    | none => simp [sourceExpr,evV,hw] at h
    | some w =>
      have hl : evV (source M entries bodies) x .callByValuePar T E (.lit w) p=some (some q) := by
        simpa only [sourceExpr,evV,hw] using h
      obtain ⟨hq,hs⟩ := literal_shape _ x .callByValuePar T E w p q hp hl
      exact ⟨hq,w,by simp [effects,hS i w hw],hs⟩
  | .notP a, _, p, q, hp, h => by
    cases ha : evV (source M entries bodies) x .callByValuePar T E (sourceExpr M a) p with
    | none => simp [sourceExpr,evV,ha] at h
    | some v => cases v with
      | some j => simp [sourceExpr,evV,ha] at h
      | none =>
        have hq : p=q := by simpa only [sourceExpr,evV,ha,Option.some.injEq] using h
        subst q; exact ⟨Nat.le_refl _,[],by simp [effects],rfl⟩
  | .seq a b, he, p, q, hp, h => by
    cases ha : evV (source M entries bodies) x .callByValuePar T E (sourceExpr M a) p with
    | none => rw [sourceExpr,evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [sourceExpr,evV_seq_fail ha] at h; cases h
      | some j =>
        rw [sourceExpr,evV_seq_ok ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := output_shape M entries bodies C x T hRows S E hS a he.1 p j hp ha
        obtain ⟨hqj,v,hv,ht⟩ := output_shape M entries bodies C x T hRows S E hS b he.2 j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++v,product_mem _ (valid M) _ _ u v hu hv,by rw [hs,ht,List.append_assoc]⟩
  | .alt a b, he, p, q, hp, h => by
    cases ha : evV (source M entries bodies) x .callByValuePar T E (sourceExpr M a) p with
    | none => simp [sourceExpr,evV,ha] at h
    | some v => cases v with
      | none =>
        obtain ⟨hq,w,hw,hs⟩ := output_shape M entries bodies C x T hRows S E hS b he.2 p q hp
          (by simpa only [sourceExpr,evV,ha] using h)
        exact ⟨hq,w,List.mem_append_right _ hw,hs⟩
      | some j =>
        have hj : j=q := by simpa only [sourceExpr,evV,ha,Option.some.injEq] using h
        subst q
        obtain ⟨hq,w,hw,hs⟩ := output_shape M entries bodies C x T hRows S E hS a he.1 p j hp ha
        exact ⟨hq,w,List.mem_append_left _ hw,hs⟩
  | .star a, he, p, q, hp, h => by
    have hh : ∀ p q, p≤x.length →
        evStar (fun z => evV (source M entries bodies) x .callByValuePar T E (sourceExpr M a) z) p=some (some q) →
        q≤p ∧ ∃ w, profile (observer M) w∈closure (observer M) (effects M C S a) ∧ sfx x p=w++sfx x q := by
      intro p
      induction p using Nat.strongRecOn with
      | ind p ih =>
        intro q hp h
        cases ha : evV (source M entries bodies) x .callByValuePar T E (sourceExpr M a) p with
        | none => rw [evStar_none ha] at h; cases h
        | some v => cases v with
          | none =>
            rw [evStar_fail ha] at h
            have hq : p=q := by simpa using h
            subst q; exact ⟨Nat.le_refl _,[],closure_nil _ (valid M) _,rfl⟩
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj] at h
              obtain ⟨hjp,u,hu,hs⟩ := output_shape M entries bodies C x T hRows S E hS a he p j hp ha
              obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,closure_append _ (valid M) _ u v hu hv,by rw [hs,ht,List.append_assoc]⟩
            · rw [evStar_stuck ha hj] at h; cases h
    exact hh p q hp h
  | .user i a, he, p, q, hp, h => by
    have hib : i<bodies.length := he.1
    have hi : bodies[i]?=some bodies[i] := List.getElem?_eq_getElem he.1
    rw [sourceExpr,evV_call_par (source_rule M entries bodies i bodies[i] hi) rfl (by decide)] at h
    cases ha : evV (source M entries bodies) x .callByValuePar T E (sourceExpr M a) p with
    | none => simp [evParArgs,ha] at h
    | some v => cases v with
      | none => simp [evParArgs,ha] at h
      | some j =>
        simp only [evParArgs,ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := output_shape M entries bodies C x T hRows S E hS a he.2 p j hp ha
        have hpre : pre x p j=u := by
          simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hjp hp)] using pre_eq (sfx_is_suffix x p) hs
        obtain ⟨hq,w,hw,hs⟩ := hRows i bodies[i] hi (pre x p j) p q hp h
        refine ⟨hq,w,List.mem_flatMap.mpr ⟨_,?_,hw⟩,hs⟩
        simpa only [hpre] using hu
termination_by e => sizeOf e

abbrev ScannerSummary (n : Nat) := Fin n → List (List Nat)

def scannerCheck {n : Nat} (M : Machine n) (H : ScannerSummary n) : Bool :=
  (List.finRange n).all (fun q =>
    (H q).contains (profile (observer M) []) &&
      (M.arcs q).all (fun (c,r) => (H r).all (fun P =>
        (H q).contains (compose (profile (observer M) [c]) P))))

private theorem next_mem {Q : Type} (arcs : List (Char × Q)) (c : Char) (q : Q)
    (h : StatefulScanner.next arcs c=some q) : (c,q)∈arcs := by
  induction arcs with
  | nil => simp [StatefulScanner.next] at h
  | cons a arcs ih =>
    obtain ⟨d,r⟩ := a
    by_cases hc : Shallot.beqChar d c=true
    · have hd : d=c := Char.toNat_inj.mp (by simpa [Shallot.beqChar] using hc)
      have hr : r=q := by simpa [StatefulScanner.next,hc] using h
      simp [hd,hr]
    · exact List.mem_cons_of_mem _ (ih (by simpa [StatefulScanner.next,hc] using h))

theorem scanner_profiles {n : Nat} (M : Machine n) (H : ScannerSummary n)
    (hH : scannerCheck M H=true) (q : Fin n) (x : List Char) :
    profile (observer M) (ObservedScanner.consumed M q x)∈H q := by
  have rule := fun q => (List.all_eq_true.mp hH) q (List.mem_finRange q)
  induction x generalizing q with
  | nil => exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp (rule q)).1
  | cons c x ih =>
    cases hs : StatefulScanner.next (M.arcs q) c with
    | none =>
      simpa [ObservedScanner.consumed,hs] using
        List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp (rule q)).1
    | some r =>
      have hstep := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (rule q)).2)
        (c,r) (next_mem (M.arcs q) c r hs)
      have hh := List.contains_iff_mem.mp ((List.all_eq_true.mp hstep) _ (ih r))
      simpa only [compose_correct _ (valid M),List.singleton_append,ObservedScanner.consumed,hs] using hh

def headerEffects {n : Nat} (M : Machine n) (H : ScannerSummary n) (entry : Entry n) (P : List Nat) : List (List Nat) :=
  match entry with
  | .iterate _ _ | .aligned _ => profiles (observer M)
  | .scan q => H q
  | .shift q R => product [profile (observer M) ((R q).getD [])] [P]
  | .replay | .safeReplay => [P]
  | .alt a b => headerEffects M H a P ++ headerEffects M H b P
  | .guard _ _ b => headerEffects M H b P

def scopeCheck (bodies : List Arg) : Arg → Bool
  | .user i a => decide (i<bodies.length) && scopeCheck bodies a
  | .seq a b | .alt a b => scopeCheck bodies a && scopeCheck bodies b
  | .notP a | .star a => scopeCheck bodies a
  | _ => true

theorem scope_sound (bodies : List Arg) : ∀ e, scopeCheck bodies e=true → Scoped bodies e
  | .user i a,h => ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,scope_sound bodies a (Bool.and_eq_true_iff.mp h).2⟩
  | .seq a b,h | .alt a b,h => ⟨scope_sound bodies a (Bool.and_eq_true_iff.mp h).1,scope_sound bodies b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h | .star a,h => scope_sound bodies a h
  | .lit _,_ | .param _,_ => True.intro

/-- This is a finite check of actual rule syntax and finite profile sets.
No recursive-row result or successful capture is supplied as a certificate. -/
def grammarCheck {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) : Bool :=
  bodies.zipIdx.all (fun (b,i) => scopeCheck bodies b &&
    (profiles (observer M)).all (fun P =>
      (product (headerEffects M H (entries i) P) (effects M C [P] b)).all (fun Q => (C i P).contains Q)))

theorem grammar_checked {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (hc : grammarCheck M entries bodies H C=true)
    (i : Nat) (b : Arg) (hi : bodies[i]?=some b) :
    Scoped bodies b ∧ ∀ P∈profiles (observer M),
      ∀ Q∈product (headerEffects M H (entries i) P) (effects M C [P] b), Q∈C i P := by
  have hm : (b,i)∈bodies.zipIdx := List.mem_of_getElem? (show bodies.zipIdx[i]?=some (b,i) from by
    simp [List.getElem?_zipIdx,hi])
  have hh := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hc) (b,i) hm)
  refine ⟨scope_sound bodies b hh.1,?_⟩
  intro P hP Q hQ
  exact List.contains_iff_mem.mp ((List.all_eq_true.mp ((List.all_eq_true.mp hh.2) P hP)) Q hQ)

theorem header_shape {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (hc : scannerCheck M H=true) (entry : Entry n)
    (x v : List Char) (k p q : Nat) (hp : p≤x.length)
    (h : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [v]
      (sourceHeader entry) p=some (some q)) :
    q≤p ∧ ∃ w, profile (observer M) w∈headerEffects M H entry (profile (observer M) v) ∧
      sfx x p=w++sfx x q := by
  induction entry with
  | replay | safeReplay =>
    have hl : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [v]
        (.lit v) p=some (some q) := by simpa only [sourceHeader,evV,List.getElem?_cons_zero] using h
    obtain ⟨hq,hs⟩ := literal_shape _ x .callByValuePar _ [v] v p q hp hl
    exact ⟨hq,v,by simp [headerEffects],hs⟩
  | iterate start R | aligned _ =>
    have hs := DependentCaptureFilter.success_prefix (by decide)
      (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
      [v] _ (sourceHeader_firstOrder _) p q hp h
    have hle : q≤p := by
      have hl := congrArg List.length hs.2
      rw [List.length_append,length_sfx x hp,length_sfx x hs.1] at hl
      omega
    exact ⟨hle,pre x p q,profile_mem _ (valid M) _,hs.2⟩
  | shift start R =>
    let u := (R start).getD []
    have he := WordArguments.word_eval (source M entries bodies) x .callByValuePar
      (sourceTable M entries bodies x k) [v] (.seq (.lit u) (.param 0)) ⟨True.intro,True.intro⟩ p
    have hl : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) []
        (.lit (u++v)) p=some (some q) := by
      simpa only [WordArguments.value,WordArguments.literal,List.getElem?_cons_zero,Option.bind_some,Option.map_some] using he.symm.trans h
    obtain ⟨hq,hs⟩ := literal_shape _ x .callByValuePar _ [] (u++v) p q hp hl
    exact ⟨hq,u++v,product_mem (observer M) (valid M) [profile (observer M) u]
      [profile (observer M) v] u v (by simp) (by simp),hs⟩
  | scan start =>
    rw [sourceHeader,RecursiveScannerProductHeader.source_scan M entries bodies start x k p [v] hp] at h
    have hq : (StatefulScanner.run M start (sfx x p)).2.length=q := by simpa only [Option.some.injEq] using h
    subst q
    have hh := RecursiveScannerProductHeader.source_scan_prefix M entries bodies start x k p [v] hp
    have hlen := StatefulScanner.run_length M start (sfx x p)
    rw [length_sfx x hp] at hlen
    refine ⟨hlen,pre x p _,?_,hh.2⟩
    rw [ObservedScanner.consumed_pre M start x p hp]
    exact scanner_profiles M H hc start (sfx x p)
  | alt a b ha hb =>
    cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [v] (sourceHeader a) p with
    | none => simp [sourceHeader,evV,hv] at h
    | some result => cases result with
      | none =>
        have hh : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [v] (sourceHeader b) p=some (some q) := by
          simpa only [sourceHeader,evV,hv] using h
        obtain ⟨hq,w,hw,hs⟩ := hb hh
        exact ⟨hq,w,List.mem_append_right _ hw,hs⟩
      | some z =>
        have hz : z=q := by simpa only [sourceHeader,evV,hv,Option.some.injEq] using h
        subst z
        obtain ⟨hq,w,hw,hs⟩ := ha hv
        exact ⟨hq,w,List.mem_append_left _ hw,hs⟩
  | guard positive a b ha hb =>
    have hh : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [v] (sourceHeader b) p=some (some q) := by
      cases positive <;>
        cases hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [v] (sourceHeader a) p with
        | none => simp [sourceHeader,MExp.andP,evV,hv] at h
        | some result => cases result <;> simp [sourceHeader,MExp.andP,evV,hv] at h <;> exact h
    exact hb hh

theorem frozen_rows {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (hH : scannerCheck M H=true)
    (hC : grammarCheck M entries bodies H C=true) (x : List Char) (k : Nat) :
    Rows M bodies C x (sourceTable M entries bodies x k) := by
  induction k with
  | zero =>
    intro i b hi v p q hp h
    rw [RecursiveScannerProductCorrespondence.source_zero] at h
    cases h
  | succ k ih =>
    intro i b hi v p q hp h
    have hc := grammar_checked M entries bodies H C hC i b hi
    rw [RecursiveScannerProductCorrespondence.source_step M entries bodies x k i b hi [v] p hp] at h
    cases hh : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) [v]
        (sourceHeader (entries i)) p with
    | none => rw [evV_seq_none hh] at h; cases h
    | some result => cases result with
      | none => rw [evV_seq_fail hh] at h; cases h
      | some j =>
        rw [evV_seq_ok hh] at h
        obtain ⟨hjp,u,hu,hs⟩ := header_shape M entries bodies H hH (entries i) x v k p j hp hh
        obtain ⟨hqj,w,hw,ht⟩ := output_shape M entries bodies C x _ ih
          [profile (observer M) v] [v] (DependentCaptureFilter.environment_accurate _ [v])
          b hc.1 j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++w,
          hc.2 _ (profile_mem _ (valid M) v) _ (product_mem _ (valid M) _ _ u w hu hw),
          by rw [hs,ht,List.append_assoc]⟩

/-- Actual new argument captures have one of the checked finite profiles,
even through mutually recursive parameterized calls and arbitrary stars. -/
theorem capture {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (hH : scannerCheck M H=true)
    (hC : grammarCheck M entries bodies H C=true) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (e : Arg) (he : scopeCheck bodies e=true) (p q : Nat) (hp : p≤x.length)
    (h : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E
      (sourceExpr M e) p=some (some q)) :
    profile (observer M) (pre x p q)∈effects M C S e ∧ sfx x p=pre x p q++sfx x q := by
  obtain ⟨hqp,w,hw,hs⟩ := output_shape M entries bodies C x _
    (frozen_rows M entries bodies H C hH hC x k) S E hS e (scope_sound bodies e he) p q hp h
  have hpre : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using pre_eq (sfx_is_suffix x p) hs
  exact ⟨hpre.symm ▸ hw,by rw [hpre]; exact hs⟩

/-- State-specific scanner arguments are certified from the finite source
checks and abstract output sets, rather than all-state totality. -/
theorem capture_frontier {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (H : ScannerSummary n) (C : Summary) (hH : scannerCheck M H=true)
    (hC : grammarCheck M entries bodies H C=true) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (e : Arg) (he : scopeCheck bodies e=true) (q : Fin n)
    (hc : (effects M C S e).all (fun P => ScannerFrontierCertificate.check P q)=true)
    (p j : Nat) (hp : p≤x.length)
    (h : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E
      (sourceExpr M e) p=some (some j)) : StatefulScanner.advance M q (pre x p j)≠none :=
  (ScannerFrontierCertificate.check_actual M _ q).mp
    ((List.all_eq_true.mp hc) _ (capture M entries bodies H C hH hC x k S E hS e he p j hp h).1)

end Shallot.MacroPeg.CBV.RecursiveCaptureProfiles
