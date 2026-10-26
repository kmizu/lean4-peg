import MacroPeg.CBV.SequentialTupleKeys
import MacroPeg.CBV.LiveCaptureQuotient

/-! Adjacency alone cannot bound a table of all admissible capture profiles
by a polynomial degree independent of arity. This is a representation-family
count, not a time lower bound for recognizing any language. The candidate
actuals/callers may vary; no fixed-source trace claim is made. -/
namespace Shallot.MacroPeg.CBV.SequentialAdjacentProfiles

open SequentialSpanRecompute (decodeEnv)

def word (n : Nat) : List Char := List.replicate n 'a'
def bound (r n : Nat) : Nat := (r+1)*n
def input (r n : Nat) : List Char := word (2*(r+1)*n)

def spans (b : Nat) : List Nat → SequentialSpanRecompute.Env
  | [] => []
  | d::ds => (b+d+ds.sum,b+ds.sum)::spans b ds

theorem spans_window (b : Nat) (ds : List Nat) :
    SequentialCaptureRegions.Window (b+ds.sum) b (spans b ds) := by
  induction ds with
  | nil => simpa [spans] using SequentialCaptureRegions.Window.nil b
  | cons d ds ih =>
    simpa [spans,List.sum_cons,Nat.add_assoc] using
      (SequentialCaptureRegions.Window.cons (p := b+d+ds.sum) (by omega) ih)

private theorem sum_bound {n : Nat} (ds : List Nat) (hb : ∀ d∈ds,d≤n) :
    ds.sum ≤ ds.length*n := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := hb d (by simp)
    have ht := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
    simp only [List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

private theorem pre_word {N a b : Nat} (ha : a≤N) :
    pre (word N) a b = word (a-b) := by
  simp [pre,sfx,word,List.drop_replicate,List.take_replicate,
    show N-(N-a)=a by omega,Nat.min_eq_left (Nat.sub_le _ _)]

theorem spans_decode (N b : Nat) (ds : List Nat) (hb : b+ds.sum≤N) :
    decodeEnv (word N) (spans b ds) = ds.map word := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.sum_cons] at hb
    simp only [spans,decodeEnv,List.map_cons]
    rw [pre_word (by omega),show b+d+ds.sum-(b+ds.sum)=d by omega]
    exact congrArg (List.cons (word d)) (ih (by omega))

/-- These are actual Seq argument captures, not merely arbitrary span lists.
The finite literal argument list varies with the candidate environment. -/
theorem literal_actuals (g : MGrammar) (T : SequentialClock.Table) (E : List (List Char))
    (N b : Nat) : ∀ ds : List Nat, b+ds.sum≤N →
      evSeqArgs g (word N) .callByValueSeq T E (ds.map (fun d => MExp.lit (word d)))
        (b+ds.sum) = some (some (ds.map word,b))
  | [],_ => rfl
  | d::ds,hb => by
    have hfx : sfx (word N) (b+(d::ds).sum) = word (b+(d::ds).sum) := by
      simp only [sfx,word,List.length_replicate,List.drop_replicate]
      congr 1
      omega
    have hs : Shallot.stripPrefix? (word d) (word (b+(d::ds).sum)) =
        some (word (b+ds.sum)) := by
      apply (CBVtoCBN.stripPrefix_exact _ _ _).mpr
      simp [word,List.sum_cons,Nat.add_left_comm]
    have hh : evV g (word N) .callByValueSeq T E (.lit (word d)) (b+(d::ds).sum) =
        some (some (b+ds.sum)) := by
      simp only [evV]
      rw [hfx,hs]
      simp [word]
    rw [List.map_cons,evSeqArgs,hh]
    simp only []
    rw [literal_actuals g T E N b ds (by simp only [List.sum_cons] at hb; omega)]
    simp only []
    rw [pre_word hb]
    simp [List.sum_cons,show b+(d+ds.sum)-(b+ds.sum)=d by omega]

def profile (ds : List Nat) : List (Option (List Char)) := ds.map (fun d => some (word d))

theorem profile_injective {ds es : List Nat} (he : profile ds=profile es) : ds=es := by
  have h := congrArg (List.map (fun w : Option (List Char) => (w.getD []).length)) he
  simpa [profile,word,List.map_map,Function.comp_def] using h

private theorem live_word {N d : Nat} (hd : d≤N) :
    LiveCaptureQuotient.profile (word N) (some (word d)) = some (word d) := by
  have hv : LiveCaptureQuotient.visible (word N) (word d) = true := by
    apply (LiveCaptureQuotient.visible_iff _ _).mpr
    refine ⟨N,by simp [word],?_⟩
    have hfx : sfx (word N) N=word N := by simpa [word] using (sfx_self (word N))
    rw [hfx]
    have hs : Shallot.stripPrefix? (word d) (word N) = some (word (N-d)) := by
      apply (CBVtoCBN.stripPrefix_exact _ _ _).mpr
      simp [word,show d+(N-d)=N by omega]
    simp [hs]
  simp [LiveCaptureQuotient.profile,hv]

/-- Every candidate is a genuinely adjacent past environment on one input,
and every field remains replayable in its common remaining suffix. -/
theorem window_profile {r n : Nat} {ds : List Nat}
    (hd : ds∈SequentialTupleKeys.paths n r) :
    SequentialCaptureRegions.Window (bound r n+ds.sum) (bound r n) (spans (bound r n) ds) ∧
    ((decodeEnv (input r n) (spans (bound r n) ds)).map
      (fun w => LiveCaptureQuotient.profile (sfx (input r n) (bound r n)) (some w))) = profile ds := by
  have hb := (SequentialTupleKeys.mem_paths n r ds).mp hd
  have hs := sum_bound ds hb.2
  rw [hb.1] at hs
  have hlen : bound r n+ds.sum ≤ 2*(r+1)*n := by
    unfold bound
    have hmul := Nat.mul_le_mul_right n (show r≤r+1 by omega)
    have he : 2*(r+1)*n = (r+1)*n+(r+1)*n := by rw [Nat.two_mul,Nat.add_mul]
    omega
  refine ⟨spans_window _ _,?_⟩
  have hbound : bound r n ≤ 2*(r+1)*n := by omega
  rw [input,spans_decode _ _ _ hlen]
  have hfx : sfx (word (2*(r+1)*n)) (bound r n) = word (bound r n) := by
    simp [sfx,word,List.drop_replicate,show 2*(r+1)*n-(2*(r+1)*n-bound r n)=bound r n by omega]
  rw [hfx]
  simp only [List.map_map,profile]
  apply List.map_congr_left
  intro d hd
  apply live_word
  exact Nat.le_trans (hb.2 d hd) (by unfold bound; rw [Nat.succ_mul]; omega)

private theorem paths_nodup (n r : Nat) : (SequentialTupleKeys.paths n r).Nodup := by
  induction r with
  | zero => simp [SequentialTupleKeys.paths]
  | succ r ih =>
    rw [SequentialTupleKeys.paths]
    apply List.pairwise_flatMap.mpr
    refine ⟨?_,?_⟩
    · intro j hj
      exact List.Pairwise.map (R := fun a b => a≠b) _
        (fun _ _ hab he => hab (List.cons.inj he).2) ih
    · apply List.nodup_range.imp
      intro i j hij u hu v hv he
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
      exact hij (List.cons.inj he).1

def candidates (r n : Nat) : List (List (Option (List Char))) :=
  (SequentialTupleKeys.paths n r).map profile

theorem candidates_nodup (r n : Nat) : (candidates r n).Nodup :=
  List.Pairwise.map (R := fun a b => a≠b) _
    (fun _ _ hab he => hab (profile_injective he)) (paths_nodup n r)

theorem candidates_count (r n : Nat) : (candidates r n).length=(n+1)^r := by
  simp [candidates,SequentialTupleKeys.paths_length]

/-- Even after imposing adjacency and retaining only live values, enumerating
all admissible profiles has no arity-independent polynomial degree. This
neither forces a recognizer to enumerate them nor excludes compact indices. -/
theorem no_uniform_enumeration_degree (d : Nat) :
    ∃ r, ∀ C : Nat, ∃ n, C*((input r n).length+1)^d < (candidates r n).length := by
  refine ⟨d+1,?_⟩
  intro C
  let B := 2*(d+2)+1
  let n := C*B^d+1
  refine ⟨n,?_⟩
  have hn : 0<n := by dsimp [n]; omega
  have hinput : (input (d+1) n).length+1 ≤ B*n := by
    simp only [input,word,List.length_replicate,Nat.add_assoc]
    dsimp [B]
    rw [Nat.add_mul]
    omega
  rw [candidates_count]
  calc
    C*((input (d+1) n).length+1)^d ≤ C*(B*n)^d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hinput d)
    _ = (C*B^d)*n^d := by rw [Nat.mul_pow,Nat.mul_assoc]
    _ < n*n^d := Nat.mul_lt_mul_of_pos_right (by dsimp [n]; omega) (Nat.pow_pos hn)
    _ = n^(d+1) := by rw [Nat.pow_succ,Nat.mul_comm]
    _ ≤ (n+1)^(d+1) := Nat.pow_le_pow_left (by omega) _

end Shallot.MacroPeg.CBV.SequentialAdjacentProfiles
