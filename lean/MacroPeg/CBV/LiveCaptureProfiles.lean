import MacroPeg.CBV.LiveCaptureQuotient

namespace Shallot.MacroPeg.CBV.LiveCaptureProfiles

open LiveCaptureQuotient (visible profile)

def value (i j : Nat) : List Char := List.replicate i 'a' ++ List.replicate j 'b'
def input (n : Nat) : List Char := value n n
def words (n : Nat) : List (List Char) :=
  (List.range (n+1)).flatMap (fun i => (List.range (n+1)).map (value i))

def representatives (n : Nat) : List (Option (List Char)) := none :: (words n).map some

theorem value_injective {i j i' j' : Nat} (h : value i j=value i' j') : i=i' ∧ j=j' := by
  have ha := congrArg (List.count 'a') h
  have hb := congrArg (List.count 'b') h
  simpa [value,List.count_replicate] using And.intro ha hb

theorem word_mem (n : Nat) (w : List Char) : w∈words n ↔
    ∃ i j, i≤n ∧ j≤n ∧ value i j=w := by
  simp only [words,List.mem_flatMap,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,j,hj,he⟩; exact ⟨i,j,by omega,by omega,he⟩
  · rintro ⟨i,j,hi,hj,he⟩; exact ⟨i,by omega,j,by omega,he⟩

private theorem visible_of_split {x lead w trail : List Char} (hx : x=lead++(w++trail)) :
    visible x w=true := by
  apply (LiveCaptureQuotient.visible_iff x w).mpr
  refine ⟨(w++trail).length, ?_, ?_⟩
  · have hh := congrArg List.length hx
    simp only [List.length_append] at hh ⊢
    omega
  · rw [sfx_suffix hx]
    have hs : Shallot.stripPrefix? w (w++trail)=some trail :=
      (CBVtoCBN.stripPrefix_exact _ _ _).mpr rfl
    simp [hs]

theorem values_visible {n i j : Nat} (hi : i≤n) (hj : j≤n) : visible (input n) (value i j)=true := by
  apply visible_of_split (lead := List.replicate (n-i) 'a') (trail := List.replicate (n-j) 'b')
  have ha : List.replicate (n-i) 'a' ++ List.replicate i 'a' = List.replicate n 'a' := by
    rw [List.replicate_append_replicate,show n-i+i=n by omega]
  have hb : List.replicate j 'b' ++ List.replicate (n-j) 'b' = List.replicate n 'b' := by
    rw [List.replicate_append_replicate,show j+(n-j)=n by omega]
  simp only [input,value]
  rw [← ha,← hb]
  simp only [List.append_assoc]

theorem visible_iff_word_mem (n : Nat) (w : List Char) : visible (input n) w=true ↔ w∈words n := by
  constructor
  · intro hv
    obtain ⟨p,hp,hmatch⟩ := (LiveCaptureQuotient.visible_iff (input n) w).mp hv
    cases hs : Shallot.stripPrefix? w (sfx (input n) p) with
    | none => simp [hs] at hmatch
    | some trail =>
      have he := (CBVtoCBN.stripPrefix_exact _ _ _).mp hs
      have hw : w = (sfx (input n) p).take w.length := by rw [he]; simp
      have hshape : sfx (input n) p =
          List.replicate (n-((input n).length-p)) 'a' ++
            List.replicate (n-((input n).length-p-n)) 'b' := by
        simp [sfx,input,value,List.drop_append]
      rw [hshape,List.take_append,List.take_replicate,List.take_replicate] at hw
      apply (word_mem n w).mpr
      refine ⟨_,_,?_,?_,hw.symm⟩
      · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.sub_le _ _)
      · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.sub_le _ _)
  · intro hw
    obtain ⟨i,j,hi,hj,rfl⟩ := (word_mem n w).mp hw
    exact values_visible hi hj

theorem words_nodup (n : Nat) : (words n).Nodup := by
  unfold words
  apply List.pairwise_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro i hi
    exact List.Pairwise.map (R := fun a b : Nat => a≠b) _
      (fun a b hab he => hab (value_injective he).2) List.nodup_range
  · apply List.nodup_range.imp
    intro i j hij u hu v hv he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
    exact hij (value_injective he).1

theorem words_length (n : Nat) : (words n).length = (n+1)*(n+1) := by
  simp [words,List.length_flatMap,List.map_const',List.sum_replicate_nat]

theorem representatives_nodup (n : Nat) : (representatives n).Nodup := by
  simp only [representatives,List.nodup_cons]
  refine ⟨by simp, ?_⟩
  exact List.Pairwise.map some (fun a b hab he => hab (Option.some.inj he)) (words_nodup n)

theorem representatives_length (n : Nat) :
    (representatives n).length = (n+1)*(n+1)+1 := by simp [representatives,words_length]

theorem profile_complete (n : Nat) (v : Option (List Char)) :
    profile (input n) v ∈ representatives n := by
  cases hp : profile (input n) v with
  | none => simp [representatives]
  | some w =>
    have hv := (LiveCaptureQuotient.profile_some _ _ _).mp hp
    have hw := (visible_iff_word_mem n w).mp hv.2
    simp [representatives,hw]

theorem representative_fixed (n : Nat) : ∀ v∈representatives n,
    profile (input n) v=v := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rfl
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact (LiveCaptureQuotient.profile_some _ _ _).mpr ⟨rfl,(visible_iff_word_mem n w).mpr hw⟩

theorem dead_representative (n : Nat) : profile (input n) (some ['c'])=none := by
  apply LiveCaptureQuotient.profile_dead
  apply CaptureObservability.absent_character
  simp [input,value]

theorem distinct_contexts {g : MGrammar} {s : Strategy} (hg : g.FirstOrder) (hs : s≠.callByName)
    {n i j i' j' : Nat} (hi : i≤n) (hj : j≤n) (_hi' : i'≤n) (_hj' : j'≤n)
    (hd : i≠i' ∨ j≠j') :
    ¬ (∀ e : MExp, e.FirstOrder →
      (SObs g s (MExp.subst [MExp.lit (value i j)] e) (input n) (some []) ↔
        SObs g s (MExp.subst [MExp.lit (value i' j')] e) (input n) (some []))) := by
  intro h
  have hp := (LiveCaptureQuotient.observations_contexts_iff hg hs [value i j] [value i' j']).mp h
  have hzero := hp 0
  simp only [List.getElem?_cons_zero] at hzero
  have he := LiveCaptureQuotient.live_injective (values_visible hi hj) hzero
  have heq := value_injective he
  exact hd.elim (fun h => h heq.1) (fun h => h heq.2)

end Shallot.MacroPeg.CBV.LiveCaptureProfiles
