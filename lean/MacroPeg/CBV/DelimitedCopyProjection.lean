import MacroPeg.CBV.RetainedViewFusionCompiler

/-! Two overlapping unbounded captures can be checked by separate original-
origin projections in a delimiter-separated copy layout. This does not
construct a residual parser from either opaque captured word. -/
namespace Shallot.MacroPeg.CBV.DelimitedCopyProjection

def Free (d : Char) (w : List Char) : Prop := d∉w

theorem split_unique (d : Char) : ∀ a b tail rest : List Char,
    Free d a → Free d b → a++d::tail=b++d::rest → a=b ∧ tail=rest
  | [],[],tail,rest,_,_,he => by simpa using he
  | [],c::b,tail,rest,_,hb,he => by
    have hc : c=d := (List.cons.inj he).1.symm
    exact False.elim (hb (by simp [hc]))
  | c::a,[],tail,rest,ha,_,he => by
    have hc : c=d := (List.cons.inj he).1
    exact False.elim (ha (by simp [hc]))
  | c::a,e::b,tail,rest,ha,hb,he => by
    have hc : c=e := (List.cons.inj he).1
    subst e
    obtain ⟨rfl,ht⟩ := split_unique d a b tail rest (fun h => ha (by simp [h])) (fun h => hb (by simp [h])) (List.cons.inj he).2
    exact ⟨rfl,ht⟩

/-- A delimiter-free prefix cannot cross the first delimiter. -/
theorem prefix_before (d : Char) : ∀ u v tail : List Char,
    Free d u → u.IsPrefix (v++d::tail) → u.IsPrefix v
  | [],v,tail,_,_ => List.nil_prefix
  | c::u,[],tail,hu,hp => by
    have hc : c=d := ((List.cons_prefix_cons).mp hp).1
    exact False.elim (hu (by simp [hc]))
  | c::u,e::v,tail,hu,hp => by
    obtain ⟨hc,ht⟩ := (List.cons_prefix_cons).mp hp
    subst e
    exact List.cons_prefix_cons.mpr ⟨rfl,prefix_before d u v tail (fun h => hu (by simp [h])) ht⟩

def shortPass (d : Char) (u rest : List Char) : Prop :=
  ∃ h z, Free d h ∧ Free d z ∧ rest=h++d::(u++d::z)
def longPass (d : Char) (v rest : List Char) : Prop :=
  ∃ t, Free d t ∧ rest=d::(t++d::v)

/-- Both projections start from the original input. The short projection
skips the unmatched part of the long first word, preserving no residual
continuation or finite summary of that prefix. -/
theorem projections_iff (d : Char) (x u v a b : List Char)
    (hu : Free d u) (hv : Free d v) (ha : x=u++a) (hb : x=v++b) :
    shortPass d u a ∧ longPass d v b ↔ x=v++d::(u++d::v) := by
  constructor
  · rintro ⟨⟨h,z,hh,hz,he⟩,⟨t,ht,he'⟩⟩
    have hx : (u++h)++d::(u++d::z)=v++d::(t++d::v) := by
      calc
        (u++h)++d::(u++d::z) = u++a := by rw [he]; simp [List.append_assoc]
        _ = v++b := ha.symm.trans hb
        _ = v++d::(t++d::v) := by rw [he']
    obtain ⟨_,hc⟩ := split_unique d (u++h) v _ _ (by simpa [Free,List.mem_append] using And.intro hu hh) hv hx
    obtain ⟨hut,_⟩ := split_unique d u t z v hu ht hc
    rw [hb,he',←hut]
  · intro hx
    have hp : u.IsPrefix (v++d::(u++d::v)) := ⟨a,ha.symm.trans hx⟩
    obtain ⟨h,he⟩ := prefix_before d u v _ hu hp
    have hh : Free d h := by
      intro hm
      apply hv
      rw [←he]
      simp [hm]
    have heA : a=h++d::(u++d::v) := by
      apply List.append_cancel_left (as := u)
      calc
        u++a = x := ha.symm
        _ = v++d::(u++d::v) := hx
        _ = u++(h++d::(u++d::v)) := by rw [←he]; simp [List.append_assoc]
    have heB : b=d::(u++d::v) := List.append_cancel_left (hb.symm.trans hx)
    exact ⟨⟨h,v,hh,hv,heA⟩,⟨u,hu,heB⟩⟩


def shortBlock (d : Char) (u a rest : List Char) : Prop :=
  ∃ h z, Free d h ∧ Free d z ∧ a=h++d::(u++d::(z++d::rest))
def longBlock (d : Char) (v b rest : List Char) : Prop :=
  ∃ t, Free d t ∧ b=d::(t++d::(v++d::rest))

/-- The projections also preserve the actual continuation after a final
separator; independent successful passes cannot choose different endpoints. -/
theorem block_projections_iff (d : Char) (x u v a b rest : List Char)
    (hu : Free d u) (hv : Free d v) (ha : x=u++a) (hb : x=v++b) :
    x=v++d::(u++d::(v++d::rest)) ↔ ∃ shortRest, shortBlock d u a shortRest ∧ longBlock d v b rest := by
  constructor
  · intro hx
    have hp : u.IsPrefix (v++d::(u++d::(v++d::rest))) := ⟨a,ha.symm.trans hx⟩
    obtain ⟨h,he⟩ := prefix_before d u v _ hu hp
    have hh : Free d h := by intro hm; apply hv; rw [←he]; simp [hm]
    have heA : a=h++d::(u++d::(v++d::rest)) := by
      apply List.append_cancel_left (as := u)
      calc
        u++a = x := ha.symm
        _ = v++d::(u++d::(v++d::rest)) := hx
        _ = u++(h++d::(u++d::(v++d::rest))) := by rw [←he]; simp [List.append_assoc]
    have heB : b=d::(u++d::(v++d::rest)) := List.append_cancel_left (hb.symm.trans hx)
    exact ⟨rest,⟨h,v,hh,hv,heA⟩,⟨u,hu,heB⟩⟩
  · rintro ⟨shortRest,⟨h,z,hh,hz,heA⟩,⟨t,ht,heB⟩⟩
    have he : (u++h)++d::(u++d::(z++d::shortRest))=v++d::(t++d::(v++d::rest)) := by
      calc
        (u++h)++d::(u++d::(z++d::shortRest)) = u++a := by rw [heA]; simp [List.append_assoc]
        _ = v++b := ha.symm.trans hb
        _ = v++d::(t++d::(v++d::rest)) := by rw [heB]
    obtain ⟨_,he'⟩ := split_unique d (u++h) v _ _ (by simpa [Free,List.mem_append] using And.intro hu hh) hv he
    obtain ⟨hut,he''⟩ := split_unique d u t _ _ hu ht he'
    obtain ⟨hzv,_⟩ := split_unique d z v _ _ hz hv he''
    rw [hb,heB,←hut]

end Shallot.MacroPeg.CBV.DelimitedCopyProjection
