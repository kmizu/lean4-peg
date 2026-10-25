import MacroPeg.CBV.DelimiterTemplate

namespace Shallot.MacroPeg.CBV.DelimitedCopyTemplates
open DelimiterTemplate DelimitedCopyProjection

theorem take_free (d : Char) : ∀ x : List Char, Free d (x.takeWhile (pred d))
  | [] => by simp [Free]
  | c::x => by
    by_cases hc : c=d
    · subst c; simp [pred,Free]
    · simpa [pred,hc,Free] using And.intro (Ne.symm hc) (take_free d x)

theorem drop_free (d : Char) : ∀ h : List Char, Free d h → ∀ tail,
    (h++d::tail).dropWhile (pred d)=d::tail
  | [],_,tail => by simp [pred]
  | c::h,hh,tail => by
    have hc : c≠d := fun he => hh (by simp [he])
    have ht : Free d h := fun hm => hh (by simp [hm])
    simpa [pred,hc] using drop_free d h ht tail

theorem drop_nil_iff (d : Char) : ∀ x : List Char, x.dropWhile (pred d)=[] ↔ Free d x
  | [] => by simp [Free]
  | c::x => by
    by_cases hc : c=d
    · subst c; simp [pred,Free]
    · simpa [pred,hc,Free,Ne.symm hc] using drop_nil_iff d x

theorem run_lit_iff (d : Char) (E : List (List Char)) (w : List Char) (ps : List Part) (x rest : List Char) :
    run d E (.lit w::ps) x=some rest ↔ ∃ y, x=w++y ∧ run d E ps y=some rest := by
  constructor
  · intro h
    cases hs : Shallot.stripPrefix? w x with
    | none => simp [run,action,hs] at h
    | some y => exact ⟨y,(CBVtoCBN.stripPrefix_exact _ _ _).mp hs,by simpa [run,action,hs] using h⟩
  · rintro ⟨y,he,hy⟩
    have hs := (CBVtoCBN.stripPrefix_exact w x y).mpr he
    simpa [run,action,hs] using hy

theorem run_gap_sep_iff (d : Char) (E : List (List Char)) (ps : List Part) (x rest : List Char) :
    run d E (.gap::.lit [d]::ps) x=some rest ↔
      ∃ h y, Free d h ∧ x=h++d::y ∧ run d E ps y=some rest := by
  constructor
  · intro h
    cases hs : Shallot.stripPrefix? [d] (x.dropWhile (pred d)) with
    | none => simp [run,action,hs] at h
    | some y =>
      refine ⟨x.takeWhile (pred d),y,take_free d x,?_,by simpa [run,action,hs] using h⟩
      have he := (CBVtoCBN.stripPrefix_exact [d] _ y).mp hs
      calc
        x = x.takeWhile (pred d)++x.dropWhile (pred d) := List.takeWhile_append_dropWhile.symm
        _ = x.takeWhile (pred d)++d::y := by rw [he]; rfl
  · rintro ⟨h,y,hh,hx,hy⟩
    rw [hx]
    simpa [run,action,drop_free d h hh y,Shallot.stripPrefix?,Shallot.beqChar] using hy

theorem run_eof_iff (d : Char) (E : List (List Char)) (x : List Char) : run d E [.eof] x=some [] ↔ x=[] := by
  by_cases hx : x=[] <;> simp [run,action,hx]

theorem run_gap_eof_iff (d : Char) (E : List (List Char)) (x : List Char) :
    run d E [.gap,.eof] x=some [] ↔ Free d x := by
  change run d E [.eof] (x.dropWhile (pred d))=some [] ↔ _
  rw [run_eof_iff,drop_nil_iff]

def sourceParts (d : Char) : List Part := [.param 1,.lit [d],.param 0,.lit [d],.param 1]
def shortParts (d : Char) : List Part := [.gap,.lit [d],.param 0,.lit [d],.gap]
def longParts (d : Char) : List Part := [.lit [d],.gap,.lit [d],.param 0]

theorem source_accept (d : Char) (u v x : List Char) :
    Accept d [u,v] (sourceParts d) x ↔ x=v++d::(u++d::v) := by
  change run d [u,v] [.lit v,.lit [d],.lit u,.lit [d],.lit v,.eof] x=some [] ↔ _
  simp only [run_lit_iff,run_eof_iff]
  simp [List.append_assoc]

theorem short_accept (d : Char) (u x : List Char) :
    Accept d [u] (shortParts d) x ↔ shortPass d u x := by
  change run d [u] [.gap,.lit [d],.lit u,.lit [d],.gap,.eof] x=some [] ↔ _
  simp only [run_gap_sep_iff,run_lit_iff,run_gap_eof_iff]
  simp [shortPass]
  constructor
  · rintro ⟨h,hh,y,hx,z,hy,t,hz,ht⟩
    exact ⟨h,hh,t,ht,by rw [hx,hy,hz]⟩
  · rintro ⟨h,hh,t,ht,hx⟩
    exact ⟨h,hh,u++d::t,hx,d::t,rfl,t,rfl,ht⟩

theorem long_accept (d : Char) (v x : List Char) :
    Accept d [v] (longParts d) x ↔ longPass d v x := by
  change run d [v] [.lit [d],.gap,.lit [d],.lit v,.eof] x=some [] ↔ _
  simp only [run_gap_sep_iff,run_lit_iff,run_eof_iff]
  simp [longPass]
  constructor
  · rintro ⟨y,hx,h,hh,hy⟩
    exact ⟨h,hh,by rw [hx,hy]⟩
  · rintro ⟨h,hh,hx⟩
    exact ⟨h++d::v,hx,h,hh,rfl⟩

/-- Exact equivalence of the real pure source body and the two generated
unary bodies on physical captured prefixes. Both values may be unbounded. -/
theorem accepts_iff (d : Char) (x u v a b : List Char)
    (hu : Free d u) (hv : Free d v) (ha : x=u++a) (hb : x=v++b) :
    Accept d [u,v] (sourceParts d) x ↔ Accept d [u] (shortParts d) a ∧ Accept d [v] (longParts d) b := by
  rw [source_accept,short_accept,long_accept]
  exact (projections_iff d x u v a b hu hv ha hb).symm


def sourceBlockParts (d : Char) : List Part := [.param 1,.lit [d],.param 0,.lit [d],.param 1,.lit [d]]
def shortBlockParts (d : Char) : List Part := [.gap,.lit [d],.param 0,.lit [d],.gap,.lit [d]]
def longBlockParts (d : Char) : List Part := [.lit [d],.gap,.lit [d],.param 0,.lit [d]]

theorem run_nil_iff (d : Char) (E : List (List Char)) (x rest : List Char) : run d E [] x=some rest ↔ x=rest := by simp [run]

theorem source_block (d : Char) (u v x rest : List Char) :
    run d [u,v] (sourceBlockParts d) x=some rest ↔ x=v++d::(u++d::(v++d::rest)) := by
  change run d [u,v] [.lit v,.lit [d],.lit u,.lit [d],.lit v,.lit [d]] x=some rest ↔ _
  simp only [run_lit_iff,run_nil_iff]
  simp [List.append_assoc]

theorem short_block (d : Char) (u x rest : List Char) :
    run d [u] (shortBlockParts d) x=some rest ↔ shortBlock d u x rest := by
  change run d [u] [.gap,.lit [d],.lit u,.lit [d],.gap,.lit [d]] x=some rest ↔ _
  simp only [run_gap_sep_iff,run_lit_iff,run_nil_iff]
  simp [shortBlock]
  constructor
  · rintro ⟨h,hh,y,hx,z,hy,t,hzt,g,hg,ht⟩
    exact ⟨h,hh,g,hg,by rw [hx,hy,hzt,ht]⟩
  · rintro ⟨h,hh,t,ht,hx⟩
    exact ⟨h,hh,u++d::(t++d::rest),hx,d::(t++d::rest),rfl,t++d::rest,rfl,t,ht,rfl⟩

theorem long_block (d : Char) (v x rest : List Char) :
    run d [v] (longBlockParts d) x=some rest ↔ longBlock d v x rest := by
  change run d [v] [.lit [d],.gap,.lit [d],.lit v,.lit [d]] x=some rest ↔ _
  simp only [run_gap_sep_iff,run_lit_iff,run_nil_iff]
  simp [longBlock]
  constructor
  · rintro ⟨y,hx,h,hh,hy⟩
    exact ⟨h,hh,by rw [hx,hy]⟩
  · rintro ⟨h,hh,hx⟩
    exact ⟨h++d::(v++d::rest),hx,h,hh,rfl⟩

/-- Equality of real partial suffix transformations, including the suffix
returned after the copy block, with both source captures unbounded. -/
theorem block_run_eq (d : Char) (x u v a b : List Char)
    (hu : Free d u) (hv : Free d v) (ha : x=u++a) (hb : x=v++b) :
    run d [u,v] (sourceBlockParts d) x=
      (run d [u] (shortBlockParts d) a).bind (fun _ => run d [v] (longBlockParts d) b) := by
  have he (rest : List Char) : run d [u,v] (sourceBlockParts d) x=some rest ↔
      (run d [u] (shortBlockParts d) a).bind (fun _ => run d [v] (longBlockParts d) b)=some rest := by
    rw [source_block,block_projections_iff d x u v a b rest hu hv ha hb]
    cases hs : run d [u] (shortBlockParts d) a with
    | none => simp [←short_block,hs]
    | some s => simp [←short_block,←long_block,hs]
  cases hleft : run d [u,v] (sourceBlockParts d) x with
  | some rest => exact ((he rest).mp hleft).symm
  | none =>
    cases hright : (run d [u] (shortBlockParts d) a).bind (fun _ => run d [v] (longBlockParts d) b) with
    | none => rfl
    | some rest => have hh := (he rest).mpr hright; rw [hleft] at hh; cases hh

end Shallot.MacroPeg.CBV.DelimitedCopyTemplates
