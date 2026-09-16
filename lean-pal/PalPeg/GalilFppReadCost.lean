import PalPeg.GalilFppReadInstances
import PalPeg.GalilFppLazyForward

set_option autoImplicit false
namespace PalPeg.GalilFppReadCost
open GalilFppInstruction GalilFppCode GalilFppMaterialize GalilFppReadInstances
open GalilFppCopyInstances (renameInstruction renameConfig steps_rename)

theorem dequeue_all_cost (j : Fin 6) (b : Fin 2) (rest : List (Fin 2)) (x : Config)
    (hp : x.pc = entry j) (hc : x.tape 2 (x.pos 2) = 6) (hq : QueueAt x (b :: rest)) :
    ∃ y qs, Steps code x qs y ∧ y.pc = resultPC j b ∧ y.pos 2 = x.pos 2 ∧
      y.tape 2 (x.pos 2) = bitSymbol b ∧ QueueAt y rest ∧
      y.tape 2 = Function.update (x.tape 2) (x.pos 2) (bitSymbol b) ∧
      (∀ t, t ≠ 2 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      qs.length + 5*y.pos 5 ≤ 7 + 5*x.pos 5 := by
  let x₀ : Config := {x with pc := 26}
  obtain ⟨y,qs,hs,hpc,hpos,hcell,hyq,hframe,hin,hcost⟩ := dequeue_cost b rest x₀ rfl hc hq
  have hm : ∀ q ∈ qs, code[renamePC j q]? = (code[q]?).map (renameInstruction (renamePC j)) := by
    intro q hq
    have hb := of_decide_eq_true (List.all_eq_true.mp hin q hq)
    have hh := instances_match j ⟨q-10,by omega⟩
    have he : q-10+10 = q := by omega
    simpa only [he] using hh
  have hr := steps_rename (renamePC j) hs hm
  have hx : renameConfig (renamePC j) x₀ = x := by
    cases x
    simp_all [renameConfig,renamePC,entry,x₀]
  rw [hx] at hr
  refine ⟨renameConfig (renamePC j) y,qs.map (renamePC j),hr,?_,hpos,hcell,hyq,hframe,?_,?_⟩
  · change renamePC j y.pc = resultPC j b
    rw [hpc]
    fin_cases b <;> simp [destination,renamePC,resultPC]
  · intro t h₂ h₅ h₆
    exact region_frame hs hin t h₂ h₅ h₆
  · simpa [renameConfig,x₀] using hcost

theorem forward_blank_cost (b : Fin 2) (rest : List (Fin 2)) (x : Config)
    (hp : x.pc = 39) (hc : x.tape 2 (x.pos 2) = 6) (hq : QueueAt x (b :: rest)) :
    ∃ y qs, Steps code x qs y ∧ y.pc = (if b = 0 then 38 else 42) ∧ y.pos 2 = x.pos 2 ∧
      y.tape 2 (x.pos 2) = bitSymbol b ∧ QueueAt y rest ∧
      y.tape 2 = Function.update (x.tape 2) (x.pos 2) (bitSymbol b) ∧
      (∀ t, t ≠ 2 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      qs.length + 5*y.pos 5 ≤ 8 + 5*x.pos 5 := by
  let u : Config := {x with pc := 59}
  have hi : code[x.pc]? = some (.read 2 [(7,59),(8,59),(6,59)]) := by rw [hp]; rfl
  have he : Execute (.read 2 [(7,59),(8,59),(6,59)]) x u := .read _ _ _ _ (by simp [hc])
  obtain ⟨y,qs,hs,hpc,hpos,hcell,hyq,hframe,hother,hcost⟩ := dequeue_all_cost 1 b rest u rfl hc hq
  refine ⟨y,39 :: qs,?_,hpc,hpos,hcell,hyq,hframe,hother,?_⟩
  · simpa only [hp] using Steps.step x u y _ qs hi he hs
  · simp only [List.length_cons]
    change qs.length + 5*y.pos 5 ≤ 7 + 5*x.pos 5 at hcost
    omega

open GalilFppLazyForward GalilFppCache

/-- Cached and materializing reads share the same amortized contract. -/
theorem read_cost (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 39) (hh : x.pos 2 ≤ n) (ha : x.pos 2 < n+q.length)
    (hs : Supply x s n q) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = (if s (x.pos 2) = 0 then 38 else 42) ∧
      y.pos 2 = x.pos 2 ∧ y.pos 2 < m ∧ Supply y s m r ∧
      n ≤ m ∧ m+r.length = n+q.length ∧
      (∀ t, t ≠ 2 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      qs.length + 5*y.pos 5 ≤ 8 + 5*x.pos 5 := by
  by_cases hlt : x.pos 2 < n
  · have hc := hs.1.1 (x.pos 2) hlt
    refine ⟨{x with pc := if s (x.pos 2) = 0 then 38 else 42},[39,59],n,q,
      GalilFppForward.dispatch _ x hp hc,rfl,rfl,hlt,hs,le_refl _,rfl,?_,by simp⟩
    exact fun _ _ _ _ => ⟨rfl,rfl⟩
  · have he : x.pos 2 = n := by omega
    cases q with
    | nil => simp at ha; omega
    | cons b rest =>
      have hb : b = s n := hs.2.2.1
      have hblank : x.tape 2 (x.pos 2) = 6 := hs.1.2 _ (by omega)
      obtain ⟨y,qs,hr,hpc,hpos,hcell,hq,ht,hframe,hcost⟩ :=
        forward_blank_cost b rest x hp hblank hs.2.1
      have hc : CacheAt y s (n+1) := by
        apply extend_cache x y s n hs.1
        simpa [he,hb] using ht
      refine ⟨y,qs,n+1,rest,hr,?_,hpos,by omega,⟨hc,hq,hs.2.2.2⟩,
        by omega,?_,hframe,hcost⟩
      · simpa [he,hb] using hpc
      · simp; omega

open GalilFppForward

theorem scan_cost (d : ℕ) (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 39) (hh : x.pos 2 ≤ n) (ha : x.pos 2+d < n+q.length)
    (hs : Supply x s n q) (hu : FullUnary (x.tape 3) (x.pos 3))
    (ho : ∀ k, k < d → s (x.pos 2+k) = 1) (hz : s (x.pos 2+d) = 0) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧ y.pos 2 = x.pos 2+d ∧
      y.pos 3 = x.pos 3+d ∧ FullUnary (y.tape 3) (y.pos 3) ∧ Supply y s m r ∧
      n ≤ m ∧ m+r.length = n+q.length ∧ y.pos 2 < m ∧
      (∀ t, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      qs.length + 5*y.pos 5 ≤ 11*d+8+5*x.pos 5 := by
  induction d generalizing x n q with
  | zero =>
    obtain ⟨y,qs,m,r,hr,hpc,hpos,hlt,hsup,hmn,hav,hframe,hcost⟩ :=
      read_cost x s n q hp hh (by simpa using ha) hs
    obtain ⟨hSp,hSt⟩ := hframe 3 (by decide) (by decide) (by decide)
    refine ⟨y,qs,m,r,hr,?_,by simpa using hpos,by simpa using hSp,?_,hsup,hmn,hav,hlt,
      fun t h2 _ h5 h6 => hframe t h2 h5 h6,by simpa using hcost⟩
    · have hzero : s (x.pos 2) = 0 := by simpa using hz
      simpa [hzero] using hpc
    · simpa [hSp,hSt] using hu
  | succ d ih =>
    have hbit : s (x.pos 2) = 1 := by simpa using ho 0 (by omega)
    obtain ⟨z,qs,m,r,hr,hpc,hpos,hlt,hsup,hmn,hav,hframe,hcost⟩ :=
      read_cost x s n q hp hh (by omega) hs
    have hpc' : z.pc = 42 := by simpa [hbit] using hpc
    have ht := advance_tail z hpc'
    let u := advanceOne z
    obtain ⟨hSp,hSt⟩ := hframe 3 (by decide) (by decide) (by decide)
    have huZ : FullUnary (z.tape 3) (z.pos 3) := by simpa [hSp,hSt] using hu
    have huU : FullUnary (u.tape 3) (u.pos 3) := by
      simpa [u,advanceOne] using full_push (z.tape 3) (z.pos 3) huZ
    have hsU : Supply u s m r := by simpa [Supply,CacheAt,QueueAt,u,advanceOne] using hsup
    have hC : u.pos 2 = x.pos 2+1 := by simp [u,advanceOne,hpos]
    have hS : u.pos 3 = x.pos 3+1 := by simp [u,advanceOne,hSp]
    have hoU : ∀ k, k < d → s (u.pos 2+k) = 1 := by
      intro k hk
      simpa [hC,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ho (k+1) (by omega)
    have hzU : s (u.pos 2+d) = 0 := by
      simpa [hC,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hz
    obtain ⟨y,rs,l,v,hrun,hyPC,hyC,hyS,hyU,hySup,hml,htotal,hylt,hyframe,hrest⟩ :=
      ih u m r rfl (by simp [u,advanceOne]; omega) (by omega) hsU huU hoU hzU
    refine ⟨y,qs ++ [42,41,40] ++ rs,l,v,
      GalilFppCopy.steps_append (GalilFppCopy.steps_append hr ht) hrun,
      hyPC,by omega,by omega,hyU,hySup,by omega,by omega,hylt,?_,?_⟩
    · intro t h2 h3 h5 h6
      obtain ⟨hyp,hyt⟩ := hyframe t h2 h3 h5 h6
      obtain ⟨hzp,hzt⟩ := hframe t h2 h5 h6
      simpa [u,advanceOne,h2,h3,hzp,hzt] using And.intro hyp hyt
    · have hB : u.pos 5 = z.pos 5 := by simp [u,advanceOne]
      rw [hB] at hrest
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega

#print axioms scan_cost
#print axioms read_cost
#print axioms dequeue_all_cost
#print axioms forward_blank_cost
end PalPeg.GalilFppReadCost
