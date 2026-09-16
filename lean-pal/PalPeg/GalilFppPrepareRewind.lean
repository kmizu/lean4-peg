import PalPeg.GalilFppPrepareCopy

set_option autoImplicit false
namespace PalPeg.GalilFppPrepareRewind
open GalilFppWide

def tape (j : Fin 3) : Fin 9 := if j = 0 then 0 else if j = 1 then 1 else 8
def entry (j : Fin 3) : ℕ := if j = 0 then 251 else if j = 1 then 245 else 242
def exitPC (j : Fin 3) : ℕ := if j = 0 then 245 else if j = 1 then 242 else 241
def choices (j : Fin 3) : List (Fin 9 × ℕ) :=
  if j = 0 then [(4,245),(0,252),(1,253),(2,254),(3,255),(5,256)]
  else if j = 1 then [(4,242),(0,246),(1,247),(2,248),(3,249),(5,250)]
  else [(4,241),(7,243),(5,244)]
def allowed (j : Fin 3) (c : Fin 9) : Bool :=
  if j = 2 then c == 7 || c == 5 else decide (c.val ≤ 3) || c == 5
def movePC (j : Fin 3) (c : Fin 9) : ℕ :=
  if j = 0 then if c = 5 then 256 else 252+c.val
  else if j = 1 then if c = 5 then 250 else 246+c.val
  else if c = 7 then 243 else 244

theorem branch_code : ∀ j : Fin 3,
    GalilFppMarkedCode.code[entry j]? = some (.read (tape j) (choices j)) := by decide
theorem left_choice : ∀ j : Fin 3, (4,exitPC j) ∈ choices j := by decide
theorem move_code : ∀ (j : Fin 3) (c : Fin 9), allowed j c = true →
    (c,movePC j c) ∈ choices j ∧
    GalilFppMarkedCode.code[movePC j c]? = some (.move (tape j) false (entry j)) := by decide

/-- All three real rewind loops preserve the complete tape contents,
terminate at the left marker and move no other head. -/
theorem rewind (j : Fin 3) (n : ℕ) (x : Config 9) (hp : x.pc = entry j)
    (hn : x.pos (tape j) = n) (hleft : x.tape (tape j) 0 = 4)
    (hbody : ∀ k, 0 < k → k ≤ n → allowed j (x.tape (tape j) k) = true) :
    ∃ y qs, Steps GalilFppMarkedCode.code x qs y ∧ qs.length = 2*n+1 ∧
      y.pc = exitPC j ∧ y.tape = x.tape ∧
      y.pos = Function.update x.pos (tape j) 0 := by
  induction n generalizing x with
  | zero =>
    let y : Config 9 := { x with pc := exitPC j }
    have hm : (x.tape (tape j) (x.pos (tape j)), exitPC j) ∈ choices j := by
      rw [hn, hleft]; exact left_choice j
    have hs : Steps GalilFppMarkedCode.code x [entry j] y := by
      simpa only [hp] using (Steps.step x y y _ [] (by rw [hp]; exact branch_code j)
        (.read _ _ _ _ hm) (.nil _))
    refine ⟨y, _, hs, rfl, rfl, rfl, ?_⟩
    change x.pos = Function.update x.pos (tape j) 0
    rw [← hn]; simp
  | succ n ih =>
    let c := x.tape (tape j) (x.pos (tape j))
    obtain ⟨hm, hc⟩ := move_code j c (hbody _ (by omega) (by omega))
    let z : Config 9 := { x with pc := movePC j c }
    let u : Config 9 := { z with
      pc := entry j
      pos := Function.update z.pos (tape j) (z.pos (tape j)-1) }
    have hs : Steps GalilFppMarkedCode.code x [entry j, movePC j c] u := by
      simpa only [hp] using (Steps.step x z u _ _ (by rw [hp]; exact branch_code j)
        (.read _ _ _ _ hm) (.step z u u _ [] hc (.left _ _ _ (by change 0 < x.pos (tape j); omega)) (.nil _)))
    have hup : u.pos (tape j) = n := by simp [u, z, hn]
    obtain ⟨y, qs, hr, hl, hypc, hyt, hyp⟩ := ih u rfl hup hleft
      (fun k hk hkn => hbody k hk (by omega))
    refine ⟨y, [entry j, movePC j c] ++ qs, steps_append hs hr, ?_, hypc, hyt, ?_⟩
    · simp [hl]; omega
    · simpa [u, z] using hyp

/-- All three rewinds and the final B advance, ending at the actual
kernel start. Every tape cell and every unrelated head is preserved. -/
theorem rewind_all (x : Config 9) (hp : x.pc = 251)
    (hleft : ∀ j : Fin 3, x.tape (tape j) 0 = 4)
    (hbody : ∀ (j : Fin 3) k, 0 < k → k ≤ x.pos (tape j) →
      allowed j (x.tape (tape j) k) = true) :
    ∃ y qs, Steps GalilFppMarkedCode.code x qs y ∧
      qs.length = 2*(x.pos 0+x.pos 1+x.pos 8)+4 ∧ y.pc = 227 ∧ y.tape = x.tape ∧
      y.pos = Function.update (Function.update (Function.update x.pos 0 0) 1 1) 8 0 := by
  obtain ⟨a, qa, ha, hla, hpa, hta, hposa⟩ :=
    rewind 0 (x.pos 0) x hp rfl (hleft 0) (hbody 0)
  have hA : a.pos = Function.update x.pos 0 0 := hposa
  have hBa : a.pos 1 = x.pos 1 := by simp [hA]
  obtain ⟨b, qb, hb, hlb, hpb, htb, hposb⟩ :=
    rewind 1 (x.pos 1) a hpa hBa (by rw [hta]; exact hleft 1)
      (by intro k hk hkn; rw [hta]; exact hbody 1 k hk hkn)
  have hB : b.pos = Function.update a.pos 1 0 := hposb
  have hMb : b.pos 8 = x.pos 8 := by simp [hB, hA]
  obtain ⟨c, qc, hc, hlc, hpc, htc, hposc⟩ :=
    rewind 2 (x.pos 8) b hpb hMb (by rw [htb, hta]; exact hleft 2)
      (by intro k hk hkn; rw [htb, hta]; exact hbody 2 k hk hkn)
  have hC : c.pos = Function.update b.pos 8 0 := hposc
  let y : Config 9 := { c with pc := 227, pos := Function.update c.pos 1 (c.pos 1+1) }
  have hm : Steps GalilFppMarkedCode.code c [241] y := by
    have hp241 : c.pc = 241 := hpc
    simpa only [hp241] using (Steps.step c y y _ [] (by rw [hp241]; rfl)
      (.right _ _ _) (.nil _))
  refine ⟨y, qa ++ qb ++ qc ++ [241], steps_append (steps_append (steps_append ha hb) hc) hm,
    ?_, rfl, htc.trans (htb.trans hta), ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · funext t
    fin_cases t <;> simp [y, hC, hB, hA]

#print axioms rewind_all
#print axioms rewind
end PalPeg.GalilFppPrepareRewind
