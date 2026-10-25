import MacroPeg.CBV.SequentialTotalSyntax

/-! Semantic control laws for total result flags. Unknown source results
make every flag finitely fail; in particular, unknown is never a finite
failure of the source and must not enable its alternative or negation.
These laws are conditional on the subexpression flags, and do not yet prove
the recursive grammar construction correct. -/
namespace Shallot.MacroPeg.CBV.SequentialTotalControl
open SequentialTotalSyntax

def zeroResult (p : Nat) : Res → Res
  | some (some q) => if q=p then some (some p) else some none
  | _ => some none
def positiveResult (p : Nat) : Res → Res
  | some (some q) => if q=p then some none else some (some q)
  | _ => some none
def failureResult (p : Nat) : Res → Res
  | some none => some (some p)
  | _ => some none
def successResult : Res → Res
  | some (some q) => some (some q)
  | _ => some none

def Realizes (g : MGrammar) (x : List Char) (T : SequentialClock.Table)
    (E : List (List Char)) (a : Forms) (p : Nat) (r : Res) : Prop :=
  evV g x .callByValueSeq T E a.zero p=zeroResult p r ∧
  evV g x .callByValueSeq T E a.positive p=positiveResult p r ∧
  evV g x .callByValueSeq T E a.failure p=failureResult p r

def seqResult (r : Res) (b : Nat → Res) : Res :=
  match r with | some (some q) => b q | other => other
def altResult (a b : Res) : Res := match a with | some none => b | other => other
def notResult (p : Nat) : Res → Res
  | none => none | some none => some (some p) | some (some _) => some none

variable {g : MGrammar} {x : List Char} {T : SequentialClock.Table}
  {E : List (List Char)} {p : Nat}

theorem success_correct (a : Forms) (r : Res) (ha : Realizes g x T E a p r) :
    evV g x .callByValueSeq T E a.success p=successResult r := by
  rcases ha with ⟨hz,hpos,hf⟩
  cases r with
  | none => simp [Forms.success,evV,hpos,hz,positiveResult,zeroResult,successResult]
  | some r => cases r with
    | none => simp [Forms.success,evV,hpos,hz,positiveResult,zeroResult,successResult]
    | some q => by_cases hq : q=p <;>
        simp [Forms.success,evV,hpos,hz,positiveResult,zeroResult,successResult,hq]

theorem alt_correct (a b : Forms) (ra rb : Res)
    (ha : Realizes g x T E a p ra) (hb : Realizes g x T E b p rb) :
    Realizes g x T E (altForms a b) p (altResult ra rb) := by
  rcases ha with ⟨az,ap,af⟩
  rcases hb with ⟨bz,bp,bf⟩
  cases ra with
  | none => simp [Realizes,altForms,evV,az,ap,af,zeroResult,positiveResult,failureResult,altResult]
  | some ra => cases ra with
    | none => simp [Realizes,altForms,evV,az,ap,af,bz,bp,bf,zeroResult,positiveResult,failureResult,altResult]
    | some q => by_cases hq : q=p <;>
        simp [Realizes,altForms,evV,az,ap,af,zeroResult,positiveResult,failureResult,altResult,hq]

theorem not_correct (a : Forms) (ra : Res) (ha : Realizes g x T E a p ra) :
    Realizes g x T E (notForms a) p (notResult p ra) := by
  have hs := success_correct a ra ha
  rcases ha with ⟨az,ap,af⟩
  cases ra with
  | none => simp [Realizes,notForms,MExp.andP,evV,af,hs,zeroResult,positiveResult,failureResult,successResult,notResult,MExp.failAlways]
  | some ra => cases ra with
    | none => simp [Realizes,notForms,MExp.andP,evV,af,hs,zeroResult,positiveResult,failureResult,successResult,notResult,MExp.failAlways]
    | some q => simp [Realizes,notForms,MExp.andP,evV,af,hs,zeroResult,positiveResult,failureResult,successResult,notResult,MExp.failAlways]

/-- The current-stage flags suffice while stationary. After a positive
left operand, the full-stage flags are used at a strictly smaller position. -/
theorem seq_correct (a b bN : Forms) (ra : Res) (rb : Nat → Res)
    (ha : Realizes g x T E a p ra)
    (hb : Realizes g x T E b p (rb p))
    (hn : ∀ q, q<p → Realizes g x T E bN q (rb q))
    (da : ∀ q, ra=some (some q) → q≤p)
    (db : ∀ q r, q<p → rb q=some (some r) → r≤q) :
    Realizes g x T E (seqForms a b bN) p (seqResult ra rb) := by
  rcases ha with ⟨az,ap,af⟩
  rcases hb with ⟨bz,bp,bf⟩
  cases hra : ra with
  | none => simp [Realizes,seqForms,MExp.andP,evV,az,ap,af,hra,zeroResult,positiveResult,failureResult,seqResult]
  | some ra => cases ra with
    | none => simp [Realizes,seqForms,MExp.andP,evV,az,ap,af,hra,zeroResult,positiveResult,failureResult,seqResult]
    | some q =>
      by_cases hq : q=p
      · subst q
        simp [Realizes,seqForms,MExp.andP,evV,az,ap,af,hra,bz,bp,bf,
          zeroResult,positiveResult,failureResult,seqResult]
      · have hqp : q<p := by have := da q hra; omega
        have hs := success_correct bN (rb q) (hn q hqp)
        obtain ⟨nz,np,nf⟩ := hn q hqp
        cases hrb : rb q with
        | none => simp [Realizes,seqForms,MExp.andP,evV,az,ap,af,hra,hs,nf,hrb,
            zeroResult,positiveResult,failureResult,successResult,seqResult,hq]
        | some rbq => cases rbq with
          | none => simp [Realizes,seqForms,MExp.andP,evV,az,ap,af,hra,hs,nf,hrb,
              zeroResult,positiveResult,failureResult,successResult,seqResult,hq]
          | some r =>
            have hrp : r≠p := by have := db q r hqp hrb; omega
            simp [Realizes,seqForms,MExp.andP,evV,az,ap,af,hra,hs,nf,hrb,
              zeroResult,positiveResult,failureResult,successResult,seqResult,hq,hrp]

/-- Greedy repetition of the positive flag must finish with the *source
finite-failure* flag. Merely stopping the positive parser would incorrectly
accept a nullable or undefined source operand. -/
theorem star_tail_correct (a : Forms) (r : Nat → Res) : ∀ p,
    (∀ q, q≤p → Realizes g x T E a q (r q)) →
    (∀ q v, q≤p → r q=some (some v) → v≤q) →
    evV g x .callByValueSeq T E (.seq (.star a.positive) a.failure) p=
      successResult (evStar r p) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro ha down
    obtain ⟨az,ap,af⟩ := ha p (Nat.le_refl _)
    change seqResult (evStar (fun q => evV g x .callByValueSeq T E a.positive q) p)
      (fun q => evV g x .callByValueSeq T E a.failure q)=_
    cases hr : r p with
    | none =>
      have hp : evV g x .callByValueSeq T E a.positive p=some none := by rw [ap,hr]; rfl
      rw [evStar_fail hp,evStar_none hr]
      simp [seqResult,af,hr,failureResult,successResult]
    | some v => cases v with
      | none =>
        have hp : evV g x .callByValueSeq T E a.positive p=some none := by rw [ap,hr]; rfl
        rw [evStar_fail hp,evStar_fail hr]
        simp [seqResult,af,hr,failureResult,successResult]
      | some q =>
        by_cases hq : q=p
        · subst q
          have hp : evV g x .callByValueSeq T E a.positive p=some none := by simp [ap,hr,positiveResult]
          rw [evStar_fail hp,evStar_stuck hr (Nat.lt_irrefl _)]
          simp [seqResult,af,hr,failureResult,successResult]
        · have hqp : q<p := by have := down p q (Nat.le_refl _) hr; omega
          have hp : evV g x .callByValueSeq T E a.positive p=some (some q) := by simp [ap,hr,positiveResult,hq]
          rw [evStar_ok hp hqp,evStar_ok hr hqp]
          exact ih q hqp (by intro j hj; exact ha j (by omega))
            (by intro j v hj hv; exact down j v (by omega) hv)

theorem star_correct (a aN : Forms) (r : Nat → Res)
    (ha : Realizes g x T E a p (r p))
    (hn : ∀ q, q<p → Realizes g x T E aN q (r q))
    (down : ∀ q v, q≤p → r q=some (some v) → v≤q) :
    Realizes g x T E (starForms a aN) p (evStar r p) := by
  obtain ⟨az,ap,af⟩ := ha
  cases hr : r p with
  | none =>
    rw [evStar_none hr]
    simp [Realizes,starForms,evV,ap,af,hr,zeroResult,positiveResult,failureResult,MExp.failAlways]
  | some v => cases v with
    | none =>
      rw [evStar_fail hr]
      simp [Realizes,starForms,evV,ap,af,hr,zeroResult,positiveResult,failureResult,MExp.failAlways]
    | some q =>
      by_cases hq : q=p
      · subst q
        rw [evStar_stuck hr (Nat.lt_irrefl _)]
        simp [Realizes,starForms,evV,ap,af,hr,zeroResult,positiveResult,failureResult,MExp.failAlways]
      · have hqp : q<p := by have := down p q (Nat.le_refl _) hr; omega
        have ht := star_tail_correct aN r q
          (by intro j hj; exact hn j (by omega))
          (by intro j v hj hv; exact down j v (by omega) hv)
        rw [evStar_ok hr hqp]
        have hp : evV g x .callByValueSeq T E a.positive p=some (some q) := by simp [ap,hr,positiveResult,hq]
        have he : evV g x .callByValueSeq T E (starForms a aN).positive p=
            successResult (evStar r q) := by
          exact (evV_seq_ok hp).trans ht
        unfold Realizes
        rw [he]
        cases hs : evStar r q with
        | none => simp [starForms,af,hr,zeroResult,positiveResult,failureResult,successResult,MExp.failAlways,evV]
        | some v => cases v with
          | none => exact False.elim (evStar_ne_fail q hs)
          | some j =>
            have hj : j≠p := by have := evStar_le q j hs; omega
            simp [starForms,af,hr,zeroResult,positiveResult,failureResult,successResult,hj,MExp.failAlways,evV]

end Shallot.MacroPeg.CBV.SequentialTotalControl
