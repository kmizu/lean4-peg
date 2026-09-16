import PalPeg.GalilOriginPeriod
import PalPeg.GalilPeriodNext
import PalPeg.GalilPeriodSpan
import PalPeg.GalilLiveCentreShift
import PalPeg.GalilLiveCentreMismatch
import PalPeg.GalilLiveCentreSegs
import PalPeg.GalilLiveCentreSeg

/-!
# The leftmost live centre across the re-shift rounds

`rounds_leftmost` carries, over the `Rounds` of the actual controller, the
package of facts that a chain round needs: the read origin (`Entry`), the
`2h`-periodicity of the current span together with its minimality, and the
centre invariant `MInv` (the centre is the leftmost live centre).

Each round: the scan segment keeps `MInv`; the terminal mismatch kills the
old centre at the next place (`not_live_of_mismatch`); the next origin's
`Entry` makes `C + h` live there; `periodOn_span_of_next` globalises the
`2h` period over the new span and `noBelow_next` carries the minimality, so
`leftmost_shift` gives the new leftmost live centre.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- `PeriodOn` transported along equal endpoints. -/
theorem periodOn_congr {α : Type} {x : List α} {p a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (h : PeriodOn x p a b) : PeriodOn x p a' b' := by
  subst ha; subst hb; exact h

theorem rounds_leftmost (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ) {m : ℕ}
    {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s') :
    ∀ w0 : GalilScaffoldChainWatch.State, s.periodOnly = true → s.chain = .watch w0 →
      zero w0.lag = true → ∀ org : ReadOrigin raw, org.interior.length+1 = h →
      Entry raw org (toOnly s w0) →
      PeriodOn (encoded raw) (2*h) (org.center - org.radius) (org.center + org.radius) →
      (∀ p, 0 < p → p < 2*h → ¬ PeriodOn (encoded raw) p (org.center - org.radius) (org.center + org.radius)) →
      c.replaying = false → MInv raw c s →
      ∃ (org' : ReadOrigin raw) (w' : GalilScaffoldChainWatch.State),
        org'.interior.length+1 = h ∧ org'.center = org.center + m*h ∧ org'.radius = org.radius + m*h ∧
        s'.chain = .watch w' ∧ zero w'.lag = true ∧ s'.periodOnly = true ∧ Entry raw org' (toOnly s' w') ∧
        PeriodOn (encoded raw) (2*h) (org'.center - org'.radius) (org'.center + org'.radius) ∧
        (∀ p, 0 < p → p < 2*h → ¬ PeriodOn (encoded raw) p (org'.center - org'.radius) (org'.center + org'.radius)) ∧
        c'.replaying = false ∧ MInv raw c' s' := by
  induction hr with
  | stop c s =>
    intro w0 hp hs hz org hint he hper0 hmin0 hrepl hM
    exact ⟨org, w0, hint, by simp, by simp, hs, hz, hp, he, hper0, hmin0, hrepl, hM⟩
  | next c s hseg hm1 hr1 hc1 w hs1 hav vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho rest ih =>
    intro w0 hp hs hz org hint he hper0 hmin0 hrepl hM
    rename_i mm nn c1 s1 tt vv cyc cc ss
    have hh : 0 < h := by omega
    -- the comparison parts
    have hcmpl : vs.left = left s1.left ∧ vs.right = right s1.right := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      exact ⟨hl0, hr0⟩
    have hmatch0 : read (left s1.left) ≠ read (right s1.right) := by
      intro h0
      apply hmis
      show read (scanLens.get (scanLens.set s1 vs)).left = read (scanLens.get (scanLens.set s1 vs)).right
      rw [scanLens.get_set]
      show read vs.left = read vs.right
      rw [hcmpl.1, hcmpl.2]; exact h0
    -- the invariant at the start of the round
    have hi0 := entry_scanInvariant he
    have hcp : position s.center = org.center + h := by
      have h0 := he.centerPos; rw [hint] at h0; exact h0
    have hiS : ScanInvariant raw (position s.center) (org.radius+1-h) s.left s.right := by
      rw [hcp]; rw [hint] at hi0; exact hi0
    -- the centre invariant along the segment
    have hM1 := minv_scanSeg raw P q first delay hseg _ hiS hM
    have hL1 : Leftmost raw (position s1.right) (position s.center) := by
      have h0 := minv_leftmost hM1 hr1
      rw [scanSeg_center P q first delay hseg] at h0
      exact h0
    -- the invariant at the terminal comparison
    obtain ⟨es, hsc⟩ := scanSeg_heads P q first delay hseg
    have hi1 := scan_events_invariant (hsc raw (position s.center) (org.radius+1-h)) hiS
    -- the round, and the next origin
    obtain ⟨_, hcr1⟩ := round_next P q first delay h hseg w0 hp hs hz hm1 hr1 hc1 w hs1 hav vs vq
      hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho
    obtain ⟨org', he', _, hinterior, _, _, _, hcenter', hradius'⟩ := rounds_origin hcr1 org hint he
    have hint' : org'.interior.length+1 = h := by rw [hinterior]; exact hint
    have hi' : ScanInvariant raw (org'.center + h) (org'.radius+1-h) tt.left s2.right := by
      have h0 := entry_scanInvariant he'
      rw [hint'] at h0; exact h0
    have hcp' : position tt.center = org'.center + h := by
      have h0 := he'.centerPos; rw [hint'] at h0; exact h0
    -- the sizes
    have hsize : 2*h ≤ org.radius := by have h0 := org.size; rw [hint] at h0; exact h0
    have hsize' : 2*h ≤ org'.radius := by have h0 := org'.size; rw [hint'] at h0; exact h0
    have hRA : org.radius ≤ org.center := org.scan.palindrome.1
    -- the positions
    have hrpos : position (right s1.right) = position s1.right + 1 :=
      right_position s1.right hav (represented_position s1.right.head raw hi1.rightRep hi1.rightPresent).1
    have hSright : s2.right = right s1.right := by
      rw [hs2.2]; simp [afterMismatch, searchLens, scanLens, hcmpl.2]
    have hposR : position s2.right = position s1.right + 1 := by rw [hSright]; exact hrpos
    have hprA : position s1.right = org.center + org.radius + 2*h := by
      have e1 := hi'.rightPos; omega
    have hcnt : org.radius+1-h+es.count true = org.radius + h := by
      have e2 := hi1.rightPos; omega
    rw [hcnt] at hi1
    -- the palindromes and the read period
    have h0 : PalAt (encoded raw) (position s.center) (org.radius + h) := hi1.palindrome
    have h1 : PalAt (encoded raw) (position s.center + h) (org.radius + h + 1 - h) := by
      have hpa := hi'.palindrome
      have e1 : org'.center + h = position s.center + h := by omega
      have e2 : org'.radius + 1 - h = org.radius + h + 1 - h := by omega
      rw [e1, e2] at hpa; exact hpa
    have hright : PeriodOn (encoded raw) (2*h) (position s.center + 1)
        (position s.center + (org.radius + h) + 1) := by
      have h2 := org'.origin_periodOn_right
      rw [hint'] at h2
      exact periodOn_congr (by omega) (by omega) h2
    have hspan := periodOn_span_of_next hh (show 2*h ≤ org.radius + h by omega) h0 h1 hright
    have hperB : PeriodOn (encoded raw) (2*h) (org.center + h - (org.radius+h))
        (org.center + h + (org.radius+h)) :=
      periodOn_restrict hspan (by omega) (by omega)
    have hlenB : org.center + h + (org.radius + h) < (encoded raw).length := by
      have h2 := h0.2.1; omega
    have hminB := noBelow_next (x := encoded raw) (C := org.center) (k := org.radius)
      (k' := org.radius + h) (h := h) hh hsize (by omega) (by omega) hRA (by omega) hlenB
      hper0 hmin0 hperB
    have hper1 : PeriodOn (encoded raw) (2*h) (org'.center - org'.radius) (org'.center + org'.radius) :=
      periodOn_congr (by omega) (by omega) hperB
    have hmin1 : ∀ p, 0 < p → p < 2*h →
        ¬ PeriodOn (encoded raw) p (org'.center - org'.radius) (org'.center + org'.radius) := by
      intro p hp0 hp2 hcon
      exact hminB p hp0 hp2 (periodOn_congr (by omega) (by omega) hcon)
    -- the shift of the leftmost live centre
    have hdead : ¬ Live raw (position s1.right + 1) (position s.center) :=
      not_live_of_mismatch hi1 hav hmatch0
    have hlive : Live raw (position s1.right + 1) (position s.center + h) := by
      have hl0 := live_of_scanInvariant hi'
      rw [hposR] at hl0
      have e : org'.center + h = position s.center + h := by omega
      rw [e] at hl0; exact hl0
    have hmin : ∀ p, 0 < p → p < 2*h →
        ¬ HasPeriod (Span raw (position s.center) (position s1.right - position s.center)) p := by
      intro p hp0 hp2 hcon
      apply hmin1 p hp0 hp2
      have ed : position s1.right - position s.center = org.radius + h := by omega
      rw [ed] at hcon
      unfold Span at hcon
      have ea : position s.center - (org.radius+h) = org'.center - org'.radius := by omega
      have eb : 2*(org.radius+h)+1 = (org'.center + org'.radius) + 1 - (org'.center - org'.radius) := by
        omega
      rw [ea, eb] at hcon
      exact (hasPeriod_slice_iff (x := encoded raw) (p := p) (by omega) (by omega)).mp hcon
    have hL' : Leftmost raw (position s1.right + 1) (position s.center + h) :=
      leftmost_shift hL1 hdead hlive hmin
    have hLS : Leftmost raw (position s2.right) (position tt.center) := by
      rw [hposR, hcp']
      have e : org'.center + h = position s.center + h := by omega
      rw [e]; exact hL'
    -- the start of the next round
    obtain ⟨w1, hw1, hz1, _, _⟩ := scanSeg_only P q first delay hseg w0 hp hs hz
    have hww : w1 = w := by rw [hs1] at hw1; injection hw1 with e; exact e.symm
    subst hww
    obtain ⟨org'', w'', hint'', hcenter'', hradius'', hchain'', hz'', hp'', he'', hper'', hmin'',
      hrepl'', hM''⟩ := ih _ (by show s2.periodOnly = true; rw [hs2.2]) rfl
      (by rw [chain_shift_lag hchain]; exact hz1) org' hint' he' hper1 hmin1 hr1
      (minv_of_leftmost hLS hr1)
    refine ⟨org'', w'', hint'', ?_, ?_, hchain'', hz'', hp'', he'', hper'', hmin'', hrepl'', hM''⟩
    · rw [hcenter'', hcenter']; ring
    · rw [hradius'', hradius']; ring

#print axioms rounds_leftmost

end PalPeg.GalilScaffoldChainInputSupply
