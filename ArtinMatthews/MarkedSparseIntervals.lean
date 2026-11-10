module

public import ArtinMatthews.MarkedSparsePrimeMoments
public import ArtinMatthews.MarkedSparseAsymptoticCount
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Passing from separated point samples to literal unit intervals, by
three residue classes of integer left endpoints. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

/-- Points in distinct unit intervals whose left endpoints agree modulo
three are separated by at least one, including both interval endpoints. -/
theorem unitInterval_mod_three_separated {z w : ℤ} {t s : ℝ}
    (hz : t ∈ Set.Icc (z : ℝ) ((z : ℝ)+1))
    (hw : s ∈ Set.Icc (w : ℝ) ((w : ℝ)+1))
    (hmod : z % 3 = w % 3) (hne : z ≠ w) : 1 ≤ |t-s| := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hgap : z+3 ≤ w := by omega
    have hgapR : (z : ℝ)+3 ≤ (w : ℝ) := by exact_mod_cast hgap
    have hts : t-s ≤ -1 := by linarith [hz.2, hw.1]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hgap : w+3 ≤ z := by omega
    have hgapR : (w : ℝ)+3 ≤ (z : ℝ) := by exact_mod_cast hgap
    have hts : 1 ≤ t-s := by linarith [hz.1, hw.2]
    exact hts.trans (le_abs_self _)

/-- An arbitrary property of points inherits a unit-interval count bound
from its one-separated sample bound. No differentiability or derivative
bound is needed to select an exceeding point in each interval. -/
theorem unitInterval_count_of_separated_samples
    (I : Finset ℤ) (Q : ℝ → Prop) {C : ℝ}
    (hwitness : ∀ z ∈ I, ∃ t ∈ Set.Icc (z : ℝ) ((z : ℝ)+1), Q t)
    (hsamples : ∀ S : Finset ℝ, (∀ t ∈ S, Q t) →
      (∀ t ∈ S, ∀ s ∈ S, t ≠ s → 1 ≤ |t-s|) → (S.card : ℝ) ≤ C) :
    (I.card : ℝ) ≤ 3*C := by
  classical
  let point : ℤ → ℝ := fun z => if hz : z ∈ I then (hwitness z hz).choose else 0
  have hp (z : ℤ) (hz : z ∈ I) :
      point z ∈ Set.Icc (z : ℝ) ((z : ℝ)+1) ∧ Q (point z) := by
    simpa only [point, dite_eq_left hz] using (hwitness z hz).choose_spec
  have hclass (j : ℤ) : ((I.filter (fun z => z%3=j)).card : ℝ) ≤ C := by
    let J := I.filter (fun z => z%3=j)
    have hJ (z : ℤ) (hz : z ∈ J) : z ∈ I ∧ z%3=j := Finset.mem_filter.mp hz
    have hinj : Set.InjOn point (J : Set ℤ) := by
      intro z hz w hw heq
      by_contra hne
      have hs := unitInterval_mod_three_separated (hp z (hJ z hz).1).1
        (hp w (hJ w hw).1).1 ((hJ z hz).2.trans (hJ w hw).2.symm) hne
      rw [heq, sub_self, abs_zero] at hs
      norm_num at hs
    have hc := hsamples (J.image point) (by
      intro t ht
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
      exact (hp z (hJ z hz).1).2) (by
      intro t ht s hs hne
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hs
      exact unitInterval_mod_three_separated (hp z (hJ z hz).1).1
        (hp w (hJ w hw).1).1 ((hJ z hz).2.trans (hJ w hw).2.symm)
        (fun h => hne (congrArg point h)))
    simpa only [Finset.card_image_of_injOn hinj] using hc
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := I) (t := Finset.Ico (0 : ℤ) 3) (f := fun z : ℤ => z%3) (by
      intro z hz
      exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg z (by norm_num), Int.emod_lt_of_pos z (by norm_num)⟩)
  calc
    (I.card : ℝ) = ∑ j ∈ Finset.Ico (0 : ℤ) 3,
        ((I.filter (fun z => z%3=j)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _j ∈ Finset.Ico (0 : ℤ) 3, C := Finset.sum_le_sum (fun j _ => hclass j)
    _ = 3*C := by norm_num

/-- The literal family of unit intervals meeting the exceptional set has
subexponential size, uniformly in every character and real shift. -/
theorem markedPrimePolynomial_sparse_unitIntervals (c C₁ C₂ A : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ Y T : ℝ, 1 < Y →
      c * L^(1/(10:ℝ)) ≤ Real.log Y →
      Real.log Y ≤ C₁ * L^(1/(5:ℝ)) → 1 < T → Real.log T ≤ C₂ * L →
      ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p : ℝ) ≤ 2*Y) →
      ∀ I : Finset ℤ,
      (∀ z ∈ I, ∃ t ∈ Set.Icc (z : ℝ) ((z : ℝ)+1),
        |t| ≤ T ∧ L^(-A) ≤ ‖markedPrimePolynomial P Y χ ξ t‖) →
      (I.card : ℝ) ≤ 3*Real.exp (L^(91/(100:ℝ))) := by
  filter_upwards [markedPrimePolynomial_sparse_samples c C₁ C₂ A hc hC₁ hC₂ hA]
    with L hsamples
  intro Y T hY hlo hhi hT hTU k χ ξ P hP hcap I hwitness
  apply unitInterval_count_of_separated_samples I
    (fun t => |t| ≤ T ∧ L^(-A) ≤ ‖markedPrimePolynomial P Y χ ξ t‖) hwitness
  intro S hS hsep
  exact hsamples Y T hY hlo hhi hT hTU k χ ξ P hP hcap S
    (fun t ht => (hS t ht).1) hsep (fun t ht => (hS t ht).2)

end
end ArtinMatthews
