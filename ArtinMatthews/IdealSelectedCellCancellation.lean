module

public import ArtinMatthews.IdealPrimeCellCancellation
public import ArtinMatthews.IdealCharacterCells
public import ArtinMatthews.IdealSelectedSplit


set_option backward.privateInPublic true
@[expose] public section

/-! Actual full-tuple character cancellation under a logarithmic cell.
Only one prime coordinate is estimated; every other harmonic coordinate
is averaged with its original probability mass. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def idealSelectedCharacterCell {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : I → Finset ℕ) (h : ℝ) (j : ℤ) : ℂ :=
  ∑ a : IdealSelectedLabels P, (idealSelectedMass P a : ℂ) *
    (if idealLogCell h a = j then χ (idealSelectedProduct a : ZMod q) else 0)

theorem idealSelectedCharacterCell_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : I → Finset ℕ) (i : I) (h : ℝ) (j : ℤ) :
    idealSelectedCharacterCell χ P h j =
      ∑ b : IdealSelectedLabels (idealSelectedRest P i),
        (idealSelectedMass (idealSelectedRest P i) b : ℂ) *
          χ (idealSelectedProduct b : ZMod q) *
            idealHarmonicPrimeCell χ (P i) h (idealSelectedProduct b) j := by
  unfold idealSelectedCharacterCell
  rw [idealSelectedExpectation_split P i]
  apply sum_congr rfl
  intro b _
  rw [mul_assoc]
  congr 1
  rw [idealHarmonicPrimeCell, mul_sum]
  apply sum_congr rfl
  intro p _
  simp only [idealLogCell, idealSelectedProduct_join, idealPrimeCellIndex, Nat.mul_comm,
    Nat.cast_mul, map_mul]
  split_ifs
  · ring
  · simp only [mul_zero]

theorem idealSelectedCharacterCell_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (i : I) (h : ℝ) (j : ℤ)
    {E : ℝ}
    (hcell : ∀ r : ℕ, 0 < r → ‖idealHarmonicPrimeCell χ (P i) h r j‖ ≤ E) :
    ‖idealSelectedCharacterCell χ P h j‖ ≤ E := by
  rw [idealSelectedCharacterCell_split χ P i h j]
  have hrest (b : IdealSelectedLabels (idealSelectedRest P i)) :
      0 ≤ idealSelectedMass (idealSelectedRest P i) b :=
    idealSelectedMass_nonneg (idealSelectedRest P i) (fun k => hV k.val) b
  have hbound (b : IdealSelectedLabels (idealSelectedRest P i)) :
      ‖idealHarmonicPrimeCell χ (P i) h (idealSelectedProduct b) j‖ ≤ E := by
    apply hcell
    exact idealSelectedProduct_pos (I := {k : I // k ≠ i})
      (P := idealSelectedRest P i) (fun k p hp => hP k.val p hp) b
  calc
    _ ≤ ∑ b : IdealSelectedLabels (idealSelectedRest P i),
        ‖(idealSelectedMass (idealSelectedRest P i) b : ℂ) *
          χ (idealSelectedProduct b : ZMod q) *
            idealHarmonicPrimeCell χ (P i) h (idealSelectedProduct b) j‖ := norm_sum_le _ _
    _ ≤ ∑ b : IdealSelectedLabels (idealSelectedRest P i),
        idealSelectedMass (idealSelectedRest P i) b * E := by
      apply sum_le_sum
      intro b _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hrest b)]
      calc
        _ ≤ (idealSelectedMass (idealSelectedRest P i) b * 1) * E :=
          mul_le_mul (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (hrest b))
            (hbound b) (norm_nonneg _) (mul_nonneg (hrest b) zero_le_one)
        _ = _ := by rw [mul_one]
    _ = E := by
      rw [← sum_mul, idealSelectedMass_sum (idealSelectedRest P i) (fun k => hV k.val), one_mul]

theorem idealSelectedCharacterCell_source_bound (a c d D v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hD : 0 ≤ D) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ L^a → χ ≠ 1 →
        ∀ (P : I → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
        (∀ i, 0 < bandReciprocalMass (P i)) → ∀ i : I,
        IdealPrimeInterval (P i) →
        (∀ p ∈ P i, Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        v₀ ≤ bandReciprocalMass (P i) →
        ∀ (h : ℝ), 0 < h → ∀ j : ℤ,
          ‖idealSelectedCharacterCell χ P h j‖ ≤ L^(-D) := by
  filter_upwards [idealHarmonicPrimeCell_source_bound a c d D v₀ ha hc hd hD hv₀]
    with L hcell
  intro q _ χ hq hχ P hP hV i hinterval hbounds hVlo h hh j
  apply idealSelectedCharacterCell_bound χ P hP hV i h j
  intro r hr
  exact hcell q χ hq hχ (P i) (hP i) hinterval hbounds hVlo h hh r hr j

end
end ArtinMatthews
