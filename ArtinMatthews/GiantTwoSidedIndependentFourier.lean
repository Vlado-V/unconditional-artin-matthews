module

public import ArtinMatthews.GiantTwoSidedFourierTwist
public import ArtinMatthews.GiantTwoSidedFixedRootTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! The original signed independent moment is the average of its
unrestricted terminal-position expression with the exact return phase. -/
namespace ArtinMatthews
open MeasureTheory Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val] {k ell n : ℕ}

def giantTwoSidedIndependentUnrestrictedMoment (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell) : ℂ :=
  ∑ labels : Fin (n + 1) → MarkedPhysicalMarking P (k + ell),
    if GiantTwoSidedStaticLabels C π τ aux labels then
      giantTwoSidedRootScalar C labels π τ aux ζ K *
        (giantTwoSidedIndependentResidueMean labels q
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)) : ℂ)
    else 0

def giantTwoSidedIndependentFourierMoment (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ labels : Fin (n + 1) → MarkedPhysicalMarking P (k + ell),
    if GiantTwoSidedStaticLabels C π τ aux labels then
      giantTwoSidedRootScalar C labels π τ aux ζ K *
        (giantTwoSidedIndependentResidueMean labels q
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)) : ℂ) *
        fourier (giantTwoSidedPathOffset
          (giantTwoSidedLabelIncrement C labels π aux step) (Fin.last n)) θ
    else 0

theorem giantTwoSidedIndependentFourier_continuous (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell) :
    Continuous (giantTwoSidedIndependentFourierMoment C π τ aux step q ζ K) := by
  unfold giantTwoSidedIndependentFourierMoment
  apply continuous_finsetSum
  intro labels _
  by_cases h : GiantTwoSidedStaticLabels C π τ aux labels
  · simp only [h, ite_true]
    exact continuous_const.mul (fourier _).continuous
  · simp only [h, ite_false]
    exact continuous_const

theorem giantTwoSidedIndependentFourier_integrable (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell) :
    Integrable (giantTwoSidedIndependentFourierMoment C π τ aux step q ζ K)
      AddCircle.haarAddCircle :=
  (giantTwoSidedIndependentFourier_continuous C π τ aux step q ζ K).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem giantTwoSidedIndependentMoment_fourier (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell) :
    giantTwoSidedIndependentMoment C π τ aux step q ζ K =
      ∫ θ : AddCircle (1 : ℝ),
        giantTwoSidedIndependentFourierMoment C π τ aux step q ζ K θ
          ∂AddCircle.haarAddCircle := by
  symm
  unfold giantTwoSidedIndependentFourierMoment
  rw [integral_finsetSum]
  · unfold giantTwoSidedIndependentMoment
    apply sum_congr rfl
    intro labels _
    by_cases h : GiantTwoSidedStaticLabels C π τ aux labels
    · simp only [h, ite_true, true_and]
      rw [integral_const_mul, giantTwoSidedFourier_integral]
      split_ifs <;> simp
    · simp [h]
  · intro labels _
    by_cases h : GiantTwoSidedStaticLabels C π τ aux labels
    · simp only [h, ite_true]
      exact (continuous_const.mul (fourier _).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · simp only [h, ite_false]
      exact integrable_const (0 : ℂ)

theorem giantTwoSidedIndependentFourier_twisted (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (θ : AddCircle (1 : ℝ)) :
    giantTwoSidedIndependentFourierMoment C π τ aux step q ζ K θ =
      giantTwoSidedIndependentUnrestrictedMoment C π τ aux step q ζ
        (fun i => giantTwoSidedFourierCoefficient θ (step i) (K i)) := by
  unfold giantTwoSidedIndependentFourierMoment giantTwoSidedIndependentUnrestrictedMoment
  apply sum_congr rfl
  intro labels _
  by_cases h : GiantTwoSidedStaticLabels C π τ aux labels
  · simp only [h, ite_true, giantTwoSidedRootScalar_fourier]
    ring
  · simp only [h, ite_false]

theorem giantTwoSidedIndependentMoment_norm_le (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    {B : ℝ} (hB : ∀ θ : AddCircle (1 : ℝ),
      ‖giantTwoSidedIndependentUnrestrictedMoment C π τ aux step q ζ
        (fun i => giantTwoSidedFourierCoefficient θ (step i) (K i))‖ ≤ B) :
    ‖giantTwoSidedIndependentMoment C π τ aux step q ζ K‖ ≤ B := by
  rw [giantTwoSidedIndependentMoment_fourier]
  have h := norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle) (Filter.Eventually.of_forall fun θ =>
      (giantTwoSidedIndependentFourier_twisted C π τ aux step q ζ K θ).symm ▸ hB θ)
  simpa only [probReal_univ, mul_one] using h

end
end ArtinMatthews
