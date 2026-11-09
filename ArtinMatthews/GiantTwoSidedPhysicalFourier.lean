module

public import ArtinMatthews.GiantTwoSidedFourierTwist
public import ArtinMatthews.GiantTwoSidedRootMoment


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier inversion applies directly to the original finite physical
path sum, including zero coefficients on every unsupported path. -/
namespace ArtinMatthews
open MeasureTheory Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell n : ℕ}

omit [DecidableEq J] in
theorem giantTwoSidedPhysicalPath_fourier_product (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    {Z : Finset ℕ} (s : Fin (n + 1) → GiantTwoSidedEndpointState P (k + ell) Z)
    (θ : AddCircle (1 : ℝ)) :
    (∏ i, giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i)
      (giantTwoSidedFourierCoefficient θ (step i) (K i))
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) =
    (∏ i, giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) *
      fourier ((s (Fin.last n)).val.1.val - (s 0).val.1.val : ℤ) θ := by
  by_cases hs : ∀ i, GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)
  · simp_rw [giantTwoSidedPhysicalCoefficient_fourier]
    rw [prod_mul_distrib]
    have hp := giantTwoSidedPatternPath_position s π τ aux step hs (Fin.last n)
    have hd : giantTwoSidedPathOffset (giantTwoSidedPatternPathIncrement s π aux step)
        (Fin.last n) = ((s (Fin.last n)).val.1.val : ℤ) - (s 0).val.1.val := by
      omega
    change _ * (∏ i, fourier (giantTwoSidedPatternPathIncrement s π aux step i) θ) = _
    rw [← giantTwoSidedFourier_path_product, hd]
  · rw [giantTwoSidedPhysicalPath_product_zero π τ aux step q ζ
        (fun i => giantTwoSidedFourierCoefficient θ (step i) (K i)) s hs,
      giantTwoSidedPhysicalPath_product_zero π τ aux step q ζ K s hs, zero_mul]

def giantTwoSidedPhysicalUnrestrictedMoment (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (I Z : Finset ℕ) : ℂ :=
  ∑ s : Fin (n + 1) → GiantTwoSidedEndpointState P (k + ell) Z,
    if (s 0).val.1.val ∈ I then
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell) : ℂ) *
        ∏ i, giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
          (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
          (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)
    else 0

theorem giantTwoSidedPhysicalFourier_continuous (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (I Z : Finset ℕ) :
    Continuous (fun θ : AddCircle (1 : ℝ) =>
      giantTwoSidedPhysicalUnrestrictedMoment C π τ aux step q ζ
        (fun i => giantTwoSidedFourierCoefficient θ (step i) (K i)) I Z) := by
  unfold giantTwoSidedPhysicalUnrestrictedMoment
  simp_rw [giantTwoSidedPhysicalPath_fourier_product]
  apply continuous_finsetSum
  intro s _
  by_cases hs : (s 0).val.1.val ∈ I
  · simp only [hs, ite_true]
    exact continuous_const.mul (continuous_const.mul (fourier _).continuous)
  · simp only [hs, ite_false]
    exact continuous_const

theorem giantTwoSidedPhysicalMoment_fourier (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (I Z : Finset ℕ) :
    giantTwoSidedPhysicalMoment C π τ aux step q ζ K I Z =
      ∫ θ : AddCircle (1 : ℝ),
        giantTwoSidedPhysicalUnrestrictedMoment C π τ aux step q ζ
          (fun i => giantTwoSidedFourierCoefficient θ (step i) (K i)) I Z
            ∂AddCircle.haarAddCircle := by
  symm
  unfold giantTwoSidedPhysicalUnrestrictedMoment
  simp_rw [giantTwoSidedPhysicalPath_fourier_product]
  rw [integral_finsetSum]
  · unfold giantTwoSidedPhysicalMoment
    apply sum_congr rfl
    intro s _
    by_cases hs : (s 0).val.1.val ∈ I
    · simp only [hs, ite_true]
      rw [integral_const_mul, integral_const_mul, giantTwoSidedFourier_integral]
      have hr : (((s (Fin.last n)).val.1.val : ℤ) - (s 0).val.1.val = 0) ↔
          (s (Fin.last n)).val.1.val = (s 0).val.1.val := by omega
      simp only [hr]
      split_ifs <;> simp
    · simp only [hs, ite_false, integral_zero]
  · intro s _
    by_cases hs : (s 0).val.1.val ∈ I
    · simp only [hs, ite_true]
      exact (continuous_const.mul (continuous_const.mul (fourier _).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · simp only [hs, ite_false]
      exact integrable_const (0 : ℂ)

end
end ArtinMatthews
