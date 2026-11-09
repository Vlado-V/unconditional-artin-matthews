module

public import ArtinMatthews.GiantTwoSidedReturnFourier
public import ArtinMatthews.GiantTwoSidedResiduePatternKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The return character factors into the actual signed dilation on
each edge. Twisting the coefficient preserves all original factors. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

def giantTwoSidedFourierCoefficient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)}
    (θ : AddCircle (1 : ℝ)) (step : ℤ)
    (K : GiantTwoSidedPatternCoefficient P C ell) :
    GiantTwoSidedPatternCoefficient P C ell :=
  fun b c a => K b c a *
    fourier (step * (giantTwoSidedPatternDilation C b a : ℤ)) θ

theorem giantTwoSidedFourierCoefficient_norm {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)}
    (θ : AddCircle (1 : ℝ)) (step : ℤ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (b c : MarkedPhysicalMarking P (k + ell)) (a : GiantTwoSidedPatternAuxiliary P C) :
    ‖giantTwoSidedFourierCoefficient θ step K b c a‖ = ‖K b c a‖ := by
  rw [giantTwoSidedFourierCoefficient, norm_mul, giantTwoSidedFourier_norm, mul_one]

theorem giantTwoSidedRootScalar_fourier {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (labels : Fin (n + 1) → MarkedPhysicalMarking P (k + ell))
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (θ : AddCircle (1 : ℝ)) :
    giantTwoSidedRootScalar C labels π τ aux ζ
        (fun i => giantTwoSidedFourierCoefficient θ (step i) (K i)) =
      giantTwoSidedRootScalar C labels π τ aux ζ K *
        fourier (giantTwoSidedPathOffset
          (giantTwoSidedLabelIncrement C labels π aux step) (Fin.last n)) θ := by
  let F (i : Fin n) :=
    (giantTwoSidedPatternAuxiliaryMass (aux i) : ℂ) *
      (giantTwoSidedPatternFreshMass P (C i) ell : ℂ) *
      K i (giantTwoSidedPermuteLabels (π i) (labels i.castSucc))
        (giantTwoSidedPermuteLabels (τ i) (labels i.succ)) (aux i) *
      (giantTwoSidedPatternDilation (C i)
        (giantTwoSidedPermuteLabels (π i) (labels i.castSucc)) (aux i) : ℂ) ^
          ((ζ i : ℂ) * Complex.I)
  have hp : (∏ i : Fin n,
      (giantTwoSidedPatternAuxiliaryMass (aux i) : ℂ) *
        (giantTwoSidedPatternFreshMass P (C i) ell : ℂ) *
        giantTwoSidedFourierCoefficient θ (step i) (K i)
          (giantTwoSidedPermuteLabels (π i) (labels i.castSucc))
          (giantTwoSidedPermuteLabels (τ i) (labels i.succ)) (aux i) *
        (giantTwoSidedPatternDilation (C i)
          (giantTwoSidedPermuteLabels (π i) (labels i.castSucc)) (aux i) : ℂ) ^
            ((ζ i : ℂ) * Complex.I)) =
        (∏ i, F i) * ∏ i, fourier (giantTwoSidedLabelIncrement C labels π aux step i) θ := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    dsimp only [F, giantTwoSidedFourierCoefficient, giantTwoSidedLabelIncrement]
    ring
  unfold giantTwoSidedRootScalar
  rw [hp, ← giantTwoSidedFourier_path_product]
  dsimp only [F]
  ring

theorem giantTwoSidedPhysicalCoefficient_fourier {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)}
    (θ : AddCircle (1 : ℝ)) (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k + ell) Z)
    (t : GiantTwoSidedEndpointState P (k + ell) Z')
    (a : GiantTwoSidedPatternAuxiliary P C) :
    giantTwoSidedPatternPhysicalCoefficient step q ζ
        (giantTwoSidedFourierCoefficient θ step K) s t a =
      giantTwoSidedPatternPhysicalCoefficient step q ζ K s t a *
        fourier (step * (giantTwoSidedPatternDilation C s.val.2 a : ℤ)) θ := by
  unfold giantTwoSidedPatternPhysicalCoefficient giantTwoSidedFourierCoefficient
  split_ifs <;> ring

theorem giantTwoSidedResidueCoefficient_fourier {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)}
    (θ : AddCircle (1 : ℝ)) (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (s t : GiantTwoSidedResidueState P (k + ell))
    (a : GiantTwoSidedPatternAuxiliary P C) :
    giantTwoSidedResiduePatternCoefficient step q ζ
        (giantTwoSidedFourierCoefficient θ step K) s t a =
      giantTwoSidedResiduePatternCoefficient step q ζ K s t a *
        fourier (step * (giantTwoSidedPatternDilation C s.val.2 a : ℤ)) θ := by
  unfold giantTwoSidedResiduePatternCoefficient giantTwoSidedFourierCoefficient
  split_ifs <;> ring

end
end ArtinMatthews
