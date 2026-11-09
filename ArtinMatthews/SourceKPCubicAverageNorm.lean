module

public import ArtinMatthews.SourceKPCompactGenuineL2
public import Mathlib.Algebra.Order.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Finite Cauchy–Schwarz for the actual cubic character weights. -/
namespace ArtinMatthews
open NumberField
open scoped BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] sourceKPCompactCubicCenter_fintype

theorem sourceKPCubicWeightedAverage_norm_sq_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (v : rootsOfUnity 3 K → V) :
    ‖(3 : ℂ)⁻¹ • ∑ z : rootsOfUnity 3 K,
        (sourceKPAdelicCentralComplex K hζ z : ℂ) • v z‖ ^ 2 ≤
      (3 : ℝ)⁻¹ * ∑ z : rootsOfUnity 3 K, ‖v z‖ ^ 2 := by
  let u : rootsOfUnity 3 K → V := fun z => (sourceKPAdelicCentralComplex K hζ z : ℂ) • v z
  have htriangle : ‖∑ z, u z‖ ≤ ∑ z, ‖v z‖ := by
    simpa only [u, norm_smul, sourceKPAdelicCentralComplex_norm, one_mul] using
      norm_sum_le Finset.univ u
  have hcs : (∑ z, ‖v z‖) ^ 2 ≤ (3 : ℝ) * ∑ z, ‖v z‖ ^ 2 := by
    simpa only [Finset.card_univ, sourceKPCubicCenter_card_three K hζ, Nat.cast_ofNat] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun z => ‖v z‖))
  have hsq := (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans hcs
  change ‖(3 : ℂ)⁻¹ • ∑ z, u z‖ ^ 2 ≤ _
  rw [norm_smul, norm_inv, Complex.norm_ofNat, mul_pow]
  calc
    _ ≤ ((3 : ℝ)⁻¹) ^ 2 * ((3 : ℝ) * ∑ z, ‖v z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

end
end ArtinMatthews
