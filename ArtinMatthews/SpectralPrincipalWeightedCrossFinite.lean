module

public import ArtinMatthews.SpectralPrincipalWeightedFinite
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted Cauchy--Schwarz for finite principal spectral cross terms. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem spectralPrincipal_cross_finset_of_moments
    {α : Type*} (u : Finset α) (τ f g : α → ℝ) (h : α → ℂ)
    (hf : ∀ i ∈ u, 0 ≤ f i) (hg : ∀ i ∈ u, 0 ≤ g i)
    {H Z M₁ M₂ : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ i ∈ u, ‖h i‖ ≤
      H*spectralPrincipalDecayWeight Z (τ i)*Real.sqrt (f i)*Real.sqrt (g i))
    (h₁ : (∑ i ∈ u, f i*spectralPrincipalDecayWeight Z (τ i)) ≤ M₁)
    (h₂ : (∑ i ∈ u, g i*spectralPrincipalDecayWeight Z (τ i)) ≤ M₂) :
    (∑ i ∈ u, ‖h i‖) ≤ H*Real.sqrt M₁*Real.sqrt M₂ := by
  let p (i : α) := Real.sqrt (f i*spectralPrincipalDecayWeight Z (τ i))
  let q (i : α) := Real.sqrt (g i*spectralPrincipalDecayWeight Z (τ i))
  have hpq (i : α) (hi : i ∈ u) :
      spectralPrincipalDecayWeight Z (τ i)*Real.sqrt (f i)*Real.sqrt (g i) = p i*q i := by
    dsimp [p,q]
    rw [Real.sqrt_mul (hf i hi), Real.sqrt_mul (hg i hi)]
    symm
    calc
      _ = (Real.sqrt (f i)*Real.sqrt (g i)) *
          (Real.sqrt (spectralPrincipalDecayWeight Z (τ i)))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (spectralPrincipalDecayWeight_nonneg Z (τ i))]; ring
  have hp : (∑ i ∈ u, (p i)^2) = ∑ i ∈ u, f i*spectralPrincipalDecayWeight Z (τ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (mul_nonneg (hf i hi) (spectralPrincipalDecayWeight_nonneg Z (τ i)))
  have hq : (∑ i ∈ u, (q i)^2) = ∑ i ∈ u, g i*spectralPrincipalDecayWeight Z (τ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (mul_nonneg (hg i hi) (spectralPrincipalDecayWeight_nonneg Z (τ i)))
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt u p q
  rw [hp,hq] at hcs
  calc
    _ ≤ ∑ i ∈ u, H*(p i*q i) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ H*(spectralPrincipalDecayWeight Z (τ i)*Real.sqrt (f i)*Real.sqrt (g i)) := by
          simpa only [mul_assoc] using hbound i hi
        _ = _ := by rw [hpq i hi]
    _ = H*(∑ i ∈ u, p i*q i) := (Finset.mul_sum _ _ _).symm
    _ ≤ H*(Real.sqrt (∑ i ∈ u, f i*spectralPrincipalDecayWeight Z (τ i)) *
        Real.sqrt (∑ i ∈ u, g i*spectralPrincipalDecayWeight Z (τ i))) :=
      mul_le_mul_of_nonneg_left hcs hH
    _ ≤ H*(Real.sqrt M₁*Real.sqrt M₂) := by
      apply mul_le_mul_of_nonneg_left _ hH
      exact mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem spectralPrincipal_cross_finset
    {α : Type*} (u : Finset α) (τ f g : α → ℝ) (h : α → ℂ)
    (hf : ∀ i ∈ u, 0 ≤ f i) (hg : ∀ i ∈ u, 0 ≤ g i)
    {H Z B₁ B₂ C₁ C₂ : ℝ} (hH : 0 ≤ H) (hZ : 1 ≤ Z)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hbound : ∀ i ∈ u, ‖h i‖ ≤
      H*spectralPrincipalDecayWeight Z (τ i)*Real.sqrt (f i)*Real.sqrt (g i))
    (hcut₁ : ∀ R : ℝ, 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|τ j| ≤ R), f i) ≤ C₁*(R^2+B₁*R))
    (hcut₂ : ∀ R : ℝ, 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|τ j| ≤ R), g i) ≤ C₂*(R^2+B₂*R)) :
    (∑ i ∈ u, ‖h i‖) ≤
      H*Real.sqrt (8*C₁*(Z^2+B₁*Z))*Real.sqrt (8*C₂*(Z^2+B₂*Z)) :=
  spectralPrincipal_cross_finset_of_moments u τ f g h hf hg hH hbound
    (spectralPrincipal_weighted_finset u τ f hf hB₁ hC₁ hZ hcut₁)
    (spectralPrincipal_weighted_finset u τ g hg hB₂ hC₂ hZ hcut₂)

end
end ArtinMatthews
