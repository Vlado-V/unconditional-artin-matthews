module

public import ArtinMatthews.SpectralPrincipalDecayWeight
public import Mathlib.Analysis.Complex.Basic
public import ArtinMatthews.SpectralPrincipalWeightedCrossFinite
public import ArtinMatthews.SpectralPrincipalWeightedFinite


set_option backward.privateInPublic true
@[expose] public section

/-! Exhaustion by arbitrary finite subsets gives genuine summability,
without an enumeration or a spectral cardinality hypothesis. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem spectralPrincipal_weighted_summable
    {α : Type*} (τ f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    {B C Z : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hZ : 1 ≤ Z)
    (hcut : ∀ (u : Finset α) (R : ℝ), 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|τ j| ≤ R), f i) ≤ C*(R^2+B*R)) :
    Summable (fun i => f i*spectralPrincipalDecayWeight Z (τ i)) ∧
      (∑' i, f i*spectralPrincipalDecayWeight Z (τ i)) ≤ 8*C*(Z^2+B*Z) := by
  have hn (i : α) : 0 ≤ f i*spectralPrincipalDecayWeight Z (τ i) :=
    mul_nonneg (hf i) (spectralPrincipalDecayWeight_nonneg Z (τ i))
  have hb (u : Finset α) :
      (∑ i ∈ u, f i*spectralPrincipalDecayWeight Z (τ i)) ≤ 8*C*(Z^2+B*Z) :=
    spectralPrincipal_weighted_finset u τ f (fun i _ => hf i) hB hC hZ (hcut u)
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

theorem spectralPrincipal_cross_summable
    {α : Type*} (τ f g : α → ℝ) (h : α → ℂ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    {H Z B₁ B₂ C₁ C₂ : ℝ} (hH : 0 ≤ H) (hZ : 1 ≤ Z)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hbound : ∀ i, ‖h i‖ ≤
      H*spectralPrincipalDecayWeight Z (τ i)*Real.sqrt (f i)*Real.sqrt (g i))
    (hcut₁ : ∀ (u : Finset α) (R : ℝ), 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|τ j| ≤ R), f i) ≤ C₁*(R^2+B₁*R))
    (hcut₂ : ∀ (u : Finset α) (R : ℝ), 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|τ j| ≤ R), g i) ≤ C₂*(R^2+B₂*R)) :
    Summable (fun i => ‖h i‖) ∧ Summable h ∧
      ‖∑' i, h i‖ ≤ H*Real.sqrt (8*C₁*(Z^2+B₁*Z))*Real.sqrt (8*C₂*(Z^2+B₂*Z)) := by
  have hb (u : Finset α) :
      (∑ i ∈ u, ‖h i‖) ≤ H*Real.sqrt (8*C₁*(Z^2+B₁*Z))*Real.sqrt (8*C₂*(Z^2+B₂*Z)) :=
    spectralPrincipal_cross_finset u τ f g h (fun i _ => hf i) (fun i _ => hg i)
      hH hZ hB₁ hB₂ hC₁ hC₂ (fun i _ => hbound i) (hcut₁ u) (hcut₂ u)
  have hs : Summable (fun i => ‖h i‖) := summable_of_sum_le (fun _ => norm_nonneg _) hb
  refine ⟨hs,hs.of_norm,?_⟩
  exact (norm_tsum_le_tsum_norm hs).trans (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hb)

end
end ArtinMatthews
