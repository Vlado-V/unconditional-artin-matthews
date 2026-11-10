module

public import ArtinMatthews.SpectralPrincipalWeightedMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The weighted principal estimate for a literal finite subset. The
only spectral input is its true filtered cutoff-mass bound. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped BigOperators
noncomputable section

theorem spectralPrincipal_weighted_finset
    {α : Type*} (u : Finset α) (τ f : α → ℝ) (hf : ∀ i ∈ u, 0 ≤ f i)
    {B C Z : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hZ : 1 ≤ Z)
    (hcut : ∀ R : ℝ, 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|τ j| ≤ R), f i) ≤ C*(R^2+B*R)) :
    (∑ i ∈ u, f i*spectralPrincipalDecayWeight Z (τ i)) ≤ 8*C*(Z^2+B*Z) := by
  classical
  letI : MeasurableSpace α := ⊤
  let ν : Measure α := ∑ i ∈ u, (ENNReal.ofReal (f i)) • Measure.dirac i
  have hτ : Measurable τ := measurable_from_top
  have hm (R : ℝ) (hR : 1 ≤ R) :
      ν (spectralPrincipalCutoff τ R) ≤ ENNReal.ofReal (C*(R^2+B*R)) := by
    have hS := spectralPrincipalCutoff_measurable hτ R
    have hv : ν (spectralPrincipalCutoff τ R) =
        ENNReal.ofReal (∑ i ∈ u.filter (fun j => 1+|τ j| ≤ R), f i) := by
      dsimp only [ν]
      rw [Measure.finsetSum_apply]
      calc
        _ = ∑ i ∈ u, if 1+|τ i| ≤ R then ENNReal.ofReal (f i) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Measure.smul_apply, Measure.dirac_apply' i hS]
          by_cases h : 1+|τ i| ≤ R <;> simp [spectralPrincipalCutoff, h]
        _ = ∑ i ∈ u.filter (fun j => 1+|τ j| ≤ R), ENNReal.ofReal (f i) := by
          rw [Finset.sum_filter]
        _ = _ := (ENNReal.ofReal_sum_of_nonneg
          (fun i hi => hf i (Finset.mem_filter.mp hi).1)).symm
    rw [hv]
    exact ENNReal.ofReal_le_ofReal (hcut R hR)
  have hlin := spectralPrincipalDecayWeight_lintegral_bound ν τ hτ hB hC hZ hm
  have hv : (∫⁻ x, ENNReal.ofReal (spectralPrincipalDecayWeight Z (τ x)) ∂ν) =
      ENNReal.ofReal (∑ i ∈ u, f i*spectralPrincipalDecayWeight Z (τ i)) := by
    dsimp only [ν]
    rw [lintegral_finsetSum_measure]
    calc
      _ = ∑ i ∈ u, ENNReal.ofReal (f i*spectralPrincipalDecayWeight Z (τ i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hd :
            (∫⁻ x, ENNReal.ofReal (spectralPrincipalDecayWeight Z (τ x)) ∂Measure.dirac i) =
              ENNReal.ofReal (spectralPrincipalDecayWeight Z (τ i)) :=
          lintegral_dirac' i (ENNReal.measurable_ofReal.comp
            (spectralPrincipalDecayWeight_measurable hτ Z))
        rw [lintegral_smul_measure, hd, smul_eq_mul]
        exact (ENNReal.ofReal_mul (hf i hi)).symm
      _ = _ := (ENNReal.ofReal_sum_of_nonneg
        (fun i hi => mul_nonneg (hf i hi) (spectralPrincipalDecayWeight_nonneg Z (τ i)))).symm
  rw [hv] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 8*C*(Z^2+B*Z))).mp hlin

end
end ArtinMatthews
