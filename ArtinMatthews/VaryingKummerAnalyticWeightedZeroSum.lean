module

public import ArtinMatthews.VaryingKummerAnalyticComplexZeroPole
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute zero-sum convergence from an actual positive pole sum. Quadratic
vertical decay suffices, with the zero multiplicities retained exactly. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth
open ArtinMatthews.ReusedGrowth Complex
open scoped BigOperators
noncomputable section

lemma reciprocal_two_re_lower {ρ : ℂ} (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1) :
    1/(4*(1+|ρ.im|)^2) ≤ (1/((2 : ℂ)-ρ)).re := by
  have hr : 1 ≤ 2-ρ.re := by linarith
  have hnorm : 0 < Complex.normSq ((2 : ℂ)-ρ) := by
    rw [Complex.normSq_pos]
    intro H
    have := congrArg Complex.re H
    norm_num at this
    linarith
  have hbound : Complex.normSq ((2 : ℂ)-ρ) ≤ 4*(1+|ρ.im|)^2 := by
    norm_num [Complex.normSq_apply]
    nlinarith [sq_abs ρ.im, abs_nonneg ρ.im, sq_nonneg ρ.re]
  have H : 1/(4*(1+|ρ.im|)^2) ≤ ((2 : ℂ)-ρ).re / Complex.normSq ((2 : ℂ)-ρ) := by
    calc
      _ ≤ 1/Complex.normSq ((2 : ℂ)-ρ) :=
        one_div_le_one_div_of_le hnorm hbound
      _ ≤ _ := div_le_div_of_nonneg_right (by simpa using hr) hnorm.le
  simpa only [one_div, Complex.inv_re] using H

lemma weighted_zero_norm_le_pole {f Φ : ℂ → ℂ} {C : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hC : 0 ≤ C)
    (hstrip : ∀ ρ, f ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1)
    (hΦ : ∀ ρ, f ρ = 0 → ‖Φ ρ‖ ≤ C/(1+|ρ.im|)^2) (ρ : ℂ) :
    ‖(zeroMultiplicity f ρ : ℂ)*Φ ρ‖ ≤ 4*C*complexZeroPole f 2 ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [hm, complexZeroPole]
  have hρ := (zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm
  have hnn : 0 ≤ (zeroMultiplicity f ρ : ℝ) := by
    exact_mod_cast zeroMultiplicity_nonneg hf ρ
  have hkernel := reciprocal_two_re_lower (hstrip ρ hρ).1 (hstrip ρ hρ).2
  have hΦ' : ‖Φ ρ‖ ≤ 4*C*(1/((2 : ℂ)-ρ)).re := by
    calc
      _ ≤ C/(1+|ρ.im|)^2 := hΦ ρ hρ
      _ = (4*C)*(1/(4*(1+|ρ.im|)^2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel (by positivity)
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hnn]
  have H := mul_le_mul_of_nonneg_left hΦ' hnn
  simpa only [complexZeroPole, mul_left_comm] using H

theorem weighted_zero_summable_and_bound {f Φ : ℂ → ℂ} {C : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z) (hC : 0 ≤ C)
    (hstrip : ∀ ρ, f ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1)
    (hΦ : ∀ ρ, f ρ = 0 → ‖Φ ρ‖ ≤ C/(1+|ρ.im|)^2) :
    Summable (fun ρ => (zeroMultiplicity f ρ : ℂ)*Φ ρ) ∧
    (∑' ρ, ‖(zeroMultiplicity f ρ : ℂ)*Φ ρ‖) ≤
      4*C*(logDeriv f 2).re := by
  have HS := hasSum_complexZeroPole hf h0 hg hfe (fun ρ hρ => (hstrip ρ hρ).2)
    (s := (2 : ℂ)) (by norm_num)
  have Hmajor := HS.summable.mul_left (4*C)
  have Hbound := weighted_zero_norm_le_pole hf h0 hC hstrip hΦ
  have Hnorm : Summable (fun ρ => ‖(zeroMultiplicity f ρ : ℂ)*Φ ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) Hbound Hmajor
  refine ⟨Hnorm.of_norm,?_⟩
  calc
    _ ≤ ∑' ρ, 4*C*complexZeroPole f 2 ρ := Hnorm.tsum_le_tsum Hbound Hmajor
    _ = 4*C*(logDeriv f 2).re := by rw [tsum_mul_left, HS.tsum_eq]

end
end OAI.PrimeDegreePackets.AnalyticGrowth
