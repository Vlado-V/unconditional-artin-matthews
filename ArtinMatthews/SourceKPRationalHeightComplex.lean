module

public import ArtinMatthews.SourceKPRationalHeightSummability
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex


set_option backward.privateInPublic true
@[expose] public section

/-! The complex height kernel used to majorize the rational open cell
in a right half-plane. All sums are over the actual number field. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem sourceKPRationalHeight_rpow_summable {r : ℝ}
    (hr : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ r) :
    Summable (fun x : K => Height.mulHeight₁ x ^ (-r)) := by
  apply Summable.of_nonneg_of_le (fun x => Real.rpow_nonneg (Height.mulHeight₁_nonneg x) _)
    (fun x => ?_) (sourceKPRationalHeight_degree_majorant_summable K)
  calc
    Height.mulHeight₁ x ^ (-r) ≤
        Height.mulHeight₁ x ^ (-(((3*(Module.finrank ℚ K+1) : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (Height.one_le_mulHeight₁ x) (neg_le_neg hr)
    _ = _ := by rw [Real.rpow_neg (Height.mulHeight₁_nonneg x), Real.rpow_natCast]

def sourceKPRationalHeightKernel (s : ℂ) (x : K) : ℂ :=
  Complex.exp (-s * (Real.log (Height.mulHeight₁ x) : ℂ))

theorem sourceKPRationalHeightKernel_norm (s : ℂ) (x : K) :
    ‖sourceKPRationalHeightKernel K s x‖ = Height.mulHeight₁ x ^ (-s.re) := by
  rw [sourceKPRationalHeightKernel, Complex.norm_exp,
    Real.rpow_def_of_pos (Height.mulHeight₁_pos x)]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem sourceKPRationalHeightKernel_summable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ s.re) :
    Summable (sourceKPRationalHeightKernel K s) := by
  apply Summable.of_norm
  simpa only [sourceKPRationalHeightKernel_norm] using sourceKPRationalHeight_rpow_summable K hs

theorem sourceKPRationalHeightKernel_normalized_summable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    Summable (sourceKPRationalHeightKernel K (2*s+1)) := by
  apply sourceKPRationalHeightKernel_summable K
  have he : (2*s+1).re = 2*s.re+1 := by norm_num [Complex.mul_re]
  rwa [he]

end
end ArtinMatthews
