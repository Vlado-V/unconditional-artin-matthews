module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Complex
open scoped Topology
noncomputable section

/-- Absolute Mellin interchange for a norm-indexed Dirichlet series.
The profile is evaluated with the same chosen inversion line. -/
theorem quadraticHeckeNormSmoothing_contour {ι : Type} [Countable ι]
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) (a : ι → ℂ)
    (H : ℂ → ℂ) (σ : ℝ)
    (hHc : Continuous (fun t : ℝ => H ((σ : ℂ) + (t : ℂ) * I)))
    (hHi : Integrable (fun t : ℝ => H ((σ : ℂ) + (t : ℂ) * I)))
    (ha : Summable (fun i => ‖a i‖ * q i ^ (-σ)))
    {X : ℝ} (hX : 0 < X) :
    (∑' i, a i * mellinInv σ H (q i / X)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (X : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) * H ((σ : ℂ) + (t : ℂ) * I) *
          (∑' i, a i * (q i : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) := by
  let s (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  let f (i : ι) (t : ℝ) : ℂ := a i * ((q i / X : ℝ) : ℂ) ^ (-s t) * H (s t)
  let c (i : ι) : ℝ := ‖a i‖ * (q i / X) ^ (-σ)
  have hpos (i : ι) : 0 < q i / X := div_pos (hq i) hX
  have hnorm (i : ι) (t : ℝ) : ‖f i t‖ = c i * ‖H (s t)‖ := by
    unfold f c
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hpos i), Complex.neg_re]
    have hs : (s t).re = σ := by simp [s]
    rw [hs]
  have hc (i : ι) : 0 ≤ c i := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hpos i).le _)
  have hcs : Summable c := by
    apply (ha.div_const (X ^ (-σ))).congr
    intro i
    change _ = ‖a i‖ * (q i / X) ^ (-σ)
    rw [Real.div_rpow (hq i).le hX.le, mul_div_assoc]
  have hF (i : ι) : Integrable (f i) := by
    have hcont : Continuous (f i) := by
      have hb : ((q i / X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos i).ne'
      have hp : Continuous (fun t => ((q i / X : ℝ) : ℂ) ^ (-s t)) := by
        simp only [Complex.cpow_def_of_ne_zero hb, s]
        fun_prop
      exact (hp.const_mul (a i)).mul hHc
    exact (hHi.norm.const_mul (c i)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ (fun t => (hnorm i t).le))
  have hS : Summable (fun i => ∫ t : ℝ, ‖f i t‖) := by
    apply (hcs.mul_right (∫ t : ℝ, ‖H (s t)‖)).congr
    intro i
    simp only [hnorm, integral_const_mul]
  have hp (i : ι) :
      a i * mellinInv σ H (q i / X) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, f i t) := by
    simp only [mellinInv, Complex.real_smul, smul_eq_mul, f, ← mul_assoc, ← integral_const_mul, s]
    congr 1
    rw [mul_comm]
  simp_rw [hp, tsum_mul_left, integral_tsum_of_summable_integral_norm hF hS]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  change a i * ((q i / X : ℝ) : ℂ) ^ (-s t) * H (s t) =
    (X : ℂ) ^ (s t) * H (s t) * (a i * (q i : ℂ) ^ (-s t))
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (hq i).le hX.le, Complex.cpow_neg (X : ℂ)]
  have hpow : (X : ℂ) ^ (s t) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  field_simp

end
end ArtinMatthews
