module

public import ArtinMatthews.CubicThetaWeightedTransform
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic
public import OAI.NumberTheory.DirichletL.Hecke.ThetaSeries
public import OAI.NumberTheory.DirichletL.LatticeSummability


set_option backward.privateInPublic true
@[expose] public section

/-!+# Uniform vanishing at the zero cusp

Dominated convergence along `UpperHalfPlane.atImInfty` controls arbitrary real
parts. Combined with the actual weighted Poisson identity, this proves the
weight-one normalized zero-cusp limit. It does not assert a modular law or
vanishing at all other cusps.
-/

noncomputable section
open scoped BigOperators Topology
open Complex UpperHalfPlane Filter
open OAI OAI.SevenEighths

namespace ArtinMatthews

theorem eisensteinGaussianParameter_norm (τ : ℍ) (z : ℤ × ℤ) :
    ‖eisensteinComplexGaussian (eisensteinGaussianParameter τ) z‖ =
      Real.exp (-2 * Real.pi * τ.im * EisensteinTheta.normForm z.1 z.2) := by
  unfold eisensteinComplexGaussian eisensteinGaussianParameter EisensteinTheta.normForm
  rw [Complex.norm_exp]
  congr 1
  simp [mul_re, mul_im, pow_two]
  ring_nf
  simp

theorem eisensteinGaussian_tendsto_zero (z : ℤ × ℤ) (hz : z ≠ (0, 0)) :
    Tendsto (fun τ : ℍ => eisensteinComplexGaussian (eisensteinGaussianParameter τ) z)
      atImInfty (𝓝 0) := by
  have hq : 0 < EisensteinTheta.normForm z.1 z.2 := by
    apply lt_of_le_of_ne (LatticeSummability.normForm_nonneg _ _)
    intro h
    apply hz
    have hh := (LatticeSummability.normForm_eq_zero_iff _ _).mp h.symm
    simpa only [Int.cast_eq_zero, Prod.ext_iff] using hh
  have him : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  have hmul := him.const_mul_atTop (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
    Real.pi_pos) hq)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [eisensteinGaussianParameter_norm, Function.comp_def,
    neg_mul, mul_assoc, mul_comm (EisensteinTheta.normForm z.1 z.2) (UpperHalfPlane.im _)] using he

/-- Every bounded lattice weight has its zero coefficient as its limit at
imaginary infinity, uniformly over the real part. -/
theorem tendsto_eisensteinBoundedWeight (w : ℤ × ℤ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ z, ‖w z‖ ≤ C) :
    Tendsto (fun τ : ℍ => ∑' z : ℤ × ℤ,
      w z * eisensteinComplexGaussian (eisensteinGaussianParameter τ) z)
      atImInfty (𝓝 (w (0, 0))) := by
  classical
  have hsum : Summable (fun z : ℤ × ℤ => C * ‖eisensteinComplexGaussian 2 z‖) :=
    (eisensteinComplexGaussian_summable (a := 2) (by norm_num)).norm.mul_left C
  have hpoint (z : ℤ × ℤ) : Tendsto
      (fun τ : ℍ => w z * eisensteinComplexGaussian (eisensteinGaussianParameter τ) z)
      atImInfty (𝓝 (if z = (0, 0) then w z else 0)) := by
    by_cases hz : z = (0, 0)
    · subst z
      simp [eisensteinComplexGaussian]
    · simpa only [hz, ↓reduceIte, mul_zero] using
        tendsto_const_nhds.mul (eisensteinGaussian_tendsto_zero z hz)
  have hbound : ∀ᶠ τ : ℍ in atImInfty, ∀ z : ℤ × ℤ,
      ‖w z * eisensteinComplexGaussian (eisensteinGaussianParameter τ) z‖ ≤
        C * ‖eisensteinComplexGaussian 2 z‖ := by
    have him : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
    filter_upwards [him.eventually_ge_atTop 1] with τ hτ
    intro z
    have hnorm : ‖eisensteinComplexGaussian (eisensteinGaussianParameter τ) z‖ ≤
        ‖eisensteinComplexGaussian 2 z‖ := by
      rw [eisensteinGaussianParameter_norm]
      unfold eisensteinComplexGaussian
      rw [Complex.norm_exp, Real.exp_le_exp]
      have hq := LatticeSummability.normForm_nonneg (z.1 : ℝ) (z.2 : ℝ)
      have hm := mul_le_mul_of_nonneg_right hτ
        (mul_nonneg (show 0 ≤ 2 * Real.pi by positivity) hq)
      simp [EisensteinTheta.normForm, mul_re, mul_im, pow_two] at *
      nlinarith
    rw [norm_mul]
    exact mul_le_mul (hw z) hnorm (norm_nonneg _) hC
  have h := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  simpa using h

theorem tendsto_eisensteinWeightedGaussian {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) :
    Tendsto (fun τ : ℍ => eisensteinWeightedGaussian w (eisensteinGaussianParameter τ))
      atImInfty (𝓝 (w (0, 0))) := by
  have h := tendsto_eisensteinBoundedWeight (HeckeTheta.periodicCoeff w)
    (C := ∑ r, ‖w r‖) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (HeckeTheta.norm_periodicCoeff_le w)
  simpa only [eisensteinWeightedGaussian, HeckeTheta.periodicCoeff_zero] using h

/-- The dual Gaussian sum appearing in the actual periodic Poisson formula. -/
def eisensteinDualTheta {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (τ : ℍ) : ℂ :=
  ∑' z : ℤ × ℤ, eisensteinResidueFourier w z *
    eisensteinComplexGaussian (eisensteinGaussianParameter τ) (z.1, -z.2)

/-- The constant term of the dual theta sum is the sum of the original
finite residue weights, uniformly in the real part. -/
theorem tendsto_eisensteinDualTheta {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    Tendsto (eisensteinDualTheta w) atImInfty (𝓝 (∑ r, w r)) := by
  have h := tendsto_eisensteinBoundedWeight
    (fun z : ℤ × ℤ => eisensteinResidueFourier w (z.1, -z.2))
    (C := ∑ r, ‖w r‖) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun _ => eisensteinResidueFourier_norm_le w _)
  have hreindex (τ : ℍ) :
      (∑' z : ℤ × ℤ, eisensteinResidueFourier w (z.1, -z.2) *
        eisensteinComplexGaussian (eisensteinGaussianParameter τ) z) =
      eisensteinDualTheta w τ := by
    have he := (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq
      (fun z : ℤ × ℤ => eisensteinResidueFourier w z *
        eisensteinComplexGaussian (eisensteinGaussianParameter τ) (z.1, -z.2))
    convert he using 1
    · apply tsum_congr
      rintro ⟨k, l⟩
      simp
    · rfl
  have hh : Tendsto (eisensteinDualTheta w) atImInfty
      (𝓝 (eisensteinResidueFourier w (0, 0))) := by
    simpa only [neg_zero] using h.congr hreindex
  simpa [eisensteinResidueFourier, RankTwoEisShift.dualPhase] using hh

/-- The Fricke map for the period-dependent level `3 N²`. -/
def eisensteinPeriodFricke (N : ℕ) [NeZero N] (τ : ℍ) : ℍ :=
  ⟨-1 / (3 * (N : ℂ) ^ 2 * (τ : ℂ)), by
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have heq : (-1 : ℂ) / (3 * (N : ℂ) ^ 2 * τ) =
        (((1 / (N : ℝ) ^ 2) : ℝ) : ℂ) * (eisensteinFricke τ : ℂ) := by
      unfold eisensteinFricke
      push_cast
      ring
    rw [heq]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (show (0 : ℝ) < 1 / (N : ℝ) ^ 2 by positivity)
      (eisensteinFricke τ).im_pos⟩

theorem eisensteinPeriodFricke_parameter (N : ℕ) [NeZero N] (τ : ℍ) :
    eisensteinGaussianParameter (eisensteinPeriodFricke N τ) * (N : ℂ) ^ 2 =
      4 / (3 * eisensteinGaussianParameter τ) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold eisensteinGaussianParameter eisensteinPeriodFricke
  field_simp
  simp [Complex.I_sq]
  ring

/-- Exact normalized Fricke expression for the actual nonprincipal Hecke
theta series in terms of its finite Fourier weight. -/
theorem heckeTheta_periodFricke_normalized (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) (τ : ℍ) :
    heckeTheta χ (eisensteinPeriodFricke χ.period τ) / (τ : ℂ) =
      (-Complex.I / (2 * (Real.sqrt 3 : ℂ))) *
        eisensteinDualTheta (HeckeFamily.coefficients χ) τ := by
  have ha : eisensteinGaussianParameter τ ≠ 0 := by
    intro h
    have hr := eisensteinGaussianParameter_re τ
    simp [h] at hr
  have hinv : 4 / (3 * (4 / (3 * eisensteinGaussianParameter τ))) =
      eisensteinGaussianParameter τ := by field_simp
  have h := heckeTheta_weighted_poisson χ hχ (eisensteinPeriodFricke χ.period τ)
  rw [eisensteinPeriodFricke_parameter, hinv] at h
  change 6 * heckeTheta χ (eisensteinPeriodFricke χ.period τ) =
    (2 / ((Real.sqrt 3 : ℂ) * (4 / (3 * eisensteinGaussianParameter τ)))) *
      eisensteinDualTheta (HeckeFamily.coefficients χ) τ at h
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)).ne'
  calc
    _ = (6 * heckeTheta χ (eisensteinPeriodFricke χ.period τ)) /
        (6 * (τ : ℂ)) := by ring
    _ = _ := by
      rw [h]
      unfold eisensteinGaussianParameter
      field_simp [τ.ne_zero, hs]
      ring

/-- The normalized actual Hecke theta function vanishes at the zero cusp
along the full upper-half-plane filter, with no restriction on real parts. -/
theorem tendsto_heckeTheta_periodFricke_zero (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) :
    Tendsto (fun τ : ℍ =>
      heckeTheta χ (eisensteinPeriodFricke χ.period τ) / (τ : ℂ))
      atImInfty (𝓝 0) := by
  have hd := tendsto_eisensteinDualTheta (HeckeFamily.coefficients χ)
  rw [HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ] at hd
  have h := hd.const_mul (-Complex.I / (2 * (Real.sqrt 3 : ℂ)))
  simpa only [heckeTheta_periodFricke_normalized χ hχ, mul_zero] using h

end ArtinMatthews
