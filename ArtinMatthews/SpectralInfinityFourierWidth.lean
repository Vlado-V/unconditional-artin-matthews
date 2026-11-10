module

public import ArtinMatthews.SpectralGamma0FourierEnergy
public import ArtinMatthews.SpectralCuspConstantTermHeights
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import ArtinMatthews.SpectralCuspTwoCellFourier
public import ArtinMatthews.SpectralCuspWidthCharacters
public import ArtinMatthews.SpectralEisensteinPrimitiveHorocycles
public import ArtinMatthews.SpectralModularDensity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual infinity cusp has period one. Its completed period-N
Fourier coefficients vanish away from the true-width frequencies. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem infinity_common_period_integral_eq_zero (N : ℕ) [NeZero N]
    (n : ℤ) (hn : ¬ (N : ℤ) ∣ n) (f : ℝ → ℂ) (hf : Function.Periodic f 1) :
    (∫ x in (0 : ℝ)..(N : ℝ), cuspFourierPhase (N : ℝ) n x * f x) = 0 := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  let g (x : ℝ) := cuspFourierPhase (N : ℝ) n x * f x
  have hχ : cuspFourierPhase (N : ℝ) n 1 ≠ 1 := by
    intro he
    apply hn
    have hd := (atkinPhase_int_ratio_eq_one_iff N (NeZero.pos N) (-n)).mp (by
      simpa only [cuspFourierPhase_as_atkinPhase, mul_one, Int.cast_neg] using he)
    simpa only [dvd_neg] using hd
  have hfN : Function.Periodic f (N : ℝ) := by simpa only [mul_one] using hf.nat_mul N
  have hperiod : Function.Periodic g (N : ℝ) := (cuspFourierPhase_periodic _ hN n).mul hfN
  have hshift : (∫ x in (0 : ℝ)..(N : ℝ), g (x+1)) = ∫ x in (0 : ℝ)..(N : ℝ), g x := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm (N : ℝ) 1] using hperiod.intervalIntegral_add_eq 1 0
  have hfactor : (∫ x in (0 : ℝ)..(N : ℝ), g (x+1)) =
      cuspFourierPhase (N : ℝ) n 1 * ∫ x in (0 : ℝ)..(N : ℝ), g x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [g, cuspFourierPhase_add, hf x]
    ring
  have hcancel : (cuspFourierPhase (N : ℝ) n 1 - 1) * (∫ x in (0 : ℝ)..(N : ℝ), g x) = 0 := by
    rw [sub_mul, one_mul, ← hfactor, hshift, sub_self]
  exact (mul_eq_zero.mp hcancel).resolve_left (sub_ne_zero.mpr hχ)

theorem gamma0InfinityFourierCoefficient_eq_zero_of_not_dvd (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : ¬ (N : ℤ) ∣ n) (f : Gamma0RegionL2 N) :
    gamma0CuspFourierCoefficient N 1 Y hY n f = 0 := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_eq (gamma0CuspFourierCoefficient N 1 Y hY n).continuous continuous_const)
  intro ψ
  apply Lp.ext
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hcoeff := Measure.ae_smul_measure (gamma0CuspFourierCoefficient_seed_ae N ψ 1 Y hY n)
    (cuspHorizontalMeasure (N : ℝ) univ)
  filter_upwards [hcoeff, cuspWeightedVerticalMeasure_ae_gt (N : ℝ) Y hY, Lp.coeFn_zero ℂ 2
    (cuspHorizontalMeasure (N : ℝ) univ • cuspVerticalMeasure Y)] with y hy hyY hzero
  rw [hy, hzero]
  have hper : Function.Periodic (fun x : ℝ => gamma0CuspSeedPlaneExtension N ψ 1 Y (x,y)) 1 := by
    intro x
    change spectralSectionSmoothExtension Y (gamma0CuspSection N ψ 1) (x+1,y) =
      spectralSectionSmoothExtension Y (gamma0CuspSection N ψ 1) (x,y)
    rw [spectralSectionSmoothExtension_eq hY _ (p := (x+1,y)) hyY.le,
      spectralSectionSmoothExtension_eq hY _ (p := (x,y)) hyY.le]
    have hp := gamma0Invariant_rawCusp_primitive_period N 1 (gamma0PoincareSeed N ψ.val)
      (gamma0PoincareSeed_invariant N ψ.val) y (hY.trans hyY) x
    have hpoint (t : ℝ) : UpperHalfPlane.ofComplex ((t : ℂ)+(y : ℂ)*Complex.I) =
        gamma0EisensteinHorizontalPoint y (hY.trans hyY) t := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hY.trans hyY)]
      apply UpperHalfPlane.ext
      change (t : ℂ)+(y : ℂ)*Complex.I = ⟨t,y⟩
      apply Complex.ext <;> simp
    simpa only [gamma0CuspTrueWidth_identity, Nat.cast_one, spectralSectionPlane,
      gamma0CuspSection, inv_one, one_smul, Complex.equivRealProdCLM_symm_apply,
      hpoint] using hp
  unfold cuspHorizontalWeightedMean cuspHorizontalMean
  rw [← intervalIntegral.integral_of_le hN.le, infinity_common_period_integral_eq_zero N n hn _ hper,
    mul_zero]
  rfl

end ArtinMatthews
