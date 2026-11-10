module

public import ArtinMatthews.SpectralPeterssonWeightedBound
public import ArtinMatthews.SpectralPeterssonHeckeRows
public import ArtinMatthews.SpectralPeterssonHeckeMajorant
public import ArtinMatthews.SpectralPeterssonHeckePoisson
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual pointwise Abel limit of the Hecke series at the infinity
seed, in every genuine cusp chart, with the uniform weighted bound
used for dominated Petersson pairing. -/

noncomputable section
open Set Filter Matrix UpperHalfPlane
open scoped MatrixGroups Topology FourierTransform

namespace ArtinMatthews

private theorem spectralPeterssonHeckeSeed_weighted_bound (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (m : ℕ+) (z : UpperHalfPlane) :
    ‖spectralPeterssonHeckeSeed u m z‖*z.im ≤ 1+2/(2*Real.pi*(m : ℝ))^2 := by
  let y := z.im
  let r := 2*Real.pi*(m : ℝ)
  have hy : 0 < y := z.im_pos
  have hr : 0 < r := by positivity
  have hvalue : ‖spectralPeterssonHeckeSeed u m z‖*z.im = y^(1+u)*Real.exp (-(r*y)) := by
    rw [spectralPeterssonHeckeSeed,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _),spectralHolomorphicCuspSeed_norm]
    change y^u*Real.exp (-(r*y))*y = _
    rw [Real.rpow_add hy,Real.rpow_one]
    ring
  rw [hvalue]
  change _ ≤ 1+2/r^2
  by_cases hs : y ≤ 1
  · have h₁ := Real.rpow_le_one hy.le hs (by linarith [hu.1] : 0 ≤ 1+u)
    have h₂ := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr.le hy.le))
    calc
      _ ≤ 1*1 := mul_le_mul h₁ h₂ (Real.exp_nonneg _) zero_le_one
      _ ≤ _ := by
        rw [mul_one]
        exact le_add_of_nonneg_right (by positivity)
  · have h₁ : y^(1+u) ≤ y^2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hs) (by linarith [hu.2])
    calc
      _ ≤ y^2*Real.exp (-(r*y)) := mul_le_mul_of_nonneg_right h₁ (Real.exp_nonneg _)
      _ ≤ 2/r^2 := by
        rw [Real.exp_neg,← div_eq_mul_inv]
        apply (div_le_div_iff₀ (Real.exp_pos _) (sq_pos_of_pos hr)).mpr
        have h := Real.quadratic_le_exp_of_nonneg (mul_nonneg hr.le hy.le)
        nlinarith only [h,mul_nonneg hr.le hy.le]
      _ ≤ _ := by linarith

theorem gamma0PeterssonHeckeZeroSector_weighted_bound (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (m : ℕ+) (z : UpperHalfPlane) :
    ‖gamma0PeterssonHeckeZeroSector N b a u m z‖*z.im ≤ 1+2/(2*Real.pi*(m : ℝ))^2 := by
  classical
  rcases isEmpty_or_nonempty (Gamma0PeterssonZeroRow N b a) with h | h
  · let _ := h
    simp only [gamma0PeterssonHeckeZeroSector,tsum_empty,norm_zero,zero_mul]
    positivity
  · let p := h.some
    unfold gamma0PeterssonHeckeZeroSector
    rw [tsum_eq_single p (fun q hq => (hq (Subsingleton.elim q p)).elim)]
    let G := gamma0TrueWidthMatrix N b a (gamma0PeterssonRowMatrix N b a p.val.val).val
    change ‖spectralHolomorphicSlash 2 G (spectralPeterssonHeckeSeed u m) z‖*z.im ≤ _
    have hcov := spectralPeterssonWeightedNorm_slash 2 G (spectralPeterssonHeckeSeed u m) z
    simp only [spectralPeterssonWeightedNorm,Nat.cast_ofNat,div_self (by norm_num : (2 : ℝ) ≠ 0),Real.rpow_one] at hcov
    rw [hcov]
    exact spectralPeterssonHeckeSeed_weighted_bound u hu m (G • z)

theorem gamma0PeterssonHeckeZeroSector_continuous_parameter (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (m : ℕ+) (z : UpperHalfPlane) : Continuous (fun u => gamma0PeterssonHeckeZeroSector N b a u m z) := by
  classical
  rcases isEmpty_or_nonempty (Gamma0PeterssonZeroRow N b a) with h | h
  · let _ := h
    simp only [gamma0PeterssonHeckeZeroSector,tsum_empty]
    exact continuous_const
  · let p := h.some
    let G := gamma0TrueWidthMatrix N b a (gamma0PeterssonRowMatrix N b a p.val.val).val
    have he (u : ℝ) : gamma0PeterssonHeckeZeroSector N b a u m z =
        spectralHolomorphicSlash 2 G (spectralPeterssonHeckeSeed u m) z := by
      unfold gamma0PeterssonHeckeZeroSector
      exact tsum_eq_single p (fun q hq => (hq (Subsingleton.elim q p)).elim)
    simp_rw [he,spectralHolomorphicSlash_apply,spectralPeterssonHeckeSeed]
    exact ((Complex.continuous_ofReal.comp (Real.continuous_const_rpow (G • z).im_ne_zero)).mul
      continuous_const).div_const _

theorem gamma0PeterssonHeckeJointTerm_tendsto (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (m : ℕ+) (c : Ioi (0 : ℕ)) (n : ℤ) (z : UpperHalfPlane) :
    Tendsto (fun u => gamma0PeterssonHeckeJointTerm N b a u m c n z) (𝓝[>] (0 : ℝ))
      (𝓝 (gamma0PeterssonHeckeJointTerm N b a 0 m c n z)) := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let C := gamma0TrueWidthModulus N b a (c.val : ℝ)
  have hC : 0 < C := gamma0TrueWidthModulus_pos N b a (Nat.cast_pos.mpr c.property)
  let lam := spectralPeterssonHeckeLambda m C z.im
  have hlam : 0 ≤ lam := by dsimp only [lam,spectralPeterssonHeckeLambda]; positivity
  let q (u : ℝ) : ℂ := ((C^(-(2+2*u))*z.im^(-1-u) : ℝ) : ℂ)
  have h₁ : Continuous (fun u : ℝ => C^(-(2+2*u))) :=
    (Real.continuous_const_rpow hC.ne').comp (by fun_prop)
  have h₂ : Continuous (fun u : ℝ => z.im^(-1-u)) :=
    (Real.continuous_const_rpow z.im_ne_zero).comp (by fun_prop)
  have hq : Continuous q := Complex.continuous_ofReal.comp (h₁.mul h₂)
  have hF := spectralPeterssonHeckeProfile_fourier_tendsto lam ((n : ℝ)*z.im) hlam
  have h := (hq.continuousAt.continuousWithinAt.mul hF).const_mul
    (gamma0TrueWidthKloostermanSum N b a c.val n (m : ℤ))
  exact h.mul_const (atkinPhase ((n : ℝ)*z.re))

theorem gamma0PeterssonHeckeModulus_tendsto (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (m : ℕ+) (c : Ioi (0 : ℕ)) (z : UpperHalfPlane) :
    Tendsto (fun u => gamma0PeterssonHeckeModulus N b 1 u m c z) (𝓝[>] (0 : ℝ))
      (𝓝 (gamma0PeterssonHeckeModulus N b 1 0 m c z)) := by
  obtain ⟨D,hD,hb⟩ := gamma0PeterssonHeckeJointTerm_majorant N b m z.im z.im_pos
  let U (n : ℤ) : ℝ := (D*(c.val : ℝ)^(-(5/4 : ℝ))/z.im)*(1+(n : ℝ)^2)⁻¹
  have hU : Summable U := spectralPetersson_inverseSquare_samples_summable.mul_left _
  have hbound : ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ n,
      ‖gamma0PeterssonHeckeJointTerm N b 1 u m c n z‖ ≤ U n := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with u hu n
    dsimp only [U]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ z.im_pos).mpr (hb u c n z ⟨hu.1.le,hu.2⟩ le_rfl)
  have h := tendsto_tsum_of_dominated_convergence hU (gamma0PeterssonHeckeJointTerm_tendsto N b 1 m c · z) hbound
  rw [← gamma0PeterssonHeckeModulus_fourier N b 1 0 ⟨le_rfl,zero_le_one⟩ m c z] at h
  refine h.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with u hu
  exact (gamma0PeterssonHeckeModulus_fourier N b 1 u ⟨hu.1.le,hu.2⟩ m c z).symm

theorem gamma0PeterssonHeckeGrouped_tendsto (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (m : ℕ+) (z : UpperHalfPlane) :
    Tendsto (fun u => gamma0PeterssonHeckeChart N b 1 u m z) (𝓝[>] (0 : ℝ))
      (𝓝 (gamma0PeterssonHeckeGrouped N b 1 0 m z)) := by
  obtain ⟨D,hD,hb⟩ := gamma0PeterssonHeckeModulus_majorant N b m z.im z.im_pos
  let U (c : Ioi (0 : ℕ)) : ℝ := (D/z.im)*(c.val : ℝ)^(-(5/4 : ℝ))
  have hU : Summable U := gamma0PeterssonHecke_rawModulusMajorant_summable.mul_left _
  have hbound : ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ c, ‖gamma0PeterssonHeckeModulus N b 1 u m c z‖ ≤ U c := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with u hu c
    dsimp only [U]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ z.im_pos).mpr (hb u c z ⟨hu.1.le,hu.2⟩ le_rfl)
  have h := tendsto_tsum_of_dominated_convergence hU (fun c => gamma0PeterssonHeckeModulus_tendsto N b m c z) hbound
  have h0 : Tendsto (fun u => gamma0PeterssonHeckeZeroSector N b 1 u m z) (𝓝[>] (0 : ℝ))
      (𝓝 (gamma0PeterssonHeckeZeroSector N b 1 0 m z)) :=
    (gamma0PeterssonHeckeZeroSector_continuous_parameter N b 1 m z).continuousAt.continuousWithinAt
  refine (h0.add h).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with u hu
  exact (gamma0PeterssonHeckeChart_eq_grouped N b 1 u hu.1 m z).symm

theorem gamma0PeterssonHeckeGrouped_weighted_bound (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (m : ℕ+) (Y : ℝ) (hY : 0 < Y) :
    ∃ D ≥ 0, ∀ (u : ℝ) (z : UpperHalfPlane), u ∈ Icc (0 : ℝ) 1 → Y ≤ z.im →
      ‖gamma0PeterssonHeckeGrouped N b 1 u m z‖*z.im ≤ D := by
  obtain ⟨D,hD,hb⟩ := gamma0PeterssonHeckeModulus_majorant N b m Y hY
  let w (c : Ioi (0 : ℕ)) : ℝ := (c.val : ℝ)^(-(5/4 : ℝ))
  let L := 1+2/(2*Real.pi*(m : ℝ))^2
  have hw : Summable w := gamma0PeterssonHecke_rawModulusMajorant_summable
  have hw' (c : Ioi (0 : ℕ)) : 0 ≤ w c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨L+D*(∑' c, w c), add_nonneg (by dsimp only [L]; positivity) (mul_nonneg hD (tsum_nonneg hw')),?_⟩
  intro u z hu hy
  let f (c : Ioi (0 : ℕ)) := gamma0PeterssonHeckeModulus N b 1 u m c z
  have hf (c : Ioi (0 : ℕ)) : ‖f c‖*z.im ≤ D*w c := hb u c z hu hy
  have hs : Summable (fun c => ‖f c‖) := by
    apply Summable.of_nonneg_of_le (fun c => norm_nonneg (f c)) _ (hw.mul_left (D/z.im))
    intro c
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ z.im_pos).mpr (hf c)
  have hb' : ‖∑' c, f c‖*z.im ≤ D*(∑' c, w c) := by
    calc
      _ ≤ (∑' c, ‖f c‖)*z.im := mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hs) z.im_pos.le
      _ = ∑' c, ‖f c‖*z.im := tsum_mul_right.symm
      _ ≤ ∑' c, D*w c := (hs.mul_right _).tsum_le_tsum hf (hw.mul_left _)
      _ = _ := tsum_mul_left
  have h0 := gamma0PeterssonHeckeZeroSector_weighted_bound N b 1 u hu m z
  unfold gamma0PeterssonHeckeGrouped
  calc
    _ ≤ (‖gamma0PeterssonHeckeZeroSector N b 1 u m z‖+‖∑' c, f c‖)*z.im :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) z.im_pos.le
    _ ≤ _ := by rw [add_mul]; exact add_le_add h0 hb'

end ArtinMatthews
