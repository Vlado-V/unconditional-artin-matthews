module

public import ArtinMatthews.SpectralPeterssonHeckeOrbital
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.SpectralPeterssonHeckePoisson
public import ArtinMatthews.SpectralPeterssonInfinityWeil
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Summable bounds for the actual regulator after the arithmetic
cancellation. They are uniform in every horizontal coordinate and in
regulator [0,1] on the entire strip y ≥ Y. -/

noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups FourierTransform

namespace ArtinMatthews

theorem gamma0PeterssonTrueWidthModulus_ge_raw (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) : (c.val : ℝ) ≤ gamma0TrueWidthModulus N b a (c.val : ℝ) := by
  have hb : 1 ≤ (gamma0CuspTrueWidth N b : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N b
  have ha : 1 ≤ (gamma0CuspTrueWidth N a : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N a
  have hbs : 1 ≤ Real.sqrt (gamma0CuspTrueWidth N b : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hb
  have has : 1 ≤ Real.sqrt (gamma0CuspTrueWidth N a : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ha
  unfold gamma0TrueWidthModulus
  calc
    (c.val : ℝ) = (c.val : ℝ)*1*1 := by ring
    _ ≤ _ := by gcongr

private theorem spectralPeterssonHecke_height_power (u Y y : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (hY : 0 < Y) (hy : Y ≤ y) : y^(-u) ≤ max 1 Y⁻¹ := by
  refine (Real.rpow_le_rpow_of_nonpos hY hy (neg_nonpos.mpr hu.1)).trans ?_
  by_cases h : Y ≤ 1
  · calc
      Y^(-u) ≤ Y^(-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hY h (neg_le_neg hu.2)
      _ = Y⁻¹ := Real.rpow_neg_one Y
      _ ≤ _ := le_max_right _ _
  · exact (Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge h) (neg_nonpos.mpr hu.1)).trans (le_max_left _ _)

theorem gamma0PeterssonHeckeJointTerm_majorant (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (m : ℕ+) (Y : ℝ) (hY : 0 < Y) :
    ∃ D > 0, ∀ (u : ℝ) (c : Ioi (0 : ℕ)) (n : ℤ) (z : UpperHalfPlane),
      u ∈ Icc (0 : ℝ) 1 → Y ≤ z.im →
      ‖gamma0PeterssonHeckeJointTerm N b 1 u m c n z‖*z.im ≤
        D*(c.val : ℝ)^(-(5/4 : ℝ))*(1+(n : ℝ)^2)⁻¹ := by
  obtain ⟨K,hK,hWeil⟩ := gamma0TrueWidthKloostermanSum_leftInfinity_weil N b m (1/4) (by norm_num)
  let L := 2*Real.pi*(m : ℝ)/Y
  let H := max (1 : ℝ) Y⁻¹
  let F := spectralPeterssonHeckeFourierCost L/min 1 (Y^2)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hF : 0 < F := div_pos (spectralPeterssonHeckeFourierCost_pos hL) (lt_min zero_lt_one (sq_pos_of_pos hY))
  have hH : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨K*H*F, mul_pos (mul_pos hK hH) hF,?_⟩
  intro u c n z hu hy
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let C := gamma0TrueWidthModulus N b 1 (c.val : ℝ)
  let y := z.im
  let lam := spectralPeterssonHeckeLambda m C y
  let T := ‖𝓕 (spectralPeterssonHeckeProfile u lam) ((n : ℝ)*y)‖
  let R := (1+(n : ℝ)^2)⁻¹
  have hc : (0 : ℝ) < c.val := Nat.cast_pos.mpr c.property
  have hc1 : (1 : ℝ) ≤ c.val := by exact_mod_cast c.property
  have hcC : (c.val : ℝ) ≤ C := gamma0PeterssonTrueWidthModulus_ge_raw N b 1 c
  have hC : 0 < C := hc.trans_le hcC
  have hC0 : 0 ≤ gamma0TrueWidthModulus N b 1 (c.val : ℝ) := hC.le
  have hC1 : 1 ≤ C := hc1.trans hcC
  have hlam : 0 ≤ lam := by dsimp only [lam,spectralPeterssonHeckeLambda]; positivity
  have hlamL : lam ≤ L := by
    dsimp only [lam,L,spectralPeterssonHeckeLambda]
    apply div_le_div_of_nonneg_left (by positivity) hY
    exact hy.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hC1) z.im_pos.le)
  have hT : T ≤ F*R := by
    apply (spectralPeterssonHeckeProfile_sample_bound u lam Y y n hu hlam hY hy).trans
    dsimp only [F,R]
    gcongr
    exact spectralPeterssonHeckeFourierCost_mono hlam hlamL
  have hP : C^(-(2+2*u)) ≤ (c.val : ℝ)^(-(2 : ℝ)) :=
    (Real.rpow_le_rpow_of_exponent_le hC1 (by linarith [hu.1])).trans
      (Real.rpow_le_rpow_of_nonpos hc hcC (by norm_num))
  have hK' : ‖gamma0TrueWidthKloostermanSum N b 1 c.val n (m : ℤ)‖ ≤ K*(c.val : ℝ)^(3/4 : ℝ) := by
    simpa only [show (1/2 : ℝ)+1/4=3/4 by norm_num] using hWeil c.val n
  have hY' : y^(-u) ≤ H := spectralPeterssonHecke_height_power u Y y hu hY hy
  have hYpow : y^(-1-u)*y = y^(-u) := by
    rw [show -1-u=-u-1 by ring,Real.rpow_sub z.im_pos,Real.rpow_one,div_mul_cancel₀ _ z.im_ne_zero]
  have he : ‖gamma0PeterssonHeckeJointTerm N b 1 u m c n z‖*z.im =
      ‖gamma0TrueWidthKloostermanSum N b 1 c.val n (m : ℤ)‖*(C^(-(2+2*u))*y^(-u)*T) := by
    dsimp only [gamma0PeterssonHeckeJointTerm,spectralPeterssonHeckeOrbitalAmplitude]
    simp only [norm_mul,atkinPhase_norm,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hC0 (-(2+2*u))),
      Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le (-1-u))]
    change ‖gamma0TrueWidthKloostermanSum N b 1 c.val n (m : ℤ)‖*
      (C^(-(2+2*u))*y^(-1-u)*T)*y = _
    calc
      _ = ‖gamma0TrueWidthKloostermanSum N b 1 c.val n (m : ℤ)‖*
        (C^(-(2+2*u))*(y^(-1-u)*y)*T) := by ring
      _ = _ := by rw [hYpow]
  rw [he]
  calc
    _ ≤ (K*(c.val : ℝ)^(3/4 : ℝ))*((c.val : ℝ)^(-(2 : ℝ))*H*(F*R)) := by
      have hR : 0 ≤ R := by dsimp only [R]; positivity
      have hT' : 0 ≤ T := norm_nonneg _
      gcongr
    _ = (K*H*F)*(c.val : ℝ)^(-(5/4 : ℝ))*R := by
      have h := Real.rpow_add hc (3/4) (-2)
      rw [show (3/4 : ℝ)+(-2)=-(5/4 : ℝ) by norm_num] at h
      rw [h]
      ring

theorem gamma0PeterssonHecke_rawModulusMajorant_summable :
    Summable (fun c : Ioi (0 : ℕ) => (c.val : ℝ)^(-(5/4 : ℝ))) :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(5/4 : ℝ) < -1)).subtype (Ioi (0 : ℕ))

theorem gamma0PeterssonHeckeModulus_majorant (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (m : ℕ+) (Y : ℝ) (hY : 0 < Y) :
    ∃ D ≥ 0, ∀ (u : ℝ) (c : Ioi (0 : ℕ)) (z : UpperHalfPlane),
      u ∈ Icc (0 : ℝ) 1 → Y ≤ z.im →
      ‖gamma0PeterssonHeckeModulus N b 1 u m c z‖*z.im ≤ D*(c.val : ℝ)^(-(5/4 : ℝ)) := by
  obtain ⟨K,hK,h⟩ := gamma0PeterssonHeckeJointTerm_majorant N b m Y hY
  let f (n : ℤ) : ℝ := (1+(n : ℝ)^2)⁻¹
  let D := K*(∑' n, f n)
  have hf : Summable f := spectralPetersson_inverseSquare_samples_summable
  refine ⟨D,mul_nonneg hK.le (tsum_nonneg fun n => by dsimp only [f]; positivity),?_⟩
  intro u c z hu hy
  let w := (c.val : ℝ)^(-(5/4 : ℝ))
  let q (n : ℤ) := gamma0PeterssonHeckeJointTerm N b 1 u m c n z
  have hq (n : ℤ) : ‖q n‖*z.im ≤ (K*w)*f n := h u c n z hu hy
  have hw : 0 ≤ w := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq' (n : ℤ) : ‖q n‖ ≤ (K*w/z.im)*f n := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ z.im_pos).mpr (hq n)
  have hsum : Summable (fun n => ‖q n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hq' (hf.mul_left _)
  rw [gamma0PeterssonHeckeModulus_fourier N b 1 u hu m c z]
  change ‖∑' n, q n‖*z.im ≤ D*w
  calc
    _ ≤ (∑' n, ‖q n‖)*z.im := mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsum) z.im_pos.le
    _ = ∑' n, ‖q n‖*z.im := tsum_mul_right.symm
    _ ≤ ∑' n, (K*w)*f n := (hsum.mul_right _).tsum_le_tsum hq (hf.mul_left _)
    _ = _ := by rw [tsum_mul_left]; unfold D; ring

end ArtinMatthews
