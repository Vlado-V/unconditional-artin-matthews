module

public import ArtinMatthews.ShiftedABLRhoCommonTest
public import ArtinMatthews.SpectralABLOppositeKTransform
public import ArtinMatthews.ShiftedABLRhoCommonDyadic
public import ArtinMatthews.SpectralABLOppositeTransformLinear
public import ArtinMatthews.SpectralABLOppositeUniform
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex Finset
open scoped ContDiff BigOperators
noncomputable section

/-- Source-uniform opposite-sign transform estimate for the literal
common test from the signed rho separation. -/
theorem shiftedABLRhoCommonTest_opposite_strip_bound (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X u Z P : ℝ, 0 < X → X ≤ B → 1+|u| ≤ Z → 1 ≤ P → P⁻¹ ≤ X → Z ≤ P →
      ∀ z : ℂ, |z.im| ≤ 1/2 →
        ‖spectralABLOppositeTransform (shiftedABLRhoCommonTest (4*Real.pi*X) u) z‖ ≤
          (C*P^δ*(Z/X)^(2*|z.im|))/(1+‖z‖/Z)^J := by
  obtain ⟨D,hD,hderiv⟩ := shiftedABLRhoCommonDyadicTest_derivative_bound (3+2*J)
  let B₀ := max 1 (8*Real.pi*B)
  have hB₀ : 1 ≤ B₀ := le_max_left _ _
  obtain ⟨E,hE,huniform⟩ := spectralABLOppositeTransform_source_uniform J B₀ 2 δ hB₀ (by norm_num) hδ
  refine ⟨8*E*D,by positivity,?_⟩
  intro X u Z P hX hXB hZ hP hPX hZP z hz
  let a := 4*Real.pi*X
  have ha : 0 < a := by dsimp [a]; positivity
  have hZ₁ : 1 ≤ Z := (by linarith [abs_nonneg u] : 1 ≤ 1+|u|).trans hZ
  have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ₁
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  let Q : Finset (ℕ × Bool) := range 4 ×ˢ (Finset.univ : Finset Bool)
  let f (i : ℕ × Bool) := shiftedABLRhoCommonDyadicTest a u i.1 i.2
  let d (i : ℕ × Bool) := shiftedABLRhoCommonDyadicScale a i.1 i.2
  have hds (i : ℕ × Bool) : 0 < d i := shiftedABLRhoCommonDyadicScale_pos ha i.1 i.2
  have hs (i : ℕ × Bool) : tsupport (f i) ⊆ Icc (d i) (2*d i) :=
    shiftedABLRhoCommonDyadicTest_tsupport ha u i.1 i.2
  have hfc (i : ℕ × Bool) : HasCompactSupport (f i) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs i)
  have hfp (i : ℕ × Bool) : tsupport (f i) ⊆ Ioi (0 : ℝ) :=
    fun x hx => (hds i).trans_le (hs i hx).1
  have hf (i : ℕ × Bool) : ContDiff ℝ ∞ (f i) :=
    shiftedABLRhoCommonDyadicTest_contDiff ha u i.1 i.2
  have hI (i : ℕ × Bool) : Integrable (spectralKLCompactOrderIntegrand (f i) (2*I*z)) :=
    spectralKLCompactOrderIntegrand_integrable (f i) (hf i).continuous (hfc i) (hfp i) _
  have hsum : spectralABLOppositeTransform (shiftedABLRhoCommonTest a u) z =
      ∑ i ∈ Q, spectralABLOppositeTransform (f i) z := by
    rw [shiftedABLRhoCommonTest_dyadic_partition ha u]
    exact spectralABLOppositeTransform_finset_sum Q f z (fun i _ => hI i)
  have hρπ : spectralDyadicRatio ≤ Real.pi := by
    have h : spectralDyadicRatio ≤ 2 := by
      change Real.sqrt 2 ≤ 2
      exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    exact h.trans (by linarith [Real.pi_gt_three])
  have hXd (i : ℕ × Bool) (hi : i ∈ Q) : X ≤ d i := by
    have hk : i.1 < 4 := mem_range.mp (mem_product.mp hi).1
    apply le_trans _ (shiftedABLRhoCommonDyadicScale_bounds ha hk i.2).1
    apply (le_div_iff₀ (mul_pos (by norm_num) spectralDyadicRatio_pos)).mpr
    calc
      _ ≤ X*(4*Real.pi) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hρπ (by norm_num)) hX.le
      _ = a := by dsimp [a]; ring
  have hBd (i : ℕ × Bool) (hi : i ∈ Q) : d i ≤ B₀*Z := by
    have hk : i.1 < 4 := mem_range.mp (mem_product.mp hi).1
    calc
      _ ≤ 2*a := (shiftedABLRhoCommonDyadicScale_bounds ha hk i.2).2
      _ = 8*Real.pi*X := by dsimp [a]; ring
      _ ≤ 8*Real.pi*B := mul_le_mul_of_nonneg_left hXB (by positivity)
      _ ≤ B₀ := le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_right (zero_le_one.trans hB₀) hZ₁
  have hXP : X⁻¹ ≤ P := by
    simpa only [one_div,inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hP₀) hPX
  have hZXP : Z/X ≤ P^(2 : ℝ) := by
    rw [Real.rpow_two,pow_two,div_eq_mul_inv]
    exact mul_le_mul hZP hXP (inv_nonneg.mpr hX.le) hP₀.le
  let r := 2*|z.im|
  let T := (E*D*P^δ*(Z/X)^r)/(1+‖z‖/Z)^J
  have hT (i : ℕ × Bool) (hi : i ∈ Q) : ‖spectralABLOppositeTransform (f i) z‖ ≤ T := by
    have hk : i.1 < 4 := mem_range.mp (mem_product.mp hi).1
    have hZd : Z/d i ≤ Z/X := div_le_div_of_nonneg_left hZ₀.le hX (hXd i hi)
    have h := huniform (d i) Z D P (f i) (hds i) hZ₁ (hBd i hi) hD.le hP
      (hZd.trans hZXP) (hf i) (hs i) (hderiv a u Z ha hZ i.1 hk i.2) z hz
    have hp : (Z/d i)^r ≤ (Z/X)^r := Real.rpow_le_rpow
      (div_nonneg hZ₀.le (hds i).le) hZd (mul_nonneg (by norm_num) (abs_nonneg _))
    refine h.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      hp (by positivity)) (by positivity)
  change ‖spectralABLOppositeTransform (shiftedABLRhoCommonTest a u) z‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ Q, ‖spectralABLOppositeTransform (f i) z‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Q, T := sum_le_sum hT
    _ = 8*T := by simp [Q,card_product]
    _ = _ := by dsimp [T,r]; ring

theorem shiftedABLRhoCommonTest_opposite_conductor_estimates (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X u Z P : ℝ, 0 < X → X ≤ B → 1+|u| ≤ Z → 1 ≤ P → P⁻¹ ≤ X → Z ≤ P →
      let f := shiftedABLRhoCommonTest (4*Real.pi*X) u
      (∀ t : ℝ, ‖spectralABLOppositeTransform f (t : ℂ)‖ ≤ C*P^δ/(1+|t|/Z)^J) ∧
      ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/4 →
        ‖spectralABLOppositeTransform f ((κ : ℂ)*I)‖ ≤ C*P^δ*(X/Z)^(-2*κ) := by
  obtain ⟨C,hC,h⟩ := shiftedABLRhoCommonTest_opposite_strip_bound B δ hB hδ J
  refine ⟨C,hC,?_⟩
  intro X u Z P hX hXB hZ hP hPX hZP f
  have hZ₀ : 0 < Z := by linarith [abs_nonneg u]
  constructor
  · intro t
    simpa only [f,Complex.ofReal_im,abs_zero,mul_zero,Real.rpow_zero,mul_one,
      Complex.norm_real,Real.norm_eq_abs] using h X u Z P hX hXB hZ hP hPX hZP (t : ℂ) (by norm_num)
  · intro κ hκ hκ₁
    let z : ℂ := (κ : ℂ)*I
    have him : z.im = κ := by simp [z,Complex.mul_im]
    have hz : |z.im| ≤ 1/2 := by rw [him,abs_of_nonneg hκ]; linarith
    have hd : 1 ≤ (1+‖z‖/Z)^J := one_le_pow₀ (by linarith [div_nonneg (norm_nonneg z) hZ₀.le])
    have hp : (Z/X)^(2*|z.im|) = (X/Z)^(-2*κ) := by
      rw [him,abs_of_nonneg hκ,show -2*κ = -(2*κ) by ring,
        Real.rpow_neg (by positivity),← Real.inv_rpow (by positivity),inv_div]
    refine (h X u Z P hX hXB hZ hP hPX hZP z hz).trans ?_
    rw [hp]
    exact div_le_self (by positivity) hd

end
end ArtinMatthews
