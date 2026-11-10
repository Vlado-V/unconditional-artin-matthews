module

public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralKRealOrderLower
public import ArtinMatthews.SpectralKSquarePhysicalBand
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Compact physical tests that detect the actual exceptional K amplitude
uniformly across real orders between zero and one half. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped ContDiff

namespace ArtinMatthews

theorem spectralKExceptionalPhysicalTest_exists {A : ℝ} (hA : 0 < A) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ Icc A (2*A) ∧ (∀ x, 0 ≤ F x ∧ F x ≤ 1) ∧
      (∀ x ∈ Icc (5*A/4) (7*A/4), F x = 1) := by
  have hS : Icc (5*A/4) (7*A/4) ⊆ Ioo A (2*A) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  obtain ⟨F,hF,h01,hS',hOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    isOpen_Ioo isClosed_Icc hS
  have hT : tsupport F ⊆ Icc A (2*A) := by
    rw [tsupport,hS']
    exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  exact ⟨F,hF,isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hT,hT,
    fun x => h01 ⟨x,rfl⟩,fun x hx => (hOne x).mp hx⟩

theorem spectralKExceptionalPhysicalTest_mass_le (F : ℝ → ℝ) (hF : Continuous F)
    {A : ℝ} (hA : 0 < A) (hT : tsupport F ⊆ Icc A (2*A))
    (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    (∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure) ≤ 1 := by
  let S := Icc A (2*A)
  have hS : S ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le hx.1
  have hExt : (∫ x in S, (F x)^2 ∂spectralKLPhysicalMeasure) =
      ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hT h))
      rw [hz,zero_pow (by norm_num : (2:ℕ) ≠ 0)])
  have hI : IntegrableOn (fun x : ℝ => (F x)^2/x) S :=
    ((hF.pow 2).continuousOn.div continuousOn_id (fun _ hx => (hS hx).ne')).integrableOn_Icc
  rw [← hExt,spectralKLPhysical_setIntegral_div _ measurableSet_Icc hS]
  calc
    _ ≤ ∫ _x in S, A⁻¹ := by
      apply setIntegral_mono_on hI (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc
      intro x hx
      apply (div_le_iff₀ (hS hx)).mpr
      have h₁ : (F x)^2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ (h01 x).1 (h01 x).2 2
      have h₂ : 1 ≤ A⁻¹*x := by
        rw [← div_eq_inv_mul]
        exact (one_le_div hA).mpr hx.1
      exact h₁.trans h₂
    _ = 1 := by
      dsimp only [S]
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show A ≤ 2*A by linarith),
        intervalIntegral.integral_const,smul_eq_mul,show 2*A-A=A by ring,mul_inv_cancel₀ hA.ne']

theorem spectralKExceptionalPhysicalTest_transform_lower (F : ℝ → ℝ) (hF : Continuous F)
    {A : ℝ} (hA : 0 < A) (hA₁ : 2*A ≤ 1) (hT : tsupport F ⊆ Icc A (2*A))
    (hF₀ : ∀ x, 0 ≤ F x) (hOne : ∀ x ∈ Icc (5*A/4) (7*A/4), F x = 1)
    {ν : ℝ} (hν : 0 ≤ ν) (hν₁ : ν ≤ 1/2) :
    (Real.exp (-Real.exp 1)/16)*A^(-ν) ≤
      ‖∫ x : ℝ, (F x : ℂ)*schlafliBesselK (ν : ℂ) x ∂spectralKLPhysicalMeasure‖ := by
  let S := Icc A (2*A)
  let J := Icc (5*A/4) (7*A/4)
  let K (x : ℝ) := (schlafliBesselK (ν : ℂ) x).re
  let b := Real.exp (-Real.exp 1)*A^(-ν)/(8*A)
  have hS : S ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le hx.1
  have hJ : J ⊆ S := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hEq :
      (∫ x : ℝ, (F x : ℂ)*schlafliBesselK (ν : ℂ) x ∂spectralKLPhysicalMeasure) =
        ((∫ x : ℝ, F x*K x ∂spectralKLPhysicalMeasure : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    dsimp only [K]
    rw [schlafliBesselK_real_order_integral ν hx,Complex.ofReal_re,Complex.ofReal_mul]
  have hExt : (∫ x in S, F x*K x ∂spectralKLPhysicalMeasure) =
      ∫ x : ℝ, F x*K x ∂spectralKLPhysicalMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hT h)),zero_mul])
  have hK : ContinuousOn K S := by
    intro x hx
    exact (Complex.continuous_re.continuousAt.comp
      (schlafliBesselK_hasDerivAt (ν : ℂ) x (hS hx)).continuousAt).continuousWithinAt
  have hI : IntegrableOn (fun x => F x*K x/x) S :=
    ((hF.continuousOn.mul hK).div continuousOn_id (fun _ hx => (hS hx).ne')).integrableOn_Icc
  have hbound (x : ℝ) (hx : x ∈ J) : b ≤ F x*K x/x := by
    have hPos := hS (hJ hx)
    have hTwo : (1/2 : ℝ) ≤ (2 : ℝ)^(-ν) := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show (-1 : ℝ) ≤ -ν by linarith)
      norm_num [Real.rpow_neg_one] at h
      exact h
    have hPow : (1/2 : ℝ)*A^(-ν) ≤ x^(-ν) := by
      calc
        _ ≤ (2 : ℝ)^(-ν)*A^(-ν) := mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg hA.le _)
        _ = (2*A)^(-ν) := (Real.mul_rpow (by norm_num) hA.le).symm
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos hPos (hJ hx).2 (neg_nonpos.mpr hν)
    rw [hOne x hx,one_mul]
    apply (le_div_iff₀ hPos).mpr
    calc
      b*x ≤ b*(2*A) := mul_le_mul_of_nonneg_left (hJ hx).2 (by dsimp only [b]; positivity)
      _ = (Real.exp (-Real.exp 1)/2)*((1/2)*A^(-ν)) := by
        dsimp only [b]
        field_simp [hA.ne']
        ring
      _ ≤ (Real.exp (-Real.exp 1)/2)*x^(-ν) := mul_le_mul_of_nonneg_left hPow (by positivity)
      _ ≤ K x := schlafliBesselK_real_order_small_height_lower hν hPos ((hJ hx).2.trans hA₁)
  rw [hEq,Complex.norm_real,Real.norm_eq_abs,← hExt,
    spectralKLPhysical_setIntegral_div _ measurableSet_Icc hS]
  apply le_trans _ (le_abs_self _)
  calc
    _ = ∫ _x in J, b := by
      dsimp only [J]
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show 5*A/4 ≤ 7*A/4 by linarith),
        intervalIntegral.integral_const,smul_eq_mul]
      dsimp only [b]
      field_simp [hA.ne']
      ring
    _ ≤ ∫ x in J, F x*K x/x := setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_ne_top)
      (hI.mono_set hJ) measurableSet_Icc hbound
    _ ≤ _ := setIntegral_mono_set hI (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact div_nonneg (mul_nonneg (hF₀ x) (schlafliBesselK_real_order_re_nonneg ν (hS hx))) (hS hx).le)
      (Eventually.of_forall (fun _ hx => hJ hx))

end ArtinMatthews
