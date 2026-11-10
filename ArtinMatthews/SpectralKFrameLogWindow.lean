module

public import ArtinMatthews.SpectralKLogHeight
public import ArtinMatthews.SpectralKSquareMellinMoment
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! One fixed smooth logarithmic window, wide enough to retain the
proved dyadic K mass and compactly contained in a fixed period. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff

namespace ArtinMatthews

def spectralKFrameLength : ℝ := Real.log 768

theorem spectralKFrameLength_pos : 0 < spectralKFrameLength := Real.log_pos (by norm_num)

theorem spectralKFrameWindow_exists :
    ∃ (ψ : ℝ → ℝ) (D : ℝ), 0 < D ∧ ContDiff ℝ ∞ ψ ∧
      tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384) ∧
      (∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1) ∧
      (∀ u ∈ Icc (Real.log 4) (Real.log 192), ψ u = 1) ∧
      (∀ u, |deriv ψ u| ≤ D) := by
  have hsub : Icc (Real.log 4) (Real.log 192) ⊆ Ioo (Real.log 2) (Real.log 384) := by
    intro u hu
    exact ⟨(Real.log_lt_log (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)<4)).trans_le hu.1,
      hu.2.trans_lt (Real.log_lt_log (by norm_num : (0 : ℝ)<192) (by norm_num : (192 : ℝ)<384))⟩
  obtain ⟨ψ,hψ,hψ01,hS,hOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    isOpen_Ioo isClosed_Icc hsub
  have hs : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384) := by
    rw [tsupport,hS]
    exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  have hd := hψ.continuous_deriv (by simp)
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := deriv ψ) (s := Icc (Real.log 2) (Real.log 384)) hd.continuousOn
  refine ⟨ψ,max D 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),hψ,hs,
    fun u => hψ01 ⟨u,rfl⟩,fun u hu => (hOne u).mp hu,?_⟩
  intro u
  by_cases hu : u ∈ Icc (Real.log 2) (Real.log 384)
  · exact (by simpa only [Real.norm_eq_abs] using hD u hu : |deriv ψ u| ≤ D).trans (le_max_left _ _)
  · have hz : deriv ψ u = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hu (hs (tsupport_deriv_subset h)))
    rw [hz,abs_zero]
    exact zero_le_one.trans (le_max_right _ _)

def spectralKFrameLogTest (ψ : ℝ → ℝ) (T t u : ℝ) : ℝ :=
  ψ u*spectralRealKLogKernel (T/32) t u

theorem spectralKFrameLogTest_contDiff_one (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (T t : ℝ) (hT : 0 < T) : ContDiff ℝ 1 (spectralKFrameLogTest ψ T t) :=
  (hψ.of_le (by simp)).mul (spectralRealKLogKernel_contDiff_one (by positivity : 0 < T/32) t)

theorem spectralKFrameLogTest_deriv (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (T t u : ℝ) (hT : 0 < T) :
    deriv (spectralKFrameLogTest ψ T t) u =
      deriv ψ u*spectralRealKLogKernel (T/32) t u+
        ψ u*((T/32*Real.exp u)*deriv (spectralKLRealKernel t) (T/32*Real.exp u)) :=
  (((hψ.differentiable (by simp)) u).hasDerivAt.mul
    (spectralRealKLogKernel_hasDerivAt (by positivity : 0 < T/32) t u)).deriv

theorem spectralKFrameLogTest_endpoints (ψ : ℝ → ℝ)
    (hs : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384)) (T t : ℝ) :
    spectralKFrameLogTest ψ T t spectralKFrameLength = 0 ∧ spectralKFrameLogTest ψ T t 0 = 0 := by
  have hL : Real.log 384 < spectralKFrameLength :=
    Real.log_lt_log (by norm_num : (0 : ℝ)<384) (by norm_num : (384 : ℝ)<768)
  have hψL : ψ spectralKFrameLength = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (not_le_of_gt hL) (hs h).2)
  have hψ0 : ψ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (not_le_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2))) (hs h).1)
  simp only [spectralKFrameLogTest,hψL,hψ0,zero_mul,and_self]

theorem spectralKFrameLogTest_mass_lower (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hOne : ∀ u ∈ Icc (Real.log 4) (Real.log 192), ψ u = 1)
    (T t : ℝ) (hT : 0 < T) (ht₁ : T ≤ 1+|t|) (ht₂ : 1+|t| ≤ 2*T) :
    spectralKSquareMoment 0 t/(648*T) ≤
      ∫ u in (0 : ℝ)..spectralKFrameLength, (spectralKFrameLogTest ψ T t u)^2 := by
  let k := T/32
  let a := Real.log 4
  let b := Real.log 192
  let G := spectralKFrameLogTest ψ T t
  have hk : 0 < k := by dsimp only [k]; positivity
  have ha : 0 < a := Real.log_pos (by norm_num)
  have hb : b ≤ spectralKFrameLength :=
    (Real.log_lt_log (by norm_num : (0 : ℝ)<192) (by norm_num : (192 : ℝ)<768)).le
  have hA : k*Real.exp a = T/8 := by dsimp only [k,a]; rw [Real.exp_log (by norm_num : (0 : ℝ)<4)]; ring
  have hB : k*Real.exp b = 6*T := by dsimp only [k,b]; rw [Real.exp_log (by norm_num : (0 : ℝ)<192)]; ring
  have hC :
      (∫ u in Ioc a b, (spectralRealKLogKernel k t u)^2) =
        ∫ x in Ioc (T/8) (6*T), (spectralKLRealKernel t x)^2 ∂spectralKLPhysicalMeasure := by
    rw [spectralKLPhysical_setIntegral_div _ measurableSet_Ioc (fun x hx => (by positivity : 0<T/8).trans hx.1)]
    unfold spectralRealKLogKernel
    rw [spectral_scaledExp_Ioc_integral (fun x : ℝ => (spectralKLRealKernel t x)^2) hk a b,hA,hB]
    simp only [smul_eq_mul,div_eq_inv_mul]
  have h₀ : spectralKSquareMoment 0 t/(648*T) = Real.pi^2/(2592*T*Real.cosh (Real.pi*t)) := by
    rw [spectralKSquareMoment_zero,div_div]
    congr 1
    ring
  have hG : Continuous G := (spectralKFrameLogTest_contDiff_one ψ hψ T t hT).continuous
  have hI : IntegrableOn (fun u => (G u)^2) (Ioc 0 spectralKFrameLength) :=
    (hG.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le spectralKFrameLength_pos.le]
  calc
    _ ≤ ∫ u in Ioc a b, (spectralRealKLogKernel k t u)^2 := by
      rw [hC,h₀]
      exact spectralKSquareDyadicBand_physical_lower t T hT ht₁ ht₂
    _ = ∫ u in Ioc a b, (G u)^2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      change _ = (ψ u*spectralRealKLogKernel k t u)^2
      rw [hOne u ⟨hu.1.le,hu.2⟩,one_mul]
    _ ≤ _ := setIntegral_mono_set hI (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun _ hu => ⟨ha.trans hu.1,hu.2.trans hb⟩))

end ArtinMatthews
