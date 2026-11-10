module

public import ArtinMatthews.SpectralKLIntegrableAnalysis
public import ArtinMatthews.SpectralKLTestSynthesisLinear
public import ArtinMatthews.SpectralKLIntegrableFubini
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

/-! The actual integrably dominated physical/spectral adjoint identity, retaining both
literal weighted measures and the real K kernel. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralKL_majorant_adjoint (f : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hM : Integrable (spectralKLIntegrableMajorant f))
    (hLp : MemLp f 2 spectralKLPhysicalMeasure) (g : spectralKLTestSubmodule) :
    inner ℂ (spectralKLTestSynthesis g) (hLp.toLp f) =
      ∫ t : ℝ, (starRingEnd ℂ) (g.val t)*spectralKLPhysicalAnalysisIntegral f t ∂spectralKLSpectralMeasure := by
  let G : ℝ → ℂ := fun t => (starRingEnd ℂ) ((spectralKLPlancherelWeight t : ℂ)*g.val t)
  have hG : Continuous G := by
    exact Complex.continuous_conj.comp
      ((Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous).mul g.property.1.continuous)
  have hGc : HasCompactSupport G :=
    (g.property.2.1.mul_left).comp_left (map_zero (starRingEnd ℂ))
  have hGeq (x : ℝ) (hx : 0 < x) :
      (starRingEnd ℂ) (spectralKLWeightedSynthesis g x) = spectralKLSynthesis G x := by
    rw [spectralKLWeightedSynthesis_eq g g.property.2.2 hx]
    exact (spectralKLSynthesis_conj _ x).symm
  have hinner :
      inner ℂ (spectralKLTestSynthesis g) (hLp.toLp f) =
        ∫ x : ℝ, f x*(starRingEnd ℂ) (spectralKLWeightedSynthesis g x) ∂spectralKLPhysicalMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [spectralKLTestSynthesis_coe g,
      hLp.coeFn_toLp] with x hS hF
    rw [RCLike.inner_apply,hS,hF]
  have hphys :
      (∫ x : ℝ, f x*(starRingEnd ℂ) (spectralKLWeightedSynthesis g x) ∂spectralKLPhysicalMeasure) =
        ∫ x in Ioi (0 : ℝ), (x⁻¹ : ℝ)* (f x*(starRingEnd ℂ) (spectralKLWeightedSynthesis g x)) :=
    spectralKLPositiveWeightMeasure_complex_integral _ _ (by fun_prop)
      (fun x hx => inv_nonneg.mpr hx.le)
  have hspec :
      (∫ t : ℝ, (starRingEnd ℂ) (g.val t)*spectralKLPhysicalAnalysisIntegral f t ∂spectralKLSpectralMeasure) =
        ∫ t in Ioi (0 : ℝ), (spectralKLPlancherelWeight t : ℂ)*
          ((starRingEnd ℂ) (g.val t)*spectralKLPhysicalAnalysisIntegral f t) :=
    spectralKLPositiveWeightMeasure_complex_integral _ _ spectralKLPlancherelWeight_continuous.measurable
      (fun t ht => (spectralKLPlancherelWeight_pos ht).le)
  rw [hinner,hphys,hspec]
  calc
    _ = ∫ x in Ioi (0 : ℝ), spectralKLSynthesis G x*spectralKLPhysicalCompactDiv f x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [hGeq x hx]
      simp only [spectralKLPhysicalCompactDiv,Complex.ofReal_inv,div_eq_mul_inv]
      ring
    _ = ∫ x : ℝ, spectralKLSynthesis G x*spectralKLPhysicalCompactDiv f x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hf0 : f x = 0 := hfzero x (le_of_not_gt hx)
      simp [spectralKLPhysicalCompactDiv,hf0]
    _ = ∫ t : ℝ, G t*spectralKLPhysicalAnalysisIntegral f t :=
      spectralKL_majorant_fubini f G hf hfzero hM hG hGc
    _ = ∫ t in Ioi (0 : ℝ), G t*spectralKLPhysicalAnalysisIntegral f t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hg0 : g.val t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (g.property.2.2 h))
      simp [G,hg0]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [G,map_mul,Complex.conj_ofReal]
      ring

end ArtinMatthews
