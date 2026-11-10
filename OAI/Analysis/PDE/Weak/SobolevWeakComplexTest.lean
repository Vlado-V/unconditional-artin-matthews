module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.CStarAlgebra.Classes
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Weak.SobolevWeakCompactTest


set_option backward.privateInPublic true
@[expose] public section

open Set _root_.MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Weak

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  {μ : Measure X} [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ]

omit [BorelSpace X] [SecondCountableTopology X] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] in
/-- The real weak derivative identity also holds against complex C¹
test functions when the two pairings are integrable. -/
theorem HasWeakDirectionalDerivative.complex_test_of_compact_support
    {v : X} {u g : X → ℝ} (h : HasWeakDirectionalDerivative μ v u g)
    {K : Set X} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂μ, x ∉ K → u x = 0) (hg : ∀ᵐ x ∂μ, x ∉ K → g x = 0)
    {φ : X → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hgφ : Integrable (fun x ↦ (g x : ℂ) * φ x) μ)
    (huφ : Integrable (fun x ↦ (u x : ℂ) * fderiv ℝ φ x v) μ) :
    (∫ x, (g x : ℂ) * φ x ∂μ) = -(∫ x, (u x : ℂ) * fderiv ℝ φ x v ∂μ) := by
  have hφd (x : X) : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.differentiable (by norm_num) x).hasFDerivAt
  have hreD (x : X) : fderiv ℝ (fun x ↦ (φ x).re) x v = (fderiv ℝ φ x v).re := by
    exact congrArg (fun L : X →L[ℝ] ℝ ↦ L v)
      ((Complex.reCLM.hasFDerivAt.comp x (hφd x)).fderiv)
  have himD (x : X) : fderiv ℝ (fun x ↦ (φ x).im) x v = (fderiv ℝ φ x v).im := by
    exact congrArg (fun L : X →L[ℝ] ℝ ↦ L v)
      ((Complex.imCLM.hasFDerivAt.comp x (hφd x)).fderiv)
  have hre := h.test_of_compact_support hK hu hg (Complex.reCLM.contDiff.comp hφ)
  have him := h.test_of_compact_support hK hu hg (Complex.imCLM.contDiff.comp hφ)
  apply Complex.ext
  · rw [Complex.neg_re]
    change Complex.reCLM (∫ x, (g x : ℂ) * φ x ∂μ) =
      -Complex.reCLM (∫ x, (u x : ℂ) * fderiv ℝ φ x v ∂μ)
    rw [← Complex.reCLM.integral_comp_comm hgφ, ← Complex.reCLM.integral_comp_comm huφ]
    simpa [Function.comp_def, hreD, mul_comm] using hre
  · rw [Complex.neg_im]
    change Complex.imCLM (∫ x, (g x : ℂ) * φ x ∂μ) =
      -Complex.imCLM (∫ x, (u x : ℂ) * fderiv ℝ φ x v ∂μ)
    rw [← Complex.imCLM.integral_comp_comm hgφ, ← Complex.imCLM.integral_comp_comm huφ]
    simpa [Function.comp_def, himD, mul_comm] using him

end OAI.Analysis.PDE.Weak
