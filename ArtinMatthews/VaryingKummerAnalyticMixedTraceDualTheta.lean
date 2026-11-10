module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualMatrix
public import ArtinMatthews.VaryingKummerAnalyticMixedTheta
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualNorm
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

/-! Poisson summation with its dual sum indexed by the actual trace-dual ideal. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField NumberField.mixedEmbedding
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedDualIntegerEquiv_embedding (z : MixedIdealIndex K I → ℤ) :
    mixedTraceTransform K (mixedFieldEmbedding K (mixedDualIntegerEquiv K I z : K)) =
      mixedDualMatrixVector K I z := by
  exact congrArg Subtype.val ((mixedTraceIdealToDualLattice K I).apply_symm_apply
    (mixedDualIntegerToLattice K I z))

theorem mixedDualIntegerEquiv_norm (z : MixedIdealIndex K I → ℤ) :
    ‖adjointEquiv (mixedIdealMatrix K I).symm (euclideanInteger z)‖ =
      ‖mixedTraceTransform K (mixedFieldEmbedding K (mixedDualIntegerEquiv K I z : K))‖ := by
  rw [mixedDualIntegerEquiv_embedding, mixedDualMatrixVector,
    LinearIsometryEquiv.norm_map]

/-- The adjoint-matrix Gaussian sum equals the literal trace-dual ideal sum. -/
theorem normalizedTheta_adjoint_eq_traceDual (t : ℝ) :
    normalizedTheta (adjointEquiv (mixedIdealMatrix K I).symm) t =
      ∑' b : (mixedTraceDualIdeal K I).1,
        Complex.exp (-((Real.pi * t : ℝ) : ℂ) *
          ‖mixedTraceTransform K (mixedFieldEmbedding K (b : K))‖ ^ 2) := by
  unfold normalizedTheta latticeTheta
  simp_rw [mixedDualIntegerEquiv_norm]
  exact (mixedDualIntegerEquiv K I).tsum_eq (fun b : (mixedTraceDualIdeal K I).1 =>
    Complex.exp (-((Real.pi * t : ℝ) : ℂ) *
      ‖mixedTraceTransform K (mixedFieldEmbedding K (b : K))‖ ^ 2))

/-- Actual number-field Poisson inversion, including all real and complex
places in the dual archimedean weight. -/
theorem mixedIdealTheta_inversion_traceDual {t : ℝ} (ht : 0 < t) :
    mixedIdealTheta K I t =
      (((((FractionalIdeal.absNorm I.1 : ℝ) *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)⁻¹) : ℝ) : ℂ) *
      (t : ℂ)^(-(((Module.finrank ℚ K : ℕ) : ℂ)/2)) *
      ∑' b : (mixedTraceDualIdeal K I).1,
        Complex.exp (-((Real.pi * t⁻¹ : ℝ) : ℂ) *
          ((∑ w : InfinitePlace K, ((w.mult : ℝ) * w (b : K)) ^ 2 : ℝ) : ℂ)) := by
  rw [mixedIdealTheta_inversion_discriminant K I ht,
    normalizedTheta_adjoint_eq_traceDual]
  congr 2
  funext b
  rw [← Complex.ofReal_pow, mixedTraceTransform_embedding_norm_sq]

end
end ArtinMatthews.VaryingKummerAnalytic
