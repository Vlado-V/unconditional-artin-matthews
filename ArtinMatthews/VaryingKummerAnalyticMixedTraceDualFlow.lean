module

public import ArtinMatthews.VaryingKummerAnalyticMixedGaussianUnfolding
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualMatrix
public import ArtinMatthews.VaryingKummerAnalyticMixedUnitAverage
public import ArtinMatthews.VaryingKummerAnalyticMixedDeterminant
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualTheta
public import ArtinMatthews.VaryingKummerAnalyticThetaDualAverages
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual trace-dual ideal enumeration for the complete logarithmic Gaussian flow. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedTraceDual_coordinate (b : K) (j : MixedIdealIndex K I) :
    (mixedIdealOrthonormalBasis K I).repr
      (mixedTraceTransform K (mixedFieldEmbedding K b)) j =
      (mixedEmbedding.stdBasis K).repr
        (mixedTraceTransformRaw K (mixedEmbedding K b)) (mixedIdealIndexEquiv K I j) := by
  rfl

theorem mixedTraceDualFlow_norm_sq (b : K) (u : logSpace K) :
    ‖logScale (mixedIdealLogScale K I u)
      ((mixedIdealOrthonormalBasis K I).repr
        (mixedTraceTransform K (mixedFieldEmbedding K b)))‖ ^ 2 =
      ∑ w : InfinitePlace K, ((w.mult : ℝ) * mixedPlaceWeight K u w * w b)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [logScale_apply, mixedTraceDual_coordinate]
  change (∑ j, (Real.exp (mixedStandardLogScale K u (mixedIdealIndexEquiv K I j)) *
    (mixedEmbedding.stdBasis K).repr (mixedTraceTransformRaw K (mixedEmbedding K b))
      (mixedIdealIndexEquiv K I j))^2) = _
  rw [(mixedIdealIndexEquiv K I).sum_comp (fun j =>
    (Real.exp (mixedStandardLogScale K u j) *
      (mixedEmbedding.stdBasis K).repr (mixedTraceTransformRaw K (mixedEmbedding K b)) j)^2),
    Fintype.sum_sum_type, InfinitePlace.sum_eq_sum_add_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    simp only [mixedStandardLogScale, mixedPlaceWeight,
      InfinitePlace.mult_isReal w, Nat.cast_one, div_one, one_mul,
      mixedEmbedding.stdBasis_apply_isReal]
    change (Real.exp _ * InfinitePlace.embedding_of_isReal w.property b)^2 = _
    rw [mul_pow, mul_pow, ← InfinitePlace.norm_embedding_of_isReal w.property,
      Real.norm_eq_abs, sq_abs]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Fin.sum_univ_two, mixedStandardLogScale,
      mixedEmbedding.stdBasis_apply_isComplex_fst,
      mixedEmbedding.stdBasis_apply_isComplex_snd,
      mixedPlaceWeight, InfinitePlace.mult_isComplex w, Nat.cast_ofNat]
    change (Real.exp _ * ((2 : ℂ) * star (w.1.embedding b)).re)^2 +
      (Real.exp _ * ((2 : ℂ) * star (w.1.embedding b)).im)^2 = _
    rw [← InfinitePlace.norm_embedding_eq]
    simp only [mul_pow, Complex.sq_norm, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    norm_num
    ring

theorem mixedDualIntegerEquiv_coordinates (z : MixedIdealIndex K I → ℤ) :
    adjointEquiv (mixedIdealMatrix K I).symm (euclideanInteger z) =
      (mixedIdealOrthonormalBasis K I).repr
        (mixedTraceTransform K (mixedFieldEmbedding K (mixedDualIntegerEquiv K I z : K))) := by
  rw [mixedDualIntegerEquiv_embedding, mixedDualMatrixVector,
    LinearIsometryEquiv.apply_symm_apply]

/-- The actual trace-dual ideal Gaussian, with arbitrary logarithmic weights. -/
theorem normalizedTheta_logScaled_adjoint_eq_traceDual (u : logSpace K) (t : ℝ) :
    normalizedTheta (logScaledLattice (adjointEquiv (mixedIdealMatrix K I).symm)
      (mixedIdealLogScale K I u)) t =
      ∑' b : (mixedTraceDualIdeal K I).1,
        Complex.exp (-((Real.pi * t : ℝ) : ℂ) *
          ((∑ w : InfinitePlace K,
            ((w.mult : ℝ) * mixedPlaceWeight K u w * w (b : K))^2 : ℝ) : ℂ)) := by
  unfold normalizedTheta latticeTheta
  change (∑' z : MixedIdealIndex K I → ℤ,
    Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
      ‖logScale (mixedIdealLogScale K I u)
        (adjointEquiv (mixedIdealMatrix K I).symm (euclideanInteger z))‖^2)) = _
  simp_rw [mixedDualIntegerEquiv_coordinates, ← Complex.ofReal_pow,
    mixedTraceDualFlow_norm_sq]
  exact (mixedDualIntegerEquiv K I).tsum_eq (fun b : (mixedTraceDualIdeal K I).1 =>
    Complex.exp (-((Real.pi * t : ℝ) : ℂ) *
      ((∑ w : InfinitePlace K,
        ((w.mult : ℝ) * mixedPlaceWeight K u w * w (b : K))^2 : ℝ) : ℂ)))

theorem mixedIdealLogScale_neg (u : logSpace K) :
    mixedIdealLogScale K I (-u) = -mixedIdealLogScale K I u := by
  funext j
  change mixedStandardLogScale K (-u) (mixedIdealIndexEquiv K I j) =
    -mixedStandardLogScale K u (mixedIdealIndexEquiv K I j)
  cases mixedIdealIndexEquiv K I j <;>
    simp only [mixedStandardLogScale, mixedRestoredPlaceLog] <;>
    split_ifs <;> simp <;> ring

/-- The complete Gaussian flow Poisson identity with literal trace-dual ideal
and opposite unit-log weight. -/
theorem mixedIdealFlowTheta_inversion_traceDual (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    mixedIdealFlowTheta K I u t =
      (((((FractionalIdeal.absNorm I.1 : ℝ) *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)⁻¹) : ℝ) : ℂ) *
      (t : ℂ)^(-(((Module.finrank ℚ K : ℕ) : ℂ)/2)) *
      ∑' b : (mixedTraceDualIdeal K I).1,
        Complex.exp (-((Real.pi * t⁻¹ : ℝ) : ℂ) *
          ((∑ w : InfinitePlace K,
            ((w.mult : ℝ) * mixedPlaceWeight K (-u) w * w (b : K))^2 : ℝ) : ℂ)) := by
  rw [mixedIdealFlowTheta_eq_normalizedTheta, normalizedTheta_inversion _ t ht,
    adjointEquiv_logScaledLattice, ← mixedIdealLogScale_neg,
    normalizedTheta_logScaled_adjoint_eq_traceDual, logScaledLattice_det,
    mixedIdealLogScale_sum, Real.exp_zero, one_mul, abs_inv,
    mixedIdealMatrix_abs_det, mixedIdealIndex_card]

end
end ArtinMatthews.VaryingKummerAnalytic
