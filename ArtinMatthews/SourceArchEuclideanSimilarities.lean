module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicVolume
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

/-! Exact differentials of the three genuine hyperbolic generators. -/
namespace ArtinMatthews.SourceArchJacquet
open OAI.CubicEisenstein
noncomputable section

lemma sourceArchWeylReflection_norm (x : EuclideanSpatial) :
    ‖euclideanWeylReflection x‖ = ‖x‖ := by
  obtain ⟨h0, h1, h2⟩ := euclideanWeylReflection_apply x
  have hs : ‖euclideanWeylReflection x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h0, h1, h2, neg_sq]
  nlinarith [norm_nonneg (euclideanWeylReflection x), norm_nonneg x]

lemma sourceArchComplexDilation_norm (b : ℂ) (x : EuclideanSpatial) :
    ‖euclideanComplexDilation b x‖ = Complex.normSq b * ‖x‖ := by
  obtain ⟨h0, h1, h2⟩ := euclideanComplexDilation_apply b x
  have hc : (b ^ 2).re ^ 2 + (b ^ 2).im ^ 2 = (Complex.normSq b) ^ 2 := by
    simpa [Complex.normSq_apply, sq] using map_pow Complex.normSq b 2
  have hs : ‖euclideanComplexDilation b x‖ ^ 2 =
      (Complex.normSq b) ^ 2 * ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h0, h1, h2]
    calc
      _ = ((b ^ 2).re ^ 2 + (b ^ 2).im ^ 2) * (x 0 ^ 2 + x 1 ^ 2) +
          (Complex.normSq b) ^ 2 * x 2 ^ 2 := by ring
      _ = _ := by rw [hc]; ring
  nlinarith [norm_nonneg (euclideanComplexDilation b x), norm_nonneg x,
    Complex.normSq_nonneg b, mul_nonneg (Complex.normSq_nonneg b) (norm_nonneg x)]

def sourceArchWeylDerivative (p : EuclideanSpatial) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanWeylReflection.comp (euclideanInversionDeriv p)

lemma sourceArchWeyl_hasFDerivAt (p : EuclideanSpatial) (hp : p ≠ 0) :
    HasFDerivAt euclideanWeylAction (sourceArchWeylDerivative p) p :=
  euclideanWeylReflection.hasFDerivAt.comp p (euclideanInversion_hasFDerivAt p hp)

lemma sourceArchWeylDerivative_norm (p v : EuclideanSpatial) :
    ‖sourceArchWeylDerivative p v‖ = (1 / ‖p‖) ^ 2 * ‖v‖ := by
  rw [sourceArchWeylDerivative, ContinuousLinearMap.comp_apply, sourceArchWeylReflection_norm]
  simp only [euclideanInversionDeriv, smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (1 / ‖p‖))]
  exact congrArg (fun t : ℝ => (1 / ‖p‖) ^ 2 * t) (((ℝ ∙ p)ᗮ).reflection.norm_map v)

end
end ArtinMatthews.SourceArchJacquet
