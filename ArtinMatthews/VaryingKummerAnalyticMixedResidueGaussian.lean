module

public import ArtinMatthews.VaryingKummerAnalyticMixedResidueTheta
public import ArtinMatthews.VaryingKummerAnalyticMixedRadialCoordinates
public import ArtinMatthews.VaryingKummerAnalyticMixedGaussianNorm
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
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

/-! Literal mixed residue theta is the weighted sum over actual nonzero ideal
elements; all archimedean factors retain the real/complex multiplicities. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedComplexArchGaussian (a : K) (t : ℝ) (u : logSpace K) : ℂ :=
  Complex.exp (-((Real.pi*t*mixedArchEnergy K a u : ℝ) : ℂ))

theorem mixedComplexArchGaussian_enorm (a : K) (t : ℝ) (u : logSpace K) :
    ‖mixedComplexArchGaussian K a t u‖ₑ = mixedArchGaussian K a t u := by
  rw [← ofReal_norm, mixedComplexArchGaussian, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  unfold mixedArchGaussian mixedArchEnergy
  congr 2
  ring

theorem mixedIntegralIdealFlow_norm_sq (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : I) (u : logSpace K) :
    ‖logScaledLattice (mixedIdealMatrix K (integralIdealFractionalUnit I hI))
      (mixedIdealLogScale K (integralIdealFractionalUnit I hI) u)
      (euclideanInteger ((mixedIntegralIdealBasis K I hI).equivFun a))‖^2 =
        mixedArchEnergy K ((a : 𝓞 K) : K) u := by
  let J := integralIdealFractionalUnit I hI
  let b := fractionalIdealBasis K J.val
  have hb : b.equivFun.symm ((mixedIntegralIdealBasis K I hI).equivFun a) =
      integralIdealToFractional K I hI a := by
    simp [mixedIntegralIdealBasis, b, J]
  have hv : logScaledLattice (mixedIdealMatrix K J) (mixedIdealLogScale K J u)
      (euclideanInteger ((mixedIntegralIdealBasis K I hI).equivFun a)) =
      logScale (mixedIdealLogScale K J u) ((mixedIdealOrthonormalBasis K J).repr
        (mixedIdealEmbedding K J (integralIdealToFractional K I hI a))) := by
    change logScale _ ((mixedIdealOrthonormalBasis K J).repr
      ((mixedIdealEuclideanBasis K J).equivFun.symm
        (fun j => (((mixedIntegralIdealBasis K I hI).equivFun a) j : ℝ)))) = _
    rw [mixedIdealEuclideanBasis_integer_apply, hb]
  rw [hv, mixedIdealFlow_norm_sq]
  rfl

theorem mixedIdealResidueFlowTheta_eq_complex (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (N : ℕ) (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : logSpace K) (t : ℝ) :
    mixedIdealResidueFlowTheta K I hI N χ u t =
      ∑' a : I, χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (a : 𝓞 K)) *
        mixedComplexArchGaussian K ((a : 𝓞 K) : K) t u := by
  unfold mixedIdealResidueFlowTheta idealCharacterTheta
  apply tsum_congr
  intro a
  congr 1
  rw [← Complex.ofReal_pow, mixedIntegralIdealFlow_norm_sq]
  unfold mixedComplexArchGaussian
  congr 1
  push_cast
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
