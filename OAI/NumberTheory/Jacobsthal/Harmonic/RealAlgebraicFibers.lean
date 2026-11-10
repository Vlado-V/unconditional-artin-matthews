module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Estimates.RealCriticalPoints
public import OAI.NumberTheory.Jacobsthal.Harmonic.PolynomialLocalGraph
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.NumberTheory.Jacobsthal.Partitions.InflectionTransport


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection ErdosLocalFiberGraphs

theorem finite_real_preimage (A : Set ℂ) (hA : A.Finite) :
    (Complex.ofReal ⁻¹' A).Finite ∧ (Complex.ofReal ⁻¹' A).ncard ≤ A.ncard := by
  refine ⟨hA.preimage Complex.ofReal_injective.injOn,?_⟩
  exact ncard_le_ncard_of_injOn Complex.ofReal (fun _ h => h) Complex.ofReal_injective.injOn hA

theorem real_vertical_nonzero (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (x : ℝ) : verticalPolynomial Q x ≠ 0 := by
  intro hz
  have hdegC : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  let P := ErdosBivariateResultant.specialize (nestedY ℂ (complexify Q)) (x : ℂ)
  have hp : P ≠ 0 := nonlinear_fibers_nonzero (complexify Q) hQ hdegC x
  have hroot : ∀ y : ℝ, P.IsRoot (y : ℂ) := by
    intro y
    have hy : peval Q x y = 0 := by rw [← verticalPolynomial_eval,hz,Polynomial.eval_zero]
    change ErdosBivariateResultant.beval (nestedY ℂ (complexify Q)) (x : ℂ) (y : ℂ) = 0
    rw [beval_nested,complexify_eval,← peval_eq_eval_pair,hy,Complex.ofReal_zero]
  have hinf : (range Complex.ofReal).Infinite := infinite_range_of_injective Complex.ofReal_injective
  apply hinf
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  rintro y ⟨z,rfl⟩
  exact hroot z

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
