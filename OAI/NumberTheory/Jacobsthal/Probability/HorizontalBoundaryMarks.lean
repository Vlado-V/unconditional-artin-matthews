module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Estimates.BivariateCalculus
public import OAI.NumberTheory.Jacobsthal.Estimates.RealCriticalPoints
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
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
public import OAI.NumberTheory.Jacobsthal.Harmonic.RealAlgebraicFibers
public import OAI.NumberTheory.Jacobsthal.Partitions.InflectionTransport


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection

theorem horizontalLine_ne_zero (z : ℂ) : affineLine 0 z ≠ 0 := by
  intro hz
  have h := congrArg (MvPolynomial.eval ![(0 : ℂ),z+1]) hz
  simp [affineLine] at h

theorem nonlinear_not_dvd_horizontal (Q : MV ℂ) (hdeg : 1 < Q.totalDegree) (z : ℂ) :
    ¬Q ∣ affineLine 0 z := by
  intro hdiv
  have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv (horizontalLine_ne_zero z)
  exact (not_le_of_gt hdeg) (hd.trans (affineLine_degree_le 0 z))

def boundaryAbscissae (Q : MV ℝ) (y : ℝ) : Set ℝ := {x | peval Q x y = 0}

theorem boundary_abscissae_bound (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (y : ℝ) :
    (boundaryAbscissae Q y).Finite ∧ (boundaryAbscissae Q y).ncard ≤ 2*Q.totalDegree := by
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hfin,hcard⟩ := irreducible_abscissa_bound (complexify Q) (affineLine 0 (y : ℂ)) hQ hd
    (nonlinear_not_dvd_horizontal _ hd y)
  have hpre := finite_real_preimage (intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ))) hfin
  have hsub : boundaryAbscissae Q y ⊆
      Complex.ofReal ⁻¹' intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ)) := by
    intro x hx
    refine ⟨((x : ℂ),(y : ℂ)),⟨?_,?_⟩,rfl⟩
    · rw [complexify_eval,← peval_eq_eval_pair]
      change peval Q x y = 0 at hx
      rw [hx,Complex.ofReal_zero]
    · simp [affineLine]
  refine ⟨hpre.1.subset hsub,?_⟩
  calc
    _ ≤ (Complex.ofReal ⁻¹' intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ))).ncard :=
      ncard_le_ncard hsub hpre.1
    _ ≤ _ := hpre.2
    _ ≤ _ := hcard
    _ ≤ 2*(complexify Q).totalDegree*1 := Nat.mul_le_mul_left _ (affineLine_degree_le 0 y)
    _ = 2*Q.totalDegree := by rw [mul_one,complexify_totalDegree]

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
