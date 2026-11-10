module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Analysis.RealCoefficientNormalization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace OAI

namespace Erdos970

section

open Set
open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosAlgebraicCurve ErdosMarkedStrips

theorem nonreal_component_card_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (hreal : ¬RealScalable F) (S : ℝ) :
    (complexSquarePoints F S).card ≤ 2*F.totalDegree^3 := by
  have hnd := nonreal_not_dvd_conjugate F hF hreal
  obtain ⟨hfinite,hcard⟩ := irreducible_intersection_bound F (conjugate F) hF hdeg hnd
  have hmap : ∀ p ∈ (complexSquarePoints F S : Set (ℤ × ℤ)),
      complexIntPoint p ∈ intersectionPoints F (conjugate F) := by
    intro p hp
    have hz := ((mem_complexSquarePoints F S p).mp hp).2
    change MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0 ∧
      MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] (conjugate F) = 0
    refine ⟨hz,?_⟩
    simpa only [Complex.ofReal_intCast,hz,map_zero] using eval_conjugate_real F p.1 p.2
  have hc := ncard_le_ncard_of_injOn complexIntPoint hmap complexIntPoint_injective.injOn hfinite
  simp only [ncard_coe_finset] at hc
  calc
    _ ≤ _ := hc
    _ ≤ _ := hcard
    _ = 2*F.totalDegree^3 := by rw [conjugate_totalDegree]; ring

theorem realScalable_component_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (hreal : RealScalable F) (S : ℝ) (hS : 0 ≤ S) :
    ((complexSquarePoints F S).card : ℝ) ≤
      182*(F.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  obtain ⟨a,ha,R,rfl⟩ := hreal
  have hR := (scalar_irreducible_iff a ha (complexify R)).mp hF
  have hd : 1 < R.totalDegree := by
    simpa only [scalar_totalDegree a ha,complexify_totalDegree] using hdeg
  simpa only [complexSquare_scalar a ha,complexSquare_complexify,scalar_totalDegree a ha,
    complexify_totalDegree] using absolutely_irreducible_curve_lattice_bound R hR hd S hS

theorem irreducible_complex_curve_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (S : ℝ) (hS : 0 ≤ S) :
    ((complexSquarePoints F S).card : ℝ) ≤
      182*(F.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  by_cases hreal : RealScalable F
  · exact realScalable_component_bound F hF hdeg hreal S hS
  · have h := nonreal_component_card_bound F hF hdeg hreal S
    have hB : 1 ≤ 1+S^((2 : ℝ)/3) := le_add_of_nonneg_right (Real.rpow_nonneg hS _)
    calc
      ((complexSquarePoints F S).card : ℝ) ≤ 2*(F.totalDegree : ℝ)^3 := by exact_mod_cast h
      _ ≤ 182*(F.totalDegree : ℝ)^3 := by gcongr; norm_num
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hB

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
