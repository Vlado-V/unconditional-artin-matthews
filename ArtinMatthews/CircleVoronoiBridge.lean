module

public import ArtinMatthews.CircleShiftedFrequency
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
public import ArtinMatthews.ShiftedDoubleVoronoiFubini
public import ArtinMatthews.CircleSourceSupport
public import ArtinMatthews.CircleVoronoiSource
public import ArtinMatthews.ShiftedDoubleVoronoiSquarefree
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Exact bridge from the finite Ramanujan source average to the already
proved double Voronoi identity, including every normalization and congruence. -/

noncomputable section
open Complex UpperHalfPlane Set
open scoped MatrixGroups ContDiff BigOperators
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews

theorem circle_weightOne_voronoi_squarefree
    (N : ℕ) [NeZero N] (hN : 3∣N) (f : CuspForm (cubicThetaKernel N) 1)
    (m1 m2 H K1 K2 : ℕ) [NeZero H] [NeZero (m1.gcd m2)]
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hne : m1≠m2)
    (hsq1 : Squarefree m1) (hsq2 : Squarefree m2)
    (hQ : N*(shiftedCommonPrimePart m1 m2)^2∣H*(m1.gcd m2))
    (hc : ((m1/(m1.gcd m2))*(m2/(m1.gcd m2))).Coprime (H*(m1.gcd m2)))
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0<u1) (hu2 : 0<u2)
    (hv1 : v1≤K1) (hv2 : v2≤K2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    let d := m1.gcd m2
    let v3 := ZMod.unitOfCoprime (m1/d) (Nat.coprime_mul_iff_left.mp hc).1
    let v4 := ZMod.unitOfCoprime (m2/d) (Nat.coprime_mul_iff_left.mp hc).2
    (∑ k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2),
      cuspSourcePair f H1 H2 k * primitiveCircleSum (H*d)
        (circleShiftedFrequency (m1/d) (m2/d) k) *
        (if (d : ℤ)∣((k.1 : ℤ)-1) then 1 else 0)) =
      (cubicThetaNebentypus (-((m1/d : ℕ) : ℤ)*(m2/d : ℕ)) / ((H*d : ℕ) : ℂ)^2) *
        ∑' k : ℕ×ℕ, cuspBesselPair f (H*d) H1 H2 k *
          ((if Int.ModEq (shiftedCommonPrimePart m1 m2 : ℤ)
            (((m1/d : ℕ) : ℤ)^2*k.1) (((m2/d : ℕ) : ℤ)^2*k.2) then 1 else 0) *
            sum ZMod.stdAddChar ((v3 : ZMod (H*d))-(v4 : ZMod (H*d)))
              ((↑(v3*v4)⁻¹ : ZMod (H*d))*((v4 : ZMod (H*d))*k.2-(v3 : ZMod (H*d))*k.1))) := by
  intro d v3 v4
  have hsource := circle_source_sum H d (m1/d) (m2/d) v3 v4
    (by simp only [v3,ZMod.coe_unitOfCoprime]) (by simp only [v4,ZMod.coe_unitOfCoprime])
    ((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)) (cuspSourcePair f H1 H2)
    (cuspSourcePair_eq_zero_of_not_box f H1 H2 K1 K2 u1 v1 u2 v2 hu1 hu2 hv1 hv2 hw1 hw2)
  rw [← hsource]
  exact weightOne_double_voronoi_squarefree N hN f m1 m2 H hm1 hm2 hne hsq1 hsq2 hQ hc
    H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2

end ArtinMatthews
