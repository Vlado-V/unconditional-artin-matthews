module

public import ArtinMatthews.SIntegerLocalCZero
public import ArtinMatthews.SIntegerResidueGauss
public import ArtinMatthews.SIntegerResidueTransform
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Actual closed zero-outer-degree source table. The Gauss constants
are the literal standard generator-induced constants, and positive
principal character powers retain their zero mask. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem standardLocalCZero_eq (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hχ : orderOf χ = 6) (n J : ℕ) :
    standardLocalCZero S₀ P hP a ha χ n J =
      if n ≤ J then (Ideal.absNorm P.asIdeal : ℂ) ^ n *
        (if n = J then residueSourceTau S₀ P hP a ha (χ ^ (n + 1))
          else if 6 ∣ n + 1 then (Ideal.absNorm P.asIdeal : ℂ) - 1 else 0)
      else 0 := by
  by_cases hnJ : n ≤ J
  · rw [ite_eq_left hnJ, standardLocalCZero_lift S₀ P hP a ha χ n J hnJ]
    change (Ideal.absNorm P.asIdeal : ℂ) ^ n *
      residueTransformOnSource S₀ P hP a ha χ (n + 1) (a ^ (J - n)) = _
    by_cases he : n = J
    · subst J
      rw [ite_eq_left rfl, Nat.sub_self, pow_zero, residueTransformOnSource_one]
    · have hm : a ^ (J - n) ∈ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
        have hm' := (generator_power_mem_iff S₀ P hP a ha 1 (J - n)).mpr (by omega)
        simpa only [pow_one] using hm'
      rw [ite_eq_right he, residueTransformOnSource_sixth S₀ P hP a ha hbad χ hχ,
        ite_eq_left hm]
  · rw [ite_eq_right hnJ, standardLocalCZero_zero_off_support S₀ P hP a ha hbad χ n J
      (Nat.lt_of_not_ge hnJ)]

end
end ArtinMatthews.SIntegerFourier
