module

public import ArtinMatthews.SIntegerLocalCOne
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

/-! Exact one-outer-degree source table, including the positive
modulus principal-character mask and the actual generator Gauss sum. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem standardLocalCOne_eq (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hχ : orderOf χ = 6) (hminus : χ (-1) = 1) (n J : ℕ) :
    standardLocalCOne S₀ P hP a ha χ n J =
      if n + 1 ≤ J then residueSourceTau S₀ P hP a ha χ *
        (Ideal.absNorm P.asIdeal : ℂ) ^ n *
        (if n + 1 = J then residueSourceTau S₀ P hP a ha (χ ^ n)
          else if 6 ∣ n then (Ideal.absNorm P.asIdeal : ℂ) - 1 else 0)
      else 0 := by
  rw [standardLocalCOne_lift S₀ P hP a ha hbad χ hminus]
  by_cases hnJ : n + 1 ≤ J
  · rw [ite_eq_left hnJ, ite_eq_left hnJ]
    by_cases he : n + 1 = J
    · subst J
      rw [ite_eq_left rfl, Nat.sub_self, pow_zero, residueTransformOnSource_one]
    · have hm : a ^ (J - (n + 1)) ∈
          P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
        have hm' := (generator_power_mem_iff S₀ P hP a ha 1 (J - (n + 1))).mpr (by omega)
        simpa only [pow_one] using hm'
      rw [ite_eq_right he, residueTransformOnSource_sixth S₀ P hP a ha hbad χ hχ,
        ite_eq_left hm]
  · rw [ite_eq_right hnJ, ite_eq_right hnJ]

end
end ArtinMatthews.SIntegerFourier
