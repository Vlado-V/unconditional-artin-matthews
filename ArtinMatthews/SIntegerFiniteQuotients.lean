module

public import ArtinMatthews.SIntegerFinitePrincipalization
public import ArtinMatthews.SIntegerPrincipalExterior
public import ArtinMatthews.SIntegerPrincipalQuotient
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
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

/-! Every nonzero ideal of the actual constructed S-integer ring has
a finite quotient. This follows from the proved exterior ideal
equivalence and the original number-field ideal quotient, not a finite
quotient hypothesis on the localized ring. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem principal_ideal_quotient_finite
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (J : Ideal (PrincipalIntegerRing S₀)) (hJ : J ≠ ⊥) :
    Finite ((PrincipalIntegerRing S₀) ⧸ J) := by
  let j : (Ideal (PrincipalIntegerRing S₀))⁰ :=
    ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩
  let I := (principalExteriorIdealEquiv S₀).symm j
  have hI : I.val.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = J :=
    congrArg Subtype.val ((principalExteriorIdealEquiv S₀).apply_symm_apply j)
  let : Finite ((𝓞 K) ⧸ I.val) := Ring.HasFiniteQuotients.finiteQuotient I.property.1
  exact Finite.of_equiv _ ((principalQuotientEquiv S₀ I.val I.property.2).toRingEquiv.trans
    (Ideal.quotEquivOfEq hI)).toEquiv

theorem principal_element_quotient_finite
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) :
    Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :=
  principal_ideal_quotient_finite S₀ _ (Ideal.span_singleton_eq_bot.not.mpr ha)

end
end ArtinMatthews.SIntegerQuotient
