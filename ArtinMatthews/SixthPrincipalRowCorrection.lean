module

public import ArtinMatthews.SixthExteriorIdealRows
public import ArtinMatthews.SixthExteriorPowerClassesFinite
public import ArtinMatthews.SixthExteriorPowerClassesQuotient
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

/-! A fixed, genuine sixth-power correction for the principal ideal row.
It depends only on S and the existing generator/transversal choices, not
on a norm cutoff. Neither frozen choice is changed. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def unitIdealExteriorUnit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) : exteriorUnitSubgroup S :=
  ⟨exteriorIdealGenerator 1 one_ne_zero,by
    intro p hp
    rw [exteriorIdealGenerator_valuation 1 one_ne_zero p (fun h => hp (hS h))]
    simpa only [Ideal.one_eq_top,FractionalIdeal.coeIdeal_top] using FractionalIdeal.count_one K p⟩

structure PrincipalRowNormalizationData (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) where
  representative : exteriorUnitSubgroup S
  representative_mem : representative ∈ exteriorUnitSixthRepresentatives S
  root : exteriorUnitSubgroup S
  identity : unitIdealExteriorUnit S hS * representative = root^6

theorem principalRowNormalizationData_nonempty (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) : Nonempty (PrincipalRowNormalizationData S hS) := by
  obtain ⟨r,hr,t,ht⟩ := exteriorUnitSixthRepresentatives_complete S (unitIdealExteriorUnit S hS)⁻¹
  refine ⟨⟨r,hr,t⁻¹,?_⟩⟩
  rw [inv_pow]
  apply (eq_inv_iff_mul_eq_one).mpr
  rw [mul_assoc,← ht,mul_inv_cancel]

def principalRowNormalizer (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) : PrincipalRowNormalizationData S hS :=
  Classical.choice (principalRowNormalizationData_nonempty S hS)

def principalRowCorrection (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) : Kˣ :=
  ((principalRowNormalizer S hS).root : Kˣ)^6

theorem principalRowCorrection_eq_generator (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) :
    principalRowCorrection S hS = exteriorIdealGenerator 1 one_ne_zero *
      ((principalRowNormalizer S hS).representative : Kˣ) :=
  (congrArg Subtype.val (principalRowNormalizer S hS).identity).symm

theorem principalRowCorrection_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) : principalRowCorrection S hS ∈ exteriorUnitSubgroup S :=
  (exteriorUnitSubgroup S).pow_mem (principalRowNormalizer S hS).root.property 6

theorem principalRowCorrection_valuation (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    exteriorPrincipalValuation p (principalRowCorrection S hS) = 0 :=
  principalRowCorrection_mem S hS p hp

theorem principalRowCorrection_class (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) :
    QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) (principalRowCorrection S hS) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨((principalRowNormalizer S hS).root : Kˣ),rfl⟩

end
end ArtinMatthews
