module

public import ArtinMatthews.SourceRowIntegralNumerator
public import ArtinMatthews.SixthKummerSharpModulus
public import ArtinMatthews.PrincipalAngularCorrection
public import ArtinMatthews.SourceGaussCharacter
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

/-! The exact exterior zero mask of the actual sharp Kummer modulus. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourceWildPrimes_subset : sixthWildPrimes F ⊆ sourceHilbertSet F S₀ := by
  intro P hP
  by_contra hn
  exact source_exterior_six_not_mem F S₀ P hn ((mem_sixthWildPrimes P).mp hP)

theorem sourceDistinctPrime_coprime (P Q : ProbePrime F) (h : P ≠ Q) :
    IsCoprime P.asIdeal Q.asIdeal := by
  apply principalAngular_prime_coprime_of_not_le P Q.asIdeal
  intro hle
  exact h (HeightOneSpectrum.asIdeal_injective (Q.isMaximal.eq_of_le P.isPrime.ne_top hle).symm)

include hζ in
theorem sourceRowKummerSharp_coprime_iff (u : sourceRing F S₀) (hu : u ≠ 0)
    (P : SourceExteriorPrime F S₀) :
    IsCoprime P.val.asIdeal (sixthKummerSharpIdeal (sourceHilbertSet F S₀) (sourceRowFieldUnit F S₀ u hu)) ↔
      sourceElementExponents F S₀ u hu P = 0 := by
  let S := sourceHilbertSet F S₀
  let v := sourceRowFieldUnit F S₀ u hu
  have h := sourceRowFieldUnit_count_zero_iff F S₀ hζ u hu P
  constructor
  · intro hc
    by_contra hj
    have hv : exteriorPrincipalValuation P.val v ≠ 0 := fun h0 => hj (h.mp h0)
    have hle := Ideal.dvd_iff_le.mp (sixthKummerSharpIdeal_radical_dvd S v P.val P.property hv)
    have ht := Ideal.isCoprime_iff_sup_eq.mp hc
    rw [sup_eq_left.mpr hle] at ht
    exact P.val.isPrime.ne_top ht
  · intro hj
    have hv : exteriorPrincipalValuation P.val v = 0 := h.mpr hj
    change IsCoprime P.val.asIdeal (sixthKummerSharpIdeal S v)
    unfold sixthKummerSharpIdeal sixthKummerFixedIdeal sixthExteriorRadicalIdeal
    apply IsCoprime.mul_right
    · apply IsCoprime.prod_right
      intro Q hQ
      have hne : P.val ≠ Q := fun he => P.property (he.symm ▸ hQ)
      exact (sourceDistinctPrime_coprime F P.val Q hne).pow_right
    · apply IsCoprime.prod_right
      intro Q hQ
      have hne : P.val ≠ Q := fun he =>
        ((mem_sixthExteriorRadicalPrimes S v Q).mp hQ).2 (he ▸ hv)
      exact sourceDistinctPrime_coprime F P.val Q hne

end
end ArtinMatthews.SourceEulerAssembly
