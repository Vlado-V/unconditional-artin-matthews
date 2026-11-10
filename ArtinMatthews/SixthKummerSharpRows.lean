module

public import ArtinMatthews.SixthExteriorIdealRowClasses
public import ArtinMatthews.SixthKummerSharpRay
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity
public import ArtinMatthews.SixthKummerSharpPrimitive
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

/-! The sharp conductor bound on the literal bounded ideal row family.
The exterior radical is proved to divide the indexing ideal, so the
conductor estimate retains the actual ideal norm cutoff. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F]

theorem sixthExteriorRadicalIdeal_dvd_of_valuations
    (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ) (I : Ideal (𝓞 F)) (hI : I ≠ 0)
    (hval : ∀ p, p ∉ S → exteriorPrincipalValuation p u=
      FractionalIdeal.count F p (I:FractionalIdeal (𝓞 F)⁰ F)) :
    sixthExteriorRadicalIdeal S u ∣ I := by
  let T := (sixthExteriorRadicalPrimes S u).image (fun p => p.asIdeal)
  have hp : ∀ P ∈ T, Prime P := by
    intro P hP
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hP
    exact p.prime
  have hd : ∀ P ∈ T, P ∣ I := by
    intro P hP
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hpS,hpu⟩ := (mem_sixthExteriorRadicalPrimes S u p).mp hp
    have hc : FractionalIdeal.count F p (I:FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      rwa [← hval p hpS]
    rw [FractionalIdeal.count_coe F p hI,Int.natCast_ne_zero,
      Associates.count_ne_zero_iff_dvd hI p.irreducible] at hc
    exact hc
  have h := Finset.prod_primes_dvd I hp hd
  have hprod : (∏ P ∈ T, P)=sixthExteriorRadicalIdeal S u := by
    unfold T sixthExteriorRadicalIdeal
    rw [Finset.prod_image]
    intro p _ q _ hpq
    exact HeightOneSpectrum.ext hpq
  rwa [hprod] at h

theorem sixthExteriorRadicalIdeal_absNorm_le_of_valuations
    (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ) (I : Ideal (𝓞 F)) (hI : I ≠ 0)
    (hval : ∀ p, p ∉ S → exteriorPrincipalValuation p u=
      FractionalIdeal.count F p (I:FractionalIdeal (𝓞 F)⁰ F)) :
    (sixthExteriorRadicalIdeal S u).absNorm ≤ I.absNorm :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm (sixthExteriorRadicalIdeal_dvd_of_valuations S u I hI hval))

theorem exteriorBoundedIdealRow_radical_norm_le
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : exteriorPrincipalizingPrimes F ⊆ S)
    (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    (sixthExteriorRadicalIdeal S (exteriorBoundedIdealRowUnit S N i)).absNorm ≤ N := by
  have hi := (mem_exteriorBoundedIdealRows S N i.1.1).mp i.1.2
  exact (sixthExteriorRadicalIdeal_absNorm_le_of_valuations S _ i.1.1 hi.2.1
    (fun p hp => exteriorIdealRow_valuation S hS _ _ i.2.1 p hp)).trans hi.1

variable [Algebra F ℂ] [NumberField.IsTotallyComplex F]

theorem exists_boundedIdealRow_primitive_conductor {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hWild : sixthWildPrimes F ⊆ S)
    (hClass : exteriorPrincipalizingPrimes F ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    ∃ (f : Ideal (𝓞 F)) (_hf : f ≠ ⊥)
      (_hMf : sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i) ≤ f)
      (Ψ : EvenIdealRayCharacter F f), IsPrimitiveOnIdeals Ψ.residue ∧
      f.absNorm ≤ (sixthKummerFixedIdeal S).absNorm*N ∧
      (∀ I : RayClass.primeToModulusIdeals (integralIdealRayModulus
          (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i))
          (sixthKummerSharpIdeal_ne_zero S _)),
        Ψ.idealHom (I:FractionalIdealGroup F)=GaloisIdealCharacter.idealHom F
          (sixthKummerRowField {(exteriorBoundedIdealRowUnit S N i:F)})
          (sixthKummerRowCharacter hζ {(exteriorBoundedIdealRowUnit S N i:F)}
            (exteriorBoundedIdealRowUnit S N i:F) (Finset.mem_singleton_self _) (Units.ne_zero _))
          (I:FractionalIdealGroup F)) ∧
      ∀ I : Ideal (𝓞 F),
        (sixthKummerSharpRayCharacter hζ S hWild (exteriorBoundedIdealRowUnit S N i)).allCoefficient I=
          if IsCoprime I (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i))
            then Ψ.allCoefficient I else 0 := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hnorm,hagree,hmask⟩ :=
    exists_sixthKummer_primitive_conductor hζ S hWild (exteriorBoundedIdealRowUnit S N i)
  exact ⟨f,hf,hMf,Ψ,hprim,hnorm.trans (Nat.mul_le_mul_left _
    (exteriorBoundedIdealRow_radical_norm_le S hClass N i)),hagree,hmask⟩

theorem exists_boundedIdealRow_nonprincipal_conductor {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hWild : sixthWildPrimes F ⊆ S)
    (hClass : exteriorPrincipalizingPrimes F ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N)
    (hu : ¬∃ t : F, t^6=(exteriorBoundedIdealRowUnit S N i:F)) :
    ∃ (f : Ideal (𝓞 F)) (_hf : f ≠ ⊥)
      (_hMf : sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i) ≤ f)
      (Ψ : EvenIdealRayCharacter F f), IsPrimitiveOnIdeals Ψ.residue ∧ Ψ.IsNonprincipal ∧
      f.absNorm ≤ (sixthKummerFixedIdeal S).absNorm*N ∧
      (∀ I : RayClass.primeToModulusIdeals (integralIdealRayModulus
          (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i))
          (sixthKummerSharpIdeal_ne_zero S _)),
        Ψ.idealHom (I:FractionalIdealGroup F)=GaloisIdealCharacter.idealHom F
          (sixthKummerRowField {(exteriorBoundedIdealRowUnit S N i:F)})
          (sixthKummerRowCharacter hζ {(exteriorBoundedIdealRowUnit S N i:F)}
            (exteriorBoundedIdealRowUnit S N i:F) (Finset.mem_singleton_self _) (Units.ne_zero _))
          (I:FractionalIdealGroup F)) ∧
      ∀ I : Ideal (𝓞 F),
        (sixthKummerSharpRayCharacter hζ S hWild (exteriorBoundedIdealRowUnit S N i)).allCoefficient I=
          if IsCoprime I (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i))
            then Ψ.allCoefficient I else 0 := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,hmask⟩ :=
    exists_sixthKummer_primitive_nonprincipal_conductor hζ S hWild
      (exteriorBoundedIdealRowUnit S N i) hu
  exact ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm.trans (Nat.mul_le_mul_left _
    (exteriorBoundedIdealRow_radical_norm_le S hClass N i)),hagree,hmask⟩

end
end ArtinMatthews
