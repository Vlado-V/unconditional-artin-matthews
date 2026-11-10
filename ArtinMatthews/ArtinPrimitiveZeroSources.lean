module

public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.KummerTowerDiscriminantModulus
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.ArtinAbelianZeroDescent
public import ArtinMatthews.ArtinFrobeniusPrimitiveBoundary
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveContinuationTransfer
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
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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

/-! Exact zero sources of a genuine abelian extension. Every nonprincipal
source is an actual primitive ideal-conductor Hecke function, with the
explicit discriminant-degree conductor budget and full prime-to values.
The principal Dedekind factor remains separate. No zero-free region is assumed. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators IsMulCommutative
noncomputable section

instance primitiveArtinZeroModulus_neZero (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    NeZero (discriminantDegreeModulus K L) := ⟨(discriminantDegreeModulus_pos K L).ne'⟩

structure PrimitiveArtinZeroWitness (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (s : ℂ) where
  character : Gal(L/K) →* ℂˣ
  nontrivial : character ≠ 1
  conductor : Ideal (𝓞 K)
  conductor_ne_zero : conductor ≠ ⊥
  conductor_le : rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L) ≤ conductor
  primitiveCharacter : EvenIdealRayCharacter K conductor
  primitive : IsPrimitiveOnIdeals primitiveCharacter.residue
  nonprincipal : primitiveCharacter.IsNonprincipal
  norm_le : conductor.absNorm ≤ (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm
  agrees : ∀ I : primeToModulusIdeals (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
    primitiveCharacter.idealHom (I : FractionalIdealGroup K) =
      GaloisIdealCharacter.idealHom K L character (I : FractionalIdealGroup K)
  one_ne_zero : primitiveCharacter.primitiveContinued conductor_ne_zero primitive 1 ≠ 0
  zero : primitiveCharacter.primitiveContinued conductor_ne_zero primitive s = 0

namespace ArtinRay
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]

local instance zeroSourceCharactersFintype : Fintype (Gal(L/K) →* ℂˣ) := Fintype.ofFinite _

private def sourceRayFamily : (Gal(L/K) →* ℂˣ) →
    EvenRayCharacter K (discriminantDegreeModulus K L) :=
  fun χ => discriminantDegreeRayCharacter χ

private theorem sourceRayFamily_nonprincipal (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    (sourceRayFamily K L χ).IsNonprincipal := discriminantDegreeRayCharacter_isNonprincipal χ hχ

private theorem source_regularized_factorization {s : ℂ} (hs : 0 < s.re) :
    mixedRegularizedDedekindZeta L s = mixedRegularizedDedekindZeta K s *
      AbelianLocal.abelianArtinRelativeContinued K L (sourceRayFamily K L) s :=
  AbelianLocal.regularizedDedekindZeta_eq_mul_abelianArtinRelativeContinued K L
    (sourceRayFamily K L) (fun _ => rfl) (discr_dvd_discriminantDegreeModulus K L)
    (sourceRayFamily_nonprincipal K L) hs

theorem regularizedDedekindZeta_zero_sources {s : ℂ} (hs : 0 < s.re) :
    mixedRegularizedDedekindZeta L s = 0 ↔
      mixedRegularizedDedekindZeta K s = 0 ∨ Nonempty (PrimitiveArtinZeroWitness K L s) := by
  classical
  constructor
  · intro hz
    rw [source_regularized_factorization K L hs, mul_eq_zero] at hz
    rcases hz with hbase | hprod
    · exact Or.inl hbase
    · right
      unfold AbelianLocal.abelianArtinRelativeContinued at hprod
      obtain ⟨χ, hχ, hzχ⟩ := Finset.prod_eq_zero_iff.mp hprod
      have hn : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
      have hnp := sourceRayFamily_nonprincipal K L χ hn
      have hzero : (sourceRayFamily K L χ).nonprincipalContinued s = 0 := by
        by_contra hnz
        exact ((AbelianLocal.abelianArtinContinuedFactor_ne_zero_iff K L χ
          (sourceRayFamily K L χ) hs).mpr hnz) hzχ
      obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,h1,_hi1⟩ :=
        discriminantDegree_exists_primitive_boundary_nonzero (K := K) (L := L) χ hn
      have hagree' : ∀ I : primeToModulusIdeals
          (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
          Ψ.idealHom (I : FractionalIdealGroup K) =
            (sourceRayFamily K L χ).idealHom (I : FractionalIdealGroup K) := hagree
      exact ⟨⟨χ,hn,f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,h1,
        ((sourceRayFamily K L χ).nonprincipalContinued_zero_iff_primitive
          f hf hMf Ψ hprim hagree' hnp hs).mp hzero⟩⟩
  · intro hsource
    rcases hsource with hbase | hw
    · rw [source_regularized_factorization K L hs, hbase, zero_mul]
    · obtain ⟨w⟩ := hw
      have hn := sourceRayFamily_nonprincipal K L w.character w.nontrivial
      have hz : (sourceRayFamily K L w.character).nonprincipalContinued s = 0 :=
        ((sourceRayFamily K L w.character).nonprincipalContinued_zero_iff_primitive
          w.conductor w.conductor_ne_zero w.conductor_le w.primitiveCharacter w.primitive
          w.agrees hn hs).mpr w.zero
      have hfactor : AbelianLocal.abelianArtinContinuedFactor K L w.character
          (sourceRayFamily K L w.character) s = 0 := by
        rw [AbelianLocal.abelianArtinContinuedFactor, hz, mul_zero]
      have hprod : AbelianLocal.abelianArtinRelativeContinued K L (sourceRayFamily K L) s = 0 := by
        unfold AbelianLocal.abelianArtinRelativeContinued
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨w.nontrivial, Finset.mem_univ _⟩) hfactor
      rw [source_regularized_factorization K L hs, hprod, mul_zero]

theorem regularizedDedekindZeta_base_zero {s : ℂ} (hs : 0 < s.re)
    (hz : mixedRegularizedDedekindZeta K s = 0) : mixedRegularizedDedekindZeta L s = 0 := by
  rw [source_regularized_factorization K L hs, hz, zero_mul]

end ArtinRay
end
end ArtinMatthews.VaryingKummerAnalytic
