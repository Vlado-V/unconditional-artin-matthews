module

public import ArtinMatthews.SixthKummerSharpRay
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import ArtinMatthews.ArtinFrobeniusConductorSupport
public import ArtinMatthews.IdealRayCharacterProduct
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

/-! The genuine finite-order Kummer component of the global Gauss
correction. For an S-unit the sharp modulus is the fixed S modulus.
In particular the factor conjugate(chi_bullet(4)) exists globally; the
quadratic Weil-index factor is a separate construction. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem sunit_sixthKummerSharpIdeal (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : exteriorUnitSubgroup S) : sixthKummerSharpIdeal S (u : Kˣ) = sixthKummerFixedIdeal S := by
  have h : sixthExteriorRadicalPrimes S (u : Kˣ) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpS,hpval⟩ := (mem_sixthExteriorRadicalPrimes S (u : Kˣ) p).mp hp
    exact hpval (u.property p hpS)
  rw [sixthKummerSharpIdeal,sixthExteriorRadicalIdeal,h,Finset.prod_empty,mul_one]

def fourFieldUnit : Kˣ := Units.mk0 4 (by norm_num)

theorem fourFieldUnit_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : sixthWildPrimes K ⊆ S) :
    fourFieldUnit (K := K) ∈ exteriorUnitSubgroup S := by
  intro p hp
  have he : (toPrincipalIdeal (𝓞 K) K (fourFieldUnit (K := K)) : FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.span {(4 : 𝓞 K)} : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [coe_toPrincipalIdeal,FractionalIdeal.coeIdeal_span_singleton]
    rfl
  change FractionalIdeal.count K p _ = 0
  rw [he]
  by_contra h
  have h4 : (4 : 𝓞 K) ∈ p.asIdeal := (principal_count_ne_zero_iff_mem K 4 (by norm_num) p).mp h
  have h22 : (2 : 𝓞 K)*2 ∈ p.asIdeal := by norm_num at h4 ⊢; exact h4
  have h2 : (2 : 𝓞 K) ∈ p.asIdeal :=
    ((show p.asIdeal.IsPrime from inferInstance).mem_or_mem h22).elim id id
  have h6 : (6 : 𝓞 K) ∈ p.asIdeal := by
    have hm := p.asIdeal.mul_mem_right (3 : 𝓞 K) h2
    norm_num at hm ⊢
    exact hm
  exact hp (hS ((mem_sixthWildPrimes p).mpr h6))

variable [Algebra K ℂ]

omit [NumberField K] in
theorem sixthKummerRowCharacter_pow_six {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset K) (a : K) (ha : a ∈ A) (ha0 : a ≠ 0)
    (σ : Gal(sixthKummerRowField A/K)) : (sixthKummerRowCharacter hζ A a ha ha0 σ)^6 = 1 := by
  unfold sixthKummerRowCharacter
  rw [MonoidHom.comp_apply,← map_pow]
  have h : (radicalAutCharacter hζ (sixthKummerRowRoot_pow A a ha)
      (sixthKummerRowRoot_ne_zero A a ha ha0) σ)^6 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 6 _).mp (radicalAutCharacter hζ (sixthKummerRowRoot_pow A a ha)
      (sixthKummerRowRoot_ne_zero A a ha ha0) σ).property
  rw [h,map_one]

theorem sixthKummerRowIdealHom_pow_six {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset K) (a : K) (ha : a ∈ A) (ha0 : a ≠ 0) (I : FractionalIdealGroup K) :
    (GaloisIdealCharacter.idealHom K (sixthKummerRowField A)
      (sixthKummerRowCharacter hζ A a ha ha0) I)^6 = 1 := by
  change (∏ᶠ p : HeightOneSpectrum (𝓞 K),
    (sixthKummerRowCharacter hζ A a ha ha0)
      (GaloisIdealCharacter.primeFrobenius K (sixthKummerRowField A) p) ^
        FractionalIdeal.count K p I.val)^6 = 1
  rw [finprod_pow
    (GaloisIdealCharacter.finite_factor_support K (sixthKummerRowField A) _ I)]
  have h (p : HeightOneSpectrum (𝓞 K)) :
      ((sixthKummerRowCharacter hζ A a ha ha0)
        (GaloisIdealCharacter.primeFrobenius K (sixthKummerRowField A) p) ^
          FractionalIdeal.count K p I.val)^6 = 1 := by
    rw [← zpow_natCast,← zpow_mul,mul_comm,zpow_mul,zpow_natCast,
      sixthKummerRowCharacter_pow_six,one_zpow]
  simp only [h,finprod_one]

variable [NumberField.IsTotallyComplex K]

def sunitKummerInverseCorrection {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : sixthWildPrimes K ⊆ S)
    (u : exteriorUnitSubgroup S) : EvenIdealRayCharacter K (sixthKummerFixedIdeal S) := by
  let ψ := (sixthKummerSharpRayCharacter hζ S hS (u : Kˣ)).inverse
  exact PrincipalIdealRay.realize ψ.idealHom (sixthKummerFixedIdeal S) (sixthKummerFixedIdeal_ne_zero S)
    (by rw [← sunit_sixthKummerSharpIdeal S u]; exact ψ.principalKernel) ψ.finiteOrder

theorem sunitKummerInverseCorrection_idealHom {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : sixthWildPrimes K ⊆ S)
    (u : exteriorUnitSubgroup S) (I : FractionalIdealGroup K) :
    (sunitKummerInverseCorrection hζ S hS u).idealHom I =
      ((sixthKummerSharpRayCharacter hζ S hS (u : Kˣ)).idealHom I)⁻¹ := rfl

theorem sunitKummerInverseCorrection_pow_six {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : sixthWildPrimes K ⊆ S)
    (u : exteriorUnitSubgroup S) (I : FractionalIdealGroup K) :
    ((sunitKummerInverseCorrection hζ S hS u).idealHom I)^6 = 1 := by
  rw [sunitKummerInverseCorrection_idealHom,inv_pow,sixthKummerSharpRayCharacter_idealHom,
    sixthKummerRowIdealHom_pow_six,inv_one]

def fourKummerInverseCorrection {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : sixthWildPrimes K ⊆ S) :
    EvenIdealRayCharacter K (sixthKummerFixedIdeal S) :=
  sunitKummerInverseCorrection hζ S hS ⟨fourFieldUnit,fourFieldUnit_mem S hS⟩

theorem fourKummerInverseCorrection_prime {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : sixthWildPrimes K ⊆ S)
    (p : HeightOneSpectrum (𝓞 K)) :
    (fourKummerInverseCorrection hζ S hS).idealHom (integralIdealFractionalUnit p.asIdeal p.ne_bot) =
      (sixthKummerRowCharacter hζ {4} 4 (Finset.mem_singleton_self _) (by norm_num)
        (GaloisIdealCharacter.primeFrobenius K (sixthKummerRowField {4}) p))⁻¹ := by
  rw [fourKummerInverseCorrection,sunitKummerInverseCorrection_idealHom,
    sixthKummerSharpRayCharacter_idealHom,GaloisIdealCharacter.idealHom_prime]
  rfl

end
end ArtinMatthews
