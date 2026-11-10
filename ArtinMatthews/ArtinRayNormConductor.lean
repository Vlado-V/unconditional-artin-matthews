module

public import ArtinMatthews.ArtinRayIdealLocalNorm
public import ArtinMatthews.SourceFullIdealFactorization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
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

/-! Realize the actual minimal abelian norm conductor as an ordinary
integral ideal, and its Artin character as an even ideal ray character. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open SourceEulerAssembly
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem integralIdealFiniteModulus_sourceFullExponentIdeal (e : RayClass.FiniteModulus K) :
    integralIdealFiniteModulus (sourceFullExponentIdeal K e) (sourceFullExponentIdeal_ne_bot K e) =
      e := by
  ext v
  rw [integralIdealFiniteModulus_apply,
    ← v.factorization_eq_multiplicity (sourceFullExponentIdeal_ne_bot K e),
    sourceFullExponentIdeal_factorization]
  exact Finsupp.embDomain_apply_self (sourceFullPrimeEmbedding K) e v

theorem integralIdeal_le_of_finiteModulus_le {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : integralIdealFiniteModulus I hI ≤ integralIdealFiniteModulus J hJ) : J ≤ I := by
  intro x hx
  apply (integralIdeal_mem_iff_modulus_prime_powers I hI x).mpr
  intro v hv
  have hv' := Finsupp.support_mono h hv
  exact Ideal.pow_le_pow_right (h v)
    ((integralIdeal_mem_iff_modulus_prime_powers J hJ x).mp hx v hv')

variable (K) (L : Type) [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsAbelianGalois K L]

def abelianNormConductorIdeal : Ideal (𝓞 K) :=
  sourceFullExponentIdeal K (ideleClassNormNarrowFiniteConductor (K := K) (L := L))

theorem abelianNormConductorIdeal_ne_bot : abelianNormConductorIdeal K L ≠ ⊥ :=
  sourceFullExponentIdeal_ne_bot K _

theorem abelianNormConductorIdeal_modulus :
    integralIdealFiniteModulus (abelianNormConductorIdeal K L) (abelianNormConductorIdeal_ne_bot K L) =
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) :=
  integralIdealFiniteModulus_sourceFullExponentIdeal _

theorem abelianNormConductorIdeal_support :
    (integralIdealFiniteModulus (abelianNormConductorIdeal K L)
      (abelianNormConductorIdeal_ne_bot K L)).support = ramifiedBaseFinitePlaces (K := K) (L := L) := by
  rw [abelianNormConductorIdeal_modulus,
    ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces]

theorem abelianNormConductorIdeal_localNorm (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v (integralIdealFiniteModulus (abelianNormConductorIdeal K L)
      (abelianNormConductorIdeal_ne_bot K L) v) ≤
      chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v := by
  rw [abelianNormConductorIdeal_modulus,
    ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus]
  exact ideleClassNormDefiningModulus_local_spec v

theorem abelianNormConductorIdeal_unramified (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (integralIdealFiniteModulus (abelianNormConductorIdeal K L)
      (abelianNormConductorIdeal_ne_bot K L)).support) :
    Algebra.IsUnramifiedAt (𝓞 K) (GaloisIdealCharacter.primeAbove K L v).val := by
  rw [abelianNormConductorIdeal_support, mem_ramifiedBaseFinitePlaces_iff] at hv
  let Q := GaloisIdealCharacter.primeAbove K L v
  by_contra hQ
  exact hv ⟨⟨Q.val, Q.property.1, GaloisIdealCharacter.primeAbove_ne_bot K L v⟩, ⟨Q.property.2.over⟩, hQ⟩

variable [NumberField.IsTotallyComplex K]

def abelianNormConductorRayCharacter (χ : Gal(L/K) →* ℂˣ) :
    EvenIdealRayCharacter K (abelianNormConductorIdeal K L) :=
  idealRayCharacter_of_localNorm _ (abelianNormConductorIdeal_ne_bot K L)
    (abelianNormConductorIdeal_localNorm K L) (abelianNormConductorIdeal_unramified K L) χ

theorem abelianNormConductorRayCharacter_idealHom (χ : Gal(L/K) →* ℂˣ) :
    (abelianNormConductorRayCharacter K L χ).idealHom = GaloisIdealCharacter.idealHom K L χ := rfl

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
