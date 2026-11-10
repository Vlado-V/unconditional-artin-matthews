module

public import ArtinMatthews.KummerTowerDiscriminantModulus
public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.ArtinRayResidueRealization
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedAlgebra
public import ArtinMatthews.ArtinRayDiscriminantSupport
public import ArtinMatthews.ArtinRayKernelComparison
public import ArtinMatthews.ArtinRayNonprincipal
public import ArtinMatthews.ArtinRayNormCorrection
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
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

/-! Actual Frobenius characters at the explicit rational modulus
`|discr L| * [L:K]^2`, using Hensel power corrections and arithmetic reciprocity. -/
noncomputable section
open scoped NumberField Classical
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
  GlobalClassFieldTheory.IdealClassFieldTheory
open GaloisIdealCharacter
attribute [local instance] ideleClassSubgroupNormal idealArtinKernelNormal
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]

theorem frobenius_principal_kernel_discriminantDegreeModulus
    (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    PrincipalRay.KernelLaw (idealHom K L χ) (discriminantDegreeModulus K L) := by
  intro a ha hc
  obtain ⟨m,hm,hnorm,hD,hur⟩ :=
    exists_discriminant_supported_artin_modulus (K := K) (L := L)
  obtain ⟨y,hy,hyNorm⟩ := exists_principal_norm_class_representative (L := L)
    m hm (NumberField.discr L).natAbs hD a ha hc
  let I := RayClass.primeToIdealMap m y
  have hk : I ∈ idealArtinKernel m (ideleClassNorm K L).range hnorm := by
    change idealArtinMap m (ideleClassNorm K L).range hnorm I = 1
    rw [GlobalClassFields.idealArtinMap_primeToIdealMap]
    exact (QuotientGroup.eq_one_iff _).mpr hyNorm
  have hArtin : arithmeticIdealArtinGaloisMap (K := K) (L := L) m hnorm I = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [arithmeticIdealArtinGaloisMap_ker]
    exact hk
  have h := DFunLike.congr_fun (idealCharacter_eq_artin_comp m hnorm hur χ) I
  change idealHom K L χ (I : FractionalIdealGroup K) =
    χ (arithmeticIdealArtinGaloisMap m hnorm I) at h
  rw [hArtin,map_one] at h
  change idealHom K L χ (integralIdealFractionalUnit (Ideal.span {a}) _) = 1
  rwa [hy] at h

/-- The ray character is constructed at the explicit small modulus; its
principal law is proved by actual arithmetic reciprocity. -/
def discriminantDegreeRayCharacter (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    EvenRayCharacter K (discriminantDegreeModulus K L) :=
  PrincipalRay.realize (idealHom K L χ) (discriminantDegreeModulus K L)
    (discriminantDegreeModulus_pos K L)
    (frobenius_principal_kernel_discriminantDegreeModulus χ)
    (idealHom_finiteOrder K L χ)

@[simp] theorem discriminantDegreeRayCharacter_idealHom
    (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    (discriminantDegreeRayCharacter χ).idealHom = idealHom K L χ := rfl

theorem discriminantDegreeRayCharacter_isNonprincipal
    (χ : (L ≃ₐ[K] L) →* ℂˣ) (hχ : χ ≠ 1) :
    (discriminantDegreeRayCharacter χ).IsNonprincipal :=
  frobenius_ray_isNonprincipal_of_totallyComplex _
    (discriminantDegreeModulus_pos K L) χ hχ (discriminantDegreeRayCharacter χ) rfl

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
