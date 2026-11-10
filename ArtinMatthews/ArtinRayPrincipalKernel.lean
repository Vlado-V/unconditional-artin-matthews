module

public import ArtinMatthews.ArtinRayResidueRealization
public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.KummerCyclotomicTower
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import ArtinMatthews.ArtinRayConductor
public import ArtinMatthews.ArtinRayKernelComparison
public import ArtinMatthews.ArtinRayLocalCongruence
public import ArtinMatthews.KummerCyclotomicTowerComplex
public import ArtinMatthews.KummerCyclotomicTowerCyclic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.ENatToNat
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

/-! The actual Frobenius ideal characters of a finite abelian extension
of a totally complex number field have a common finite ray modulus.
The principal kernel is supplied by the proved arithmetic Artin map. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
noncomputable section
open scoped NumberField Classical
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open GaloisIdealCharacter
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The global principal-ray kernel for actual Frobenius characters,
with real-place positivity retained for an arbitrary base number field. -/
theorem exists_frobenius_principal_ray_modulus
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ m : RayClass.Modulus K, m.infinitePart = Finset.univ ∧
      ∀ (χ : (L ≃ₐ[K] L) →* ℂˣ) (I : RayClass.primeToModulusIdeals m),
        I ∈ RayClass.principalRayIdealSubgroup m → idealHom K L χ I = 1 := by
  obtain ⟨m,hInfinite,hnorm,hur⟩ := exists_unramified_artin_modulus_with_signs K L
  exact ⟨m,hInfinite,fun χ I hI => idealCharacter_principalRay_eq_one m hnorm hur χ I hI⟩

theorem idealCharacter_kernelLaw_of_even_modulus
    (m : RayClass.Modulus K) (hm : m.infinitePart = ∅)
    (hnorm : m.congruenceSubgroup ≤ (ideleClassNorm K L).range)
    (hunram : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v ∉ m.finitePart.support →
      Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val)
    (N : ℕ)
    (hN : ∀ v ∈ m.finitePart.support,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m.finitePart v)
    (χ : (L ≃ₐ[K] L) →* ℂˣ) : PrincipalRay.KernelLaw (idealHom K L χ) N := by
  intro a ha hcong
  let x : Kˣ := Units.mk0 (a : K) (by exact_mod_cast ha)
  have hx : IdeleGroup.principalIdele K x ∈ RayClass.idelePrimeToModulusSubgroup m :=
    principalIdele_mem_even_ray_of_congruence m hm N hN a ha hcong
  let y : RayClass.idelePrimeToModulusSubgroup m := ⟨IdeleGroup.principalIdele K x, hx⟩
  let I := RayClass.primeToIdealMap m y
  have hI : I ∈ RayClass.principalRayIdealSubgroup m := by
    refine ⟨y, ?_, rfl⟩
    exact ⟨x, rfl⟩
  have H := idealCharacter_principalRay_eq_one m hnorm hunram χ I hI
  have hval : (I : FractionalIdealGroup K) = integralIdealFractionalUnit
      (Ideal.span {a}) (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha) := by
    change IdeleGroup.fractionalIdeal (IdeleGroup.principalIdele K x) = _
    rw [IdeleGroup.fractionalIdeal_principalIdele]
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact (FractionalIdeal.coeIdeal_span_singleton a).symm
  change idealHom K L χ (I : FractionalIdealGroup K) = 1 at H
  change idealHom K L χ (integralIdealFractionalUnit (Ideal.span {a}) _) = 1
  rwa [hval] at H


/-- No ray-kernel condition is assumed: the common finite modulus and its
kernel law are constructed from actual arithmetic reciprocity. -/
theorem exists_frobenius_principal_kernel_of_totallyComplex
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [NumberField.IsTotallyComplex K] :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr L).natAbs ∣ N ∧
      ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, PrincipalRay.KernelLaw (idealHom K L χ) N := by
  obtain ⟨m,N,hN,hdN,hm,hnorm,hlocal,hur⟩ :=
    exists_integer_even_artin_modulus (K := K) (L := L)
  exact ⟨N,hN,hdN,idealCharacter_kernelLaw_of_even_modulus m hm hnorm hur N hlocal⟩

theorem exists_frobenius_ray_family_of_totallyComplex
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [NumberField.IsTotallyComplex K] :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr L).natAbs ∣ N ∧
      ∃ ψ : ((L ≃ₐ[K] L) →* ℂˣ) → EvenRayCharacter K N,
        ∀ χ, (ψ χ).idealHom = idealHom K L χ := by
  obtain ⟨N,hN,hdN,hkernel⟩ := exists_frobenius_principal_kernel_of_totallyComplex K L
  refine ⟨N,hN,hdN,fun χ => PrincipalRay.realize (idealHom K L χ) N hN
    (hkernel χ) (idealHom_finiteOrder K L χ),?_⟩
  intro χ
  rfl

/-- The preserved actual auxiliary cyclotomic tower specializes the genuine
finite-ray realization without any assumption on its principal subgroup. -/
theorem twelfthKummer_frobenius_ray_family (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr (twelfthKummerField q a)).natAbs ∣ N ∧
      ∃ ψ : (Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ) →
          EvenRayCharacter (twelfthCyclotomicField q) N,
        ∀ χ, (ψ χ).idealHom = idealHom (twelfthCyclotomicField q) (twelfthKummerField q a) χ :=
  exists_frobenius_ray_family_of_totallyComplex (twelfthCyclotomicField q) (twelfthKummerField q a)

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
