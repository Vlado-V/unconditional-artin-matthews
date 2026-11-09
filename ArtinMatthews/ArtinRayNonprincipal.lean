module

public import ArtinMatthews.ArtinRayPrincipalKernel
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedAlgebra


set_option backward.privateInPublic true
@[expose] public section

/-! Nontrivial actual Galois characters yield nonprincipal ray characters.
This uses surjectivity of the genuine arithmetic Artin map and prime
ideal generation; no prime-distribution theorem is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
noncomputable section
open scoped NumberField Classical
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
  GlobalClassFieldTheory.IdealClassFieldTheory
open GaloisIdealCharacter

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

theorem exists_prime_frobenius_value_ne_one
    (m : RayClass.Modulus K)
    (hm : m.congruenceSubgroup ≤ (ideleClassNorm K L).range)
    (hunram : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v ∉ m.finitePart.support →
      Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val)
    (χ : (L ≃ₐ[K] L) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v ∉ m.finitePart.support ∧ χ (primeFrobenius K L v) ≠ 1 := by
  by_contra hn
  have hall (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m.finitePart.support) : χ (primeFrobenius K L v) = 1 := by
    by_contra h
    exact hn ⟨v,hv,h⟩
  have hhom : (idealHom K L χ).comp (RayClass.primeToModulusIdeals m).subtype = 1 := by
    apply RayClass.primeToModulusIdeals_hom_ext m
    intro v hv
    change idealHom K L χ (integralIdealFractionalUnit v.asIdeal v.ne_bot) = 1
    rw [idealHom_prime]
    exact hall v hv
  rw [idealCharacter_eq_artin_comp m hm hunram χ] at hhom
  apply hχ
  ext g
  obtain ⟨I,rfl⟩ := arithmeticIdealArtinGaloisMap_surjective (K := K) (L := L) m hm g
  exact congrArg Units.val (DFunLike.congr_fun hhom I)

theorem frobenius_ray_isNonprincipal_of_totallyComplex
    [NumberField.IsTotallyComplex K] (N : ℕ) (hN : 0 < N)
    (χ : (L ≃ₐ[K] L) →* ℂˣ) (hχ : χ ≠ 1)
    (ψ : EvenRayCharacter K N) (he : ψ.idealHom = idealHom K L χ) :
    ψ.IsNonprincipal := by
  obtain ⟨m,_,hnorm,hur⟩ := exists_even_unramified_artin_modulus (K := K) (L := L)
  have hNZ : (N : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let I := integralIdealFractionalUnit (Ideal.span {(N : 𝓞 K)})
    (by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using hNZ)
  let b : RayClass.FiniteModulus K :=
    (FractionalIdealGroup.countVector I).mapRange Int.natAbs rfl
  let m' := m.replaceFinitePart (m.finitePart+b)
  have hle : m ≤ m' := by
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · exact Finset.Subset.refl _
  have hnorm' : m'.congruenceSubgroup ≤ (ideleClassNorm K L).range :=
    (RayClass.Modulus.congruenceSubgroup_antitone hle).trans hnorm
  have hzero (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m'.finitePart.support) : m.finitePart v = 0 ∧ b v = 0 := by
    have h := Finsupp.notMem_support_iff.mp hv
    change m.finitePart v+b v = 0 at h
    omega
  obtain ⟨v,hv,hvalue⟩ := exists_prime_frobenius_value_ne_one m' hnorm'
    (fun v hv => hur v (Finsupp.notMem_support_iff.mpr (hzero v hv).1)) χ hχ
  have hcount : FractionalIdeal.count K v (Ideal.span {(N : 𝓞 K)}) = 0 :=
    Int.natAbs_eq_zero.mp (hzero v hv).2
  have hnot : (N : 𝓞 K) ∉ v.asIdeal := by
    exact mt ((principal_count_ne_zero_iff_mem K (N : 𝓞 K) hNZ v).mpr)
      (by simpa using hcount)
  have hcop : IsCoprime v.asIdeal (rationalModulusIdeal (𝓞 K) N) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    exact (Ideal.isMaximal_iff.mp inferInstance).2 _ (N : 𝓞 K)
      le_sup_left hnot (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  refine ⟨v.asIdeal,v.ne_bot,hcop,?_⟩
  rw [he,idealHom_prime]
  exact hvalue

theorem exists_nonprincipal_frobenius_ray_family_of_totallyComplex
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [NumberField.IsTotallyComplex K] :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr L).natAbs ∣ N ∧
      ∃ ψ : ((L ≃ₐ[K] L) →* ℂˣ) → EvenRayCharacter K N,
        (∀ χ, (ψ χ).idealHom = idealHom K L χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  obtain ⟨N,hN,hdN,ψ,he⟩ := exists_frobenius_ray_family_of_totallyComplex K L
  exact ⟨N,hN,hdN,ψ,he,fun χ hχ =>
    frobenius_ray_isNonprincipal_of_totallyComplex N hN χ hχ (ψ χ) (he χ)⟩

/-- The common ray family for the actual auxiliary cyclotomic Kummer tower,
including nonprincipality for every nontrivial Galois character. -/
theorem twelfthKummer_nonprincipal_frobenius_ray_family
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr (twelfthKummerField q a)).natAbs ∣ N ∧
      ∃ ψ : (Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ) →
          EvenRayCharacter (twelfthCyclotomicField q) N,
        (∀ χ, (ψ χ).idealHom =
          idealHom (twelfthCyclotomicField q) (twelfthKummerField q a) χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal :=
  exists_nonprincipal_frobenius_ray_family_of_totallyComplex
    (twelfthCyclotomicField q) (twelfthKummerField q a)

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
