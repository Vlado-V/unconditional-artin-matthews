module

public import ArtinMatthews.ArtinRayNonprincipal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealModulus


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine Artin surjectivity separates two distinct finite abelian
characters at a prime avoiding any prescribed nonzero ideal. No prime
distribution or Chebotarev assertion is used. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open GaloisIdealCharacter
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

theorem exists_prime_separating_frobenius_avoiding
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (χ θ : Gal(L/K) →* ℂˣ) (hne : χ ≠ θ) :
    ∃ v : HeightOneSpectrum (𝓞 K), IsCoprime v.asIdeal M ∧
      χ (primeFrobenius K L v) ≠ θ (primeFrobenius K L v) := by
  obtain ⟨m,_,hnorm,hur⟩ := exists_unramified_artin_modulus_with_signs K L
  let m' := m.replaceFinitePart (m.finitePart + integralIdealFiniteModulus M hM)
  have hle : m ≤ m' := by
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · exact Finset.Subset.refl _
  have hnorm' : m'.congruenceSubgroup ≤ (ideleClassNorm K L).range :=
    (RayClass.Modulus.congruenceSubgroup_antitone hle).trans hnorm
  have hzero (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ m'.finitePart.support) :
      m.finitePart v=0 ∧ integralIdealFiniteModulus M hM v=0 := by
    have h := Finsupp.notMem_support_iff.mp hv
    change m.finitePart v + integralIdealFiniteModulus M hM v=0 at h
    omega
  have hdiv : χ/θ ≠ 1 := fun h => hne (div_eq_one.mp h)
  obtain ⟨v,hv,hvalue⟩ := exists_prime_frobenius_value_ne_one m' hnorm'
    (fun v hv => hur v (Finsupp.notMem_support_iff.mpr (hzero v hv).1)) (χ/θ) hdiv
  have hnd : ¬v.asIdeal ∣ M := by
    intro hd
    have hm := (integralIdealFiniteModulus_mem_support M hM v).mpr hd
    exact (Finsupp.mem_support_iff.mp hm) (hzero v hv).2
  have hnle : ¬M ≤ v.asIdeal := fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨a,ha,han⟩ := Set.not_subset.mp hnle
  have hcop : IsCoprime v.asIdeal M := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    exact (Ideal.isMaximal_iff.mp inferInstance).2 _ a le_sup_left han (Submodule.mem_sup_right ha)
  refine ⟨v,hcop,?_⟩
  intro heq
  apply hvalue
  change χ (primeFrobenius K L v)/θ (primeFrobenius K L v)=1
  rw [heq]
  simp

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
