module

public import ArtinMatthews.SixthExteriorReduction
public import ArtinMatthews.SixthExteriorPowerClassesQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! Actual reduced representatives of every global sixth-power class.
The sixth quotient fractional ideal is constructed from the integer prime
exponents. The finite class-support set supplies its exterior generator. -/
namespace ArtinMatthews
open IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def exteriorPrincipalExponentVector (u : Kˣ) : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun p => exteriorPrincipalValuation p u)
    (by
      simpa only [Function.support,exteriorPrincipalValuation] using
        (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors
          (toPrincipalIdeal (𝓞 K) K u : FractionalIdeal (𝓞 K)⁰ K))))

@[simp] theorem exteriorPrincipalExponentVector_apply (u : Kˣ)
    (p : HeightOneSpectrum (𝓞 K)) :
    exteriorPrincipalExponentVector u p=exteriorPrincipalValuation p u := rfl

def exteriorSixthQuotientExponents (u : Kˣ) : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  (exteriorPrincipalExponentVector u).mapRange (fun n : ℤ => n/6) (by decide)

@[simp] theorem exteriorSixthQuotientExponents_apply (u : Kˣ)
    (p : HeightOneSpectrum (𝓞 K)) :
    exteriorSixthQuotientExponents u p=exteriorPrincipalValuation p u/6 := rfl

def exteriorSixthQuotientIdeal (u : Kˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 ((exteriorSixthQuotientExponents u).prod
    (fun p n => (p.asIdeal : FractionalIdeal (𝓞 K)⁰ K)^n))
    (Finsupp.prod_ne_zero_iff.mpr fun p _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot))

theorem exteriorSixthQuotientIdeal_count (u : Kˣ) (p : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K p (exteriorSixthQuotientIdeal u : FractionalIdeal (𝓞 K)⁰ K)=
      exteriorPrincipalValuation p u/6 := by
  change FractionalIdeal.count K p ((exteriorSixthQuotientExponents u).prod
    (fun q n => (q.asIdeal : FractionalIdeal (𝓞 K)⁰ K)^n))=_
  rw [FractionalIdeal.count_finsuppProd,exteriorSixthQuotientExponents_apply]

/-- Every field unit has a reduced representative in its sixth-power
class, with no assumed principal generator or power-class injection. -/
theorem exists_exterior_sixth_reduced_representative (u : Kˣ) :
    ∃ v t : Kˣ, ExteriorSixthReduced (exteriorPrincipalizingPrimes K) v ∧ u=v*t^6 := by
  obtain ⟨t,ht⟩ := exists_principal_generator_outside_class_support
    (exteriorSixthQuotientIdeal u)
  refine ⟨u/t^6,t,?_,by simp⟩
  intro p hp
  rw [exteriorPrincipalValuation_div,exteriorPrincipalValuation_pow,ht p hp,
    exteriorSixthQuotientIdeal_count]
  omega

theorem exteriorSixthReduced_mono {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) {u : Kˣ} (hu : ExteriorSixthReduced S u) : ExteriorSixthReduced T u :=
  fun p hp => hu p (fun h => hp (hST h))

theorem exists_exterior_sixth_reduced_representative_enlargement
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) :
    ∃ v t : Kˣ, ExteriorSixthReduced (exteriorPrincipalizingPrimes K ∪ S) v ∧ u=v*t^6 := by
  obtain ⟨v,t,hv,he⟩ := exists_exterior_sixth_reduced_representative u
  exact ⟨v,t,exteriorSixthReduced_mono Finset.subset_union_left hv,he⟩

theorem exteriorReducedPowerClassMap_surjective :
    Function.Surjective (exteriorReducedPowerClassMap (exteriorPrincipalizingPrimes K)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro u
  obtain ⟨v,t,hv,he⟩ := exists_exterior_sixth_reduced_representative u
  refine ⟨Quotient.mk (exteriorReducedPowerSetoid (exteriorPrincipalizingPrimes K)) ⟨v,hv⟩,?_⟩
  change QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) v=
    QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) u
  have ht : QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) (t^6)=1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨t,rfl⟩
  rw [he,map_mul,ht]
  exact (_root_.mul_one
    (QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) v)).symm

def exteriorReducedPowerClassEquiv :
    ExteriorSixthReducedClasses (exteriorPrincipalizingPrimes K) ≃
      Kˣ ⧸ globalSixthPowerSubgroup :=
  Equiv.ofBijective (exteriorReducedPowerClassMap (exteriorPrincipalizingPrimes K))
    ⟨exteriorReducedPowerClassMap_injective _,exteriorReducedPowerClassMap_surjective⟩

end
end ArtinMatthews
