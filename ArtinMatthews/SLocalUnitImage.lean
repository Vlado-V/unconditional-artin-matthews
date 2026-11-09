module

public import ArtinMatthews.SLocalPowerInjection


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cardinality of the actual local power-class space and of the
actual diagonal S-unit image. The local cardinality is the genuine local
power-index/product-formula calculation, not a dimension hypothesis. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.GlobalClassFields GlobalClassFieldTheory.ClassFieldAxiom
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sUnitPowerImage (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SLocalPowerClasses K n S) := (sUnitPowerClassMap K n S).range

variable [NumberField.IsTotallyComplex K]

def sUnitPowerImageEquiv (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    (SUnitGroup (K := K) S ⧸
      (powMonoidHom (n : ℕ) : SUnitGroup (K := K) S →* SUnitGroup (K := K) S).range) ≃*
      sUnitPowerImage K n S :=
  MonoidHom.ofInjective (sUnitPowerClassMap_injective K n hmu S hS)

theorem sUnitPowerImage_card (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    Nat.card (sUnitPowerImage K n S) = (n : ℕ) ^ totalPlaceCard (K := K) S := by
  rw [Nat.card_congr (sUnitPowerImageEquiv K n hmu S hS).symm.toEquiv]
  exact card_sUnit_nthPowerQuotient S n hmu

theorem sLocalPowerClasses_card (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal ∣ Ideal.span {((n : ℕ) : 𝓞 K)} → v ∈ S) :
    Nat.card (SLocalPowerClasses K n S) = (n : ℕ) ^ (2 * totalPlaceCard (K := K) S) := by
  have harch : Nat.card (∀ w : InfinitePlace K,
      w.Completionˣ ⧸ (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range) = 1 := by
    rw [Nat.card_pi]
    apply Finset.prod_eq_one
    intro w _
    rw [card_infinitePlace_nthPowerQuotient]
    have hw : ¬ w.IsReal :=
      InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex w)
    simp [hw]
  have h := card_supportedIdeleQuotient_eq_power_two_totalPlaceCard
    (K := K) n hmu S ∅ hS
  rw [card_supportedIdeleQuotient_eq_localPowerClasses, Nat.card_prod, harch, one_mul] at h
  exact h

theorem sLocalPowerClasses_card_eq_unitImage_sq (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    Nat.card (SLocalPowerClasses K n S) = (Nat.card (sUnitPowerImage K n S)) ^ 2 := by
  rw [sUnitPowerImage_card K n hmu S hS,
    sLocalPowerClasses_card K n hmu S (fun v hv =>
      hS (mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast n ∅ hv))]
  rw [← pow_mul]
  congr 1
  omega

theorem hilbertPrincipalizingSet_local_card_eq_unitImage_sq
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card (SLocalPowerClasses K n (hilbertPrincipalizingSet K S₀ n)) =
      (Nat.card (sUnitPowerImage K n (hilbertPrincipalizingSet K S₀ n))) ^ 2 :=
  sLocalPowerClasses_card_eq_unitImage_sq K n hmu _
    (normSupport_subset_hilbertPrincipalizingSet K S₀ n)

end
end ArtinMatthews
