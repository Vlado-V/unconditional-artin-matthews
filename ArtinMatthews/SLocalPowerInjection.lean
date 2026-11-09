module

public import ArtinMatthews.SLocalUnitIsotropy
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SUnitKummerNormCore
public import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitLocalPowerKernel
public import ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual S-unit power quotient injects into the product of the
actual local power quotients. The finite set is constructed from a genuine
idelic support and the proved principalization. The local-power kernel
is discharged by the genuine Kummer norm-index theorem. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.GlobalClassFields GlobalClassFieldTheory.ClassFieldAxiom
open SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def hilbertPrincipalizingSet (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  principalizingSet (S₀ ∪ sUnitKummerNormSupport (K := K) n ∅)

theorem required_subset_hilbertPrincipalizingSet
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) :
    S₀ ⊆ hilbertPrincipalizingSet K S₀ n :=
  Finset.Subset.trans Finset.subset_union_left (required_subset_principalizingSet _)

theorem normSupport_subset_hilbertPrincipalizingSet
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) :
    sUnitKummerNormSupport (K := K) n ∅ ⊆ hilbertPrincipalizingSet K S₀ n :=
  Finset.Subset.trans Finset.subset_union_right (required_subset_principalizingSet _)

theorem hilbertPrincipalizingSet_isPrincipalIdealRing
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) :
    IsPrincipalIdealRing (IntegerRing (K := K) (hilbertPrincipalizingSet K S₀ n)) :=
  principalIntegerRing_isPrincipalIdealRing _

theorem sUnitKummerNormSupport_eq_self (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    sUnitKummerNormSupport (K := K) n S = S := by
  ext v
  constructor
  · intro hv
    change v ∈ (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪ _ at hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact hv
      · exact hS (Finset.mem_union_left _ (by simpa using hv))
    · exact hS (Finset.mem_union_right _ hv)
  · exact fun hv => subset_sUnitKummerNormSupport n S hv

abbrev SLocalPowerClasses (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ∀ v : S, ClassFieldTheory.PowerClassGroup ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) n

def sUnitPowerClassMap (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (SUnitGroup (K := K) S ⧸
      (powMonoidHom (n : ℕ) : SUnitGroup (K := K) S →* SUnitGroup (K := K) S).range) →*
    SLocalPowerClasses K n S := by
  refine QuotientGroup.lift (M := SLocalPowerClasses K n S)
    (powMonoidHom (n : ℕ) : SUnitGroup (K := K) S →* SUnitGroup (K := K) S).range
    (sUnitLocalPowerMap (K := K) n S S) ?_
  exact nthPowerSubgroup_le_sUnitLocalPowerKernel n S S

@[simp] theorem sUnitPowerClassMap_mk (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : SUnitGroup (K := K) S) :
    sUnitPowerClassMap K n S (QuotientGroup.mk' _ u) =
      sUnitLocalPowerMap (K := K) n S S u := rfl

variable [NumberField.IsTotallyComplex K]

theorem sUnitLocalPowerKernel_eq_powers (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    sUnitLocalPowerKernel (K := K) n S S =
      (powMonoidHom (n : ℕ) : SUnitGroup (K := K) S →* SUnitGroup (K := K) S).range := by
  apply le_antisymm
  · intro u hu
    have hprincipal : (u : Kˣ) ∈ principalIdelePowerLocalUnitSubgroup (K := K) n S ∅ := by
      change IdeleGroup.principalIdele K (u : Kˣ) ∈
        idelePowerLocalUnitSubgroup (K := K) n S ∅
      rw [mem_idelePowerLocalUnitSubgroup_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro w
        have hw : ¬ w.IsReal :=
          InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex w)
        rw [nthPowerSubgroup_eq_infinitePositiveSubgroup n w (Or.inr hw)]
        simp [RayClass.mem_infinitePositiveSubgroup_iff, hw]
      · intro v hv
        exact (mem_sUnitLocalPowerKernel_iff n S S u).mp hu ⟨v, hv⟩
      · intro v hv
        rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
          IdeleGroup.finiteComponent_principalIdele,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact u.property v (by simpa using hv)
    have he := principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowers_on_kummerNormSupport
      (K := K) n hmu S
    dsimp only at he
    rw [sUnitKummerNormSupport_eq_self K n S hS] at he
    rw [he] at hprincipal
    obtain ⟨v, hv, hvu⟩ := hprincipal
    have hvu' : v = u := Subtype.ext hvu
    exact hvu' ▸ hv
  · exact nthPowerSubgroup_le_sUnitLocalPowerKernel n S S

theorem sUnitPowerClassMap_injective (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    Function.Injective (sUnitPowerClassMap K n S) := by
  apply (sUnitPowerClassMap K n S).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ q
  change QuotientGroup.mk' _ u = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [← sUnitLocalPowerKernel_eq_powers K n hmu S hS]
  change sUnitLocalPowerMap (K := K) n S S u = 1
  change sUnitPowerClassMap K n S (QuotientGroup.mk' _ u) = 1 at hq
  rw [sUnitPowerClassMap_mk] at hq
  change sUnitLocalPowerMap (K := K) n S S u = 1 at hq
  exact hq

theorem hilbertPrincipalizingSet_powerClassMap_injective
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Function.Injective (sUnitPowerClassMap K n (hilbertPrincipalizingSet K S₀ n)) :=
  sUnitPowerClassMap_injective K n hmu _ (normSupport_subset_hilbertPrincipalizingSet K S₀ n)

end
end ArtinMatthews
