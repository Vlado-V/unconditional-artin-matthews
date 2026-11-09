module

public import ArtinMatthews.SIntegerAwayLocalization
public import ArtinMatthews.LocalizationClassGroupSurjective
public import ArtinMatthews.SixthExteriorReduction


set_option backward.privateInPublic true
@[expose] public section

/-! Construct the finite S enlargement from the actual finite ideal
class group. A nonzero element in each integral representative becomes
a unit after localization, so every localized ideal is principal. -/

namespace ArtinMatthews.SIntegerPrincipalization

open NumberField IsDedekindDomain Set
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def classSupportWitness (c : ClassGroup (𝓞 K)) : 𝓞 K :=
  ((Submodule.ne_bot_iff _).mp (mem_nonZeroDivisors_iff_ne_zero.mp
    (exteriorClassRepresentative c).property)).choose

theorem classSupportWitness_mem (c : ClassGroup (𝓞 K)) :
    classSupportWitness c ∈ (exteriorClassRepresentative c).val :=
  ((Submodule.ne_bot_iff _).mp (mem_nonZeroDivisors_iff_ne_zero.mp
    (exteriorClassRepresentative c).property)).choose_spec.1

theorem classSupportWitness_ne_zero (c : ClassGroup (𝓞 K)) : classSupportWitness c ≠ 0 :=
  ((Submodule.ne_bot_iff _).mp (mem_nonZeroDivisors_iff_ne_zero.mp
    (exteriorClassRepresentative c).property)).choose_spec.2

def primeSupportWitness (p : HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  ((Submodule.ne_bot_iff _).mp p.ne_bot).choose

omit [NumberField K] in
theorem primeSupportWitness_mem (p : HeightOneSpectrum (𝓞 K)) :
    primeSupportWitness p ∈ p.asIdeal := ((Submodule.ne_bot_iff _).mp p.ne_bot).choose_spec.1

omit [NumberField K] in
theorem primeSupportWitness_ne_zero (p : HeightOneSpectrum (𝓞 K)) : primeSupportWitness p ≠ 0 :=
  ((Submodule.ne_bot_iff _).mp p.ne_bot).choose_spec.2

def principalizingDenominator (S₀ : Finset (HeightOneSpectrum (𝓞 K))) : 𝓞 K :=
  (∏ c : ClassGroup (𝓞 K), classSupportWitness c) * ∏ p ∈ S₀, primeSupportWitness p

theorem principalizingDenominator_ne_zero (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    principalizingDenominator S₀ ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun c _ => classSupportWitness_ne_zero c))
    (Finset.prod_ne_zero_iff.mpr (fun p _ => primeSupportWitness_ne_zero p))

theorem classSupportWitness_dvd_denominator (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (c : ClassGroup (𝓞 K)) : classSupportWitness c ∣ principalizingDenominator S₀ :=
  dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (f := classSupportWitness) (Finset.mem_univ c)) _

theorem primeSupportWitness_dvd_denominator (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S₀) : primeSupportWitness p ∣ principalizingDenominator S₀ :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (f := primeSupportWitness) hp) _

def principalizingSet (S₀ : Finset (HeightOneSpectrum (𝓞 K))) : Finset (HeightOneSpectrum (𝓞 K)) :=
  denominatorSupport (principalizingDenominator S₀) (principalizingDenominator_ne_zero S₀)

theorem required_subset_principalizingSet (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    S₀ ⊆ principalizingSet S₀ := by
  intro p hp
  apply (mem_denominatorSupport _ _ p).mpr
  obtain ⟨a, ha⟩ := primeSupportWitness_dvd_denominator S₀ p hp
  rw [ha]
  exact p.asIdeal.mul_mem_right a (primeSupportWitness_mem p)

abbrev PrincipalIntegerRing (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :=
  IntegerRing (K := K) (principalizingSet S₀)

theorem principalIntegerRing_isLocalization (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
  integerRing_isLocalization_away _ (principalizingDenominator_ne_zero S₀) _
    (fun p => mem_denominatorSupport _ _ p)

theorem principalIntegerRing_isDedekindDomain (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsDedekindDomain (PrincipalIntegerRing S₀) :=
  integerRing_isDedekindDomain _ (principalizingDenominator_ne_zero S₀) _
    (fun p => mem_denominatorSupport _ _ p)

theorem classRepresentative_map_eq_top (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (c : ClassGroup (𝓞 K)) :
    (exteriorClassRepresentative c).val.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = ⊤ := by
  have hu := denominator_isUnit (principalizingDenominator S₀) (principalizingDenominator_ne_zero S₀)
    (principalizingSet S₀) (fun p => mem_denominatorSupport _ _ p)
  have hw : IsUnit (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) (classSupportWitness c)) :=
    isUnit_of_dvd_unit (map_dvd _ (classSupportWitness_dvd_denominator S₀ c)) hu
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (classSupportWitness_mem c)) hw

theorem principalIntegerRing_classGroup_subsingleton (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    Subsingleton (ClassGroup (PrincipalIntegerRing S₀)) := by
  let : IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
    principalIntegerRing_isLocalization S₀
  let : IsDedekindDomain (PrincipalIntegerRing S₀) := principalIntegerRing_isDedekindDomain S₀
  apply localization_classGroup_subsingleton (Submonoid.powers (principalizingDenominator S₀))
    exteriorClassRepresentative exteriorClassRepresentative_class
  exact classRepresentative_map_eq_top S₀

theorem principalIntegerRing_isPrincipalIdealRing (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsPrincipalIdealRing (PrincipalIntegerRing S₀) := by
  let : IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
    principalIntegerRing_isLocalization S₀
  let : IsDedekindDomain (PrincipalIntegerRing S₀) := principalIntegerRing_isDedekindDomain S₀
  apply localization_isPrincipalIdealRing_of_representatives
    (Submonoid.powers (principalizingDenominator S₀))
    exteriorClassRepresentative exteriorClassRepresentative_class
  exact classRepresentative_map_eq_top S₀

theorem exists_finite_principal_sIntegers (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧ IsPrincipalIdealRing (IntegerRing (K := K) S) :=
  ⟨principalizingSet S₀, required_subset_principalizingSet S₀,
    principalIntegerRing_isPrincipalIdealRing S₀⟩

theorem exists_integer_ideal_generator (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Ideal (PrincipalIntegerRing S₀)) : ∃ a, I = Ideal.span {a} := by
  let : IsPrincipalIdealRing (PrincipalIntegerRing S₀) := principalIntegerRing_isPrincipalIdealRing S₀
  exact Submodule.IsPrincipal.principal I

theorem exists_nonzero_integer_ideal_generator (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Ideal (PrincipalIntegerRing S₀)) (hI : I ≠ ⊥) : ∃ a ≠ 0, I = Ideal.span {a} := by
  obtain ⟨a, ha⟩ := exists_integer_ideal_generator S₀ I
  refine ⟨a, ?_, ha⟩
  intro he
  apply hI
  simpa only [he, Ideal.span_singleton_zero] using ha

end
end ArtinMatthews.SIntegerPrincipalization
