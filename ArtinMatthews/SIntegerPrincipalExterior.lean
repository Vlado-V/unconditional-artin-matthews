module

public import ArtinMatthews.SIntegerFinitePrincipalization
public import ArtinMatthews.SIntegerExteriorIdealEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! The constructed principal S-integer ring has the expected exterior
ideal equivalence and genuine field generators, including fractional
ideals. Its fraction field and PID structure are conclusions. -/

namespace ArtinMatthews.SIntegerPrincipalization
open NumberField IsDedekindDomain FractionalIdeal Set
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem coprime_denominator_iff_exterior (d : 𝓞 K) (hd : d ≠ 0) (I : Ideal (𝓞 K)) :
    IsCoprime I (Ideal.span {d}) ↔
      ∀ p : HeightOneSpectrum (𝓞 K), p ∈ denominatorSupport d hd → ¬ p.asIdeal ∣ I := by
  constructor
  · intro hc p hp hdiv
    have hle : (⊤ : Ideal (𝓞 K)) ≤ p.asIdeal := by
      rw [← hc.sup_eq]
      exact sup_le (Ideal.le_of_dvd hdiv)
        ((Ideal.span_singleton_le_iff_mem _).mpr ((mem_denominatorSupport d hd p).mp hp))
    exact p.isPrime.ne_top (top_unique hle)
  · intro hext
    apply Ideal.coprime_of_no_prime_ge
    intro P hIP hDP hP
    have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hd) hDP
    let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP, hP0⟩
    apply hext p
      ((mem_denominatorSupport d hd p).mpr (hDP (Ideal.subset_span (by simp))))
    exact Ideal.dvd_iff_le.mpr hIP

def principalExteriorIdealEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    exteriorIdeals (principalizingDenominator S₀) ≃* (Ideal (PrincipalIntegerRing S₀))⁰ := by
  let : IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
    principalIntegerRing_isLocalization S₀
  exact awayExteriorIdealEquiv (A := PrincipalIntegerRing S₀) (principalizingDenominator S₀)

@[simp] theorem principalExteriorIdealEquiv_apply (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : exteriorIdeals (principalizingDenominator S₀)) :
    (principalExteriorIdealEquiv S₀ I).val = I.val.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := rfl

theorem exteriorIdeals_mem_iff (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)) :
    I ∈ exteriorIdeals (principalizingDenominator S₀) ↔
      I ≠ ⊥ ∧ ∀ p : HeightOneSpectrum (𝓞 K), p ∈ principalizingSet S₀ → ¬ p.asIdeal ∣ I := by
  change (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {principalizingDenominator S₀})) ↔ _
  rw [coprime_denominator_iff_exterior _ (principalizingDenominator_ne_zero S₀)]
  rfl

theorem principalIntegerRing_isFractionRing (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsFractionRing (PrincipalIntegerRing S₀) K := by
  let : IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
    principalIntegerRing_isLocalization S₀
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (principalizingDenominator S₀)) (PrincipalIntegerRing S₀) K

attribute [local instance] principalIntegerRing_isFractionRing

theorem exists_exterior_field_generator (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : exteriorIdeals (principalizingDenominator S₀)) :
    ∃ (u : Kˣ) (a : PrincipalIntegerRing S₀), (u : K) = (a : K) ∧
      I.val.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a} := by
  let J := principalExteriorIdealEquiv S₀ I
  obtain ⟨a, ha, hgen⟩ := exists_nonzero_integer_ideal_generator S₀ J.val
    (mem_nonZeroDivisors_iff_ne_zero.mp J.property)
  have haK : (a : K) ≠ 0 := by
    intro he
    apply ha
    exact Subtype.ext he
  exact ⟨Units.mk0 (a : K) haK, a, rfl, hgen⟩

theorem exists_fractional_field_generator (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : (FractionalIdeal (PrincipalIntegerRing S₀)⁰ K)ˣ) :
    ∃ u : Kˣ, toPrincipalIdeal (PrincipalIntegerRing S₀) K u = I := by
  let : Subsingleton (ClassGroup (PrincipalIntegerRing S₀)) :=
    principalIntegerRing_classGroup_subsingleton S₀
  have hI : ClassGroup.mk K I = 1 := Subsingleton.elim _ _
  have h := congrArg (ClassGroup.equiv K) hI
  have hrefl : Units.mapEquiv (MulEquiv.refl (FractionalIdeal (PrincipalIntegerRing S₀)⁰ K)) I = I :=
    Units.ext rfl
  have hr : I ∈ (toPrincipalIdeal (PrincipalIntegerRing S₀) K).range := by
    simpa only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
      RingEquiv.coe_mulEquiv_refl, hrefl, map_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] using h
  exact hr

end
end ArtinMatthews.SIntegerPrincipalization
