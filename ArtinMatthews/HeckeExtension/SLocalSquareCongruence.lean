module

public import ArtinMatthews.SLocalWeakApproximation
public import ArtinMatthews.SixthLocalHenselRay
public import ArtinMatthews.ArtinRayLocalCongruence


set_option backward.privateInPublic true
@[expose] public section

/-! An explicit finite congruence kills all actual S-local square classes.
The local sixth roots are supplied by genuine Hensel lifting. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory
open VaryingKummerAnalytic VaryingKummerAnalytic.ArtinRay
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sLocalGlobalSquareClass_eq_one_of_higher_congruence
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : 𝓞 K) (ha : a ≠ 0)
    (hc : ∀ v ∈ S,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ sixthLocalHenselDepth v) :
    sLocalGlobalClassMap K 2 S (Units.mk0 (a : K) (by exact_mod_cast ha)) = 1 := by
  funext v
  let u := Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom
    (Units.mk0 (a : K) (by exact_mod_cast ha))
  have hu : u ∈ RayClass.localHigherUnitGroup v.val (sixthLocalHenselDepth v.val) :=
    principal_local_mem_higherUnits v.val (sixthLocalHenselDepth_pos v.val) a ha
      (hc v.val v.property)
  obtain ⟨w, hw⟩ := sixthLocal_higherUnit_exists_root v.val u hu
  change powerClass (v.val.adicCompletion K) 2 u = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨w ^ 3, ?_⟩
  change (w ^ 3) ^ 2 = u
  simpa only [← pow_mul] using hw

theorem exists_sLocalSquare_congruence_modulus
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ N : ℕ, 0 < N ∧ ∀ (a : 𝓞 K) (ha : a ≠ 0),
      a - 1 ∈ rationalModulusIdeal (𝓞 K) N →
      sLocalGlobalClassMap K 2 S (Units.mk0 (a : K) (by exact_mod_cast ha)) = 1 := by
  obtain ⟨N, hN, _, hlocal⟩ := exists_integer_for_local_congruences
    S sixthLocalHenselDepth (D := 1) (by decide)
  refine ⟨N, hN, fun a ha hc => ?_⟩
  apply sLocalGlobalSquareClass_eq_one_of_higher_congruence K S a ha
  intro v hv
  exact completed_congruence_of_integer v _ N (hlocal v hv) hc

end
end ArtinMatthews
