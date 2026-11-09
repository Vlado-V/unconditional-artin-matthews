module

public import ArtinMatthews.SixthLocalHenselDVR
public import ArtinMatthews.ArtinRayCompletedPower


set_option backward.privateInPublic true
@[expose] public section

/-! Sixth roots in actual finite-place completions of arbitrary number fields.
The finite depth is `2*v(6)+1`, and equals one at every prime not dividing `6`. -/

noncomputable section

open scoped NumberField
open IsDedekindDomain

namespace ArtinMatthews

variable {K : Type*} [Field K] [NumberField K]

/-- The explicit sixth-root depth in the actual completed integer ring. -/
def sixthLocalHenselDepth (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  sixthHenselDepth (v.adicCompletionIntegers K)

theorem sixthLocalHenselDepth_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < sixthLocalHenselDepth v :=
  sixthHenselDepth_pos

/-- An integer outside the original prime remains a unit in the completion. -/
theorem completed_isUnit_of_not_mem (v : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    IsUnit (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) := by
  apply HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr
  change Valued.v ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) = 1
  rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr ha

theorem sixthLocalHenselDepth_eq_one (v : HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) :
    sixthLocalHenselDepth v = 1 := by
  apply sixthHenselDepth_eq_one_of_isUnit
  simpa only [map_ofNat] using completed_isUnit_of_not_mem v 6 h6

theorem sixthLocal_six_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    (6 : v.adicCompletionIntegers K) ≠ 0 := by
  intro h
  have h' : algebraMap (𝓞 K) (v.adicCompletionIntegers K) (6 : 𝓞 K) =
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) 0 := by
    simpa only [map_ofNat, map_zero] using h
  exact (by norm_num : (6 : 𝓞 K) ≠ 0)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)) h')

/-- Every sufficiently deep completed integer unit has an actual sixth root. -/
theorem sixthLocal_exists_root (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletionIntegers K)ˣ)
    (hu : (u : v.adicCompletionIntegers K) - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ sixthLocalHenselDepth v) :
    ∃ w : (v.adicCompletionIntegers K)ˣ, w^6 = u := by
  let := VaryingKummerAnalytic.ArtinRay.completedIntegers_henselianLocalRing v
  exact exists_sixthRoot_of_depth (sixthLocal_six_ne_zero v) u hu

/-- Every principal unit at a prime not dividing `6` has an actual sixth root. -/
theorem sixthLocal_exists_root_of_not_mem (v : HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (u : (v.adicCompletionIntegers K)ˣ)
    (hu : (u : v.adicCompletionIntegers K) - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    ∃ w : (v.adicCompletionIntegers K)ˣ, w^6 = u := by
  apply sixthLocal_exists_root v u
  simpa only [sixthLocalHenselDepth_eq_one v h6, pow_one] using hu

/-- A depth works uniformly for all units in the local principal-unit filtration. -/
theorem sixthLocal_exists_depth (v : HeightOneSpectrum (𝓞 K)) :
    ∃ c : ℕ, 0 < c ∧ ∀ u : (v.adicCompletionIntegers K)ˣ,
      (u : v.adicCompletionIntegers K) - 1 ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ c →
      ∃ w : (v.adicCompletionIntegers K)ˣ, w^6 = u :=
  ⟨sixthLocalHenselDepth v, sixthLocalHenselDepth_pos v, sixthLocal_exists_root v⟩

end ArtinMatthews
