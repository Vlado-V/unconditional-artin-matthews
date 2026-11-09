module

public import ArtinMatthews.SixthLocalHensel


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ray higher units are sixth powers, hence actual local norms for
extensions whose degree divides six. The norm statement retains this degree
condition and makes no assertion about a common Kummer compositum. -/

noncomputable section

open scoped NumberField
open IsDedekindDomain

namespace ArtinMatthews

variable {K : Type*} [Field K] [NumberField K]

/-- Every higher unit at the explicit depth is a sixth power in the completion. -/
theorem sixthLocal_higherUnit_exists_root (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ)
    (hu : u ∈ RayClass.localHigherUnitGroup v (sixthLocalHenselDepth v)) :
    ∃ w : (v.adicCompletion K)ˣ, w^6 = u := by
  obtain ⟨y, rfl, hy⟩ := (RayClass.mem_localHigherUnitGroup_iff v _ u).mp hu
  let z : (v.adicCompletionIntegers K)ˣ :=
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y
  have hz : (z : v.adicCompletionIntegers K) - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ sixthLocalHenselDepth v :=
    (RayClass.localHigherUnitMap_eq_one_iff v _ y).mp hy
  obtain ⟨w, hw⟩ := sixthLocal_exists_root v z hz
  refine ⟨Units.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)).toMonoidHom w, ?_⟩
  apply Units.ext
  have h := congrArg (fun x : (v.adicCompletionIntegers K)ˣ =>
    ((x : v.adicCompletionIntegers K) : v.adicCompletion K)) hw
  exact h

theorem sixthLocal_higherUnit_le_sixthPowers (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v (sixthLocalHenselDepth v) ≤
      (powMonoidHom (α := (v.adicCompletion K)ˣ) 6).range := by
  intro u hu
  obtain ⟨w, hw⟩ := sixthLocal_higherUnit_exists_root v u hu
  exact ⟨w, hw⟩

/-- At a prime not dividing six the first ray higher-unit group suffices. -/
theorem sixthLocal_principalUnit_exists_root (v : HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (u : (v.adicCompletion K)ˣ)
    (hu : u ∈ RayClass.localHigherUnitGroup v 1) :
    ∃ w : (v.adicCompletion K)ˣ, w^6 = u := by
  apply sixthLocal_higherUnit_exists_root v u
  simpa only [sixthLocalHenselDepth_eq_one v h6] using hu

/-- Actual sixth powers are norms when the actual local degree divides six. -/
theorem sixthLocal_norm_of_root (v : HeightOneSpectrum (𝓞 K))
    (L : Type*) [Field L] [Algebra (v.adicCompletion K) L]
    [FiniteDimensional (v.adicCompletion K) L]
    (hd : Module.finrank (v.adicCompletion K) L ∣ 6)
    (u r : (v.adicCompletion K)ˣ) (hr : r^6 = u) :
    ∃ w : Lˣ, Units.map (Algebra.norm (v.adicCompletion K) : L →* v.adicCompletion K) w = u := by
  obtain ⟨w, hw⟩ := HenselPower.exists_unit_norm_of_pow (R := v.adicCompletion K)
    (K := v.adicCompletion K) (L := L) 6 hd u r hr
  refine ⟨w, ?_⟩
  apply Units.ext
  have h := congrArg Units.val hw
  change Algebra.norm (v.adicCompletion K) (w : L) = (u : v.adicCompletion K) at h
  exact h

/-- The explicit higher-unit group is contained in the genuine local norm group. -/
theorem sixthLocal_higherUnit_exists_norm (v : HeightOneSpectrum (𝓞 K))
    (L : Type*) [Field L] [Algebra (v.adicCompletion K) L]
    [FiniteDimensional (v.adicCompletion K) L]
    (hd : Module.finrank (v.adicCompletion K) L ∣ 6)
    (u : (v.adicCompletion K)ˣ)
    (hu : u ∈ RayClass.localHigherUnitGroup v (sixthLocalHenselDepth v)) :
    ∃ w : Lˣ, Units.map (Algebra.norm (v.adicCompletion K) : L →* v.adicCompletion K) w = u := by
  obtain ⟨r, hr⟩ := sixthLocal_higherUnit_exists_root v u hu
  exact sixthLocal_norm_of_root v L hd u r hr

theorem sixthLocal_higherUnit_le_norm (v : HeightOneSpectrum (𝓞 K))
    (L : Type*) [Field L] [Algebra (v.adicCompletion K) L]
    [FiniteDimensional (v.adicCompletion K) L]
    (hd : Module.finrank (v.adicCompletion K) L ∣ 6) :
    RayClass.localHigherUnitGroup v (sixthLocalHenselDepth v) ≤
      (Units.map (Algebra.norm (v.adicCompletion K) : L →* v.adicCompletion K)).range := by
  intro u hu
  exact sixthLocal_higherUnit_exists_norm v L hd u hu

theorem sixthLocal_principalUnit_le_norm (v : HeightOneSpectrum (𝓞 K))
    (L : Type*) [Field L] [Algebra (v.adicCompletion K) L]
    [FiniteDimensional (v.adicCompletion K) L]
    (hd : Module.finrank (v.adicCompletion K) L ∣ 6)
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) :
    RayClass.localHigherUnitGroup v 1 ≤
      (Units.map (Algebra.norm (v.adicCompletion K) : L →* v.adicCompletion K)).range := by
  simpa only [sixthLocalHenselDepth_eq_one v h6] using sixthLocal_higherUnit_le_norm v L hd

end ArtinMatthews
