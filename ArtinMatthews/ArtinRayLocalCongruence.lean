module

public import ArtinMatthews.VaryingKummerAnalyticRayCharacter
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology


set_option backward.privateInPublic true
@[expose] public section

/-! A positive rational integer enforces every finite conductor congruence.
These local higher-unit assertions are proved for the actual completions. -/
noncomputable section
open scoped NumberField BigOperators Classical

namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay


variable {K : Type*} [Field K] [NumberField K]

theorem integral_mem_completed_maximal
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {a : 𝓞 K} (ha : a ∈ v.asIdeal) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  apply (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).mpr
  change Valued.v ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) < 1
  rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
  exact (v.intValuation_lt_one_iff_mem a).mpr ha

theorem exists_integer_for_local_congruences
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (c : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    {D : ℕ} (hD : 0 < D) :
    ∃ N : ℕ, 0 < N ∧ D ∣ N ∧ ∀ v ∈ S,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ c v := by
  let N := D * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ c v
  have hnorm (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      0 < Ideal.absNorm v.asIdeal := by
    apply Nat.pos_of_ne_zero
    intro h
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  refine ⟨N, Nat.mul_pos hD (Finset.prod_pos (fun v _ => pow_pos (hnorm v) _)),
    dvd_mul_right D _, ?_⟩
  intro v hv
  have hd : Ideal.absNorm v.asIdeal ^ c v ∣ N := by
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _
  obtain ⟨k, hk⟩ := hd
  have hm := Ideal.pow_mem_pow
    (integral_mem_completed_maximal v (Ideal.absNorm_mem v.asIdeal)) (c v)
  rw [hk, Nat.cast_mul, map_mul, Nat.cast_pow, map_pow]
  exact Ideal.mul_mem_right _ _ hm

theorem completed_congruence_of_integer
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c N : ℕ)
    (hN : algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ c)
    {a : 𝓞 K} (ha : a - 1 ∈ rationalModulusIdeal (𝓞 K) N) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ c := by
  have hd : (N : 𝓞 K) ∣ a - 1 := Ideal.mem_span_singleton.mp ha
  obtain ⟨b, hb⟩ := hd
  rw [← map_one (algebraMap (𝓞 K) (v.adicCompletionIntegers K)), ← map_sub, hb, map_mul]
  exact Ideal.mul_mem_right _ _ hN

theorem completed_integral_isUnit_of_congruence
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {c : ℕ} (hc : 0 < c)
    {a : 𝓞 K}
    (ha : algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ c) :
    IsUnit (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) := by
  apply (IsLocalRing.notMem_maximalIdeal).mp
  intro hmem
  have hsub := (Ideal.pow_le_self hc.ne') ha
  have hone : (1 : v.adicCompletionIntegers K) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    simpa only [sub_sub_cancel] using
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).sub_mem hmem hsub
  exact (IsLocalRing.maximalIdeal.isMaximal (v.adicCompletionIntegers K)).ne_top
    ((Ideal.eq_top_iff_one _).mpr hone)

theorem principal_local_mem_higherUnits
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {c : ℕ} (hc : 0 < c)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcong : algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ c) :
    (IdeleGroup.principalIdele K
      (Units.mk0 (a : K) (by exact_mod_cast ha))).2 v ∈
        RayClass.localHigherUnitGroup v c := by
  let hu := completed_integral_isUnit_of_congruence v hc hcong
  let z : (v.adicCompletionIntegers K)ˣ := hu.unit
  let y : (v.adicCompletionIntegers K).units :=
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z
  apply (RayClass.mem_localHigherUnitGroup_iff v c _).mpr
  refine ⟨y, ?_, ?_⟩
  · apply Units.ext
    change ((z : v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((a : K) : v.adicCompletion K)
    rw [show (z : v.adicCompletionIntegers K) =
        algebraMap (𝓞 K) (v.adicCompletionIntegers K) a from hu.unit_spec]
    rfl
  · apply (RayClass.localHigherUnitMap_eq_one_iff v c y).mpr
    change (z : v.adicCompletionIntegers K) - 1 ∈ _
    rwa [show (z : v.adicCompletionIntegers K) =
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) a from hu.unit_spec]

theorem principalIdele_mem_even_ray_of_congruence
    (m : RayClass.Modulus K) (hm : m.infinitePart = ∅)
    (N : ℕ)
    (hN : ∀ v ∈ m.finitePart.support,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m.finitePart v)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcong : a - 1 ∈ rationalModulusIdeal (𝓞 K) N) :
    IdeleGroup.principalIdele K (Units.mk0 (a : K) (by exact_mod_cast ha)) ∈
      RayClass.idelePrimeToModulusSubgroup m := by
  constructor
  · change (IdeleGroup.principalIdele K
      (Units.mk0 (a : K) (by exact_mod_cast ha))).1 ∈ m.infiniteCongruenceSubgroup
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    intro v hv
    simp only [hm, Finset.notMem_empty] at hv
  · intro v hv
    apply principal_local_mem_higherUnits v
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)) a ha
    exact completed_congruence_of_integer v (m.finitePart v) N (hN v hv) hcong

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
