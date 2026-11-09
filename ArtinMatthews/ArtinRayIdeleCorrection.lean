module

public import ArtinMatthews.ArtinRayCompletedPower


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-place power corrections of principal ideles. -/
noncomputable section
open scoped NumberField Classical
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
variable {K : Type*} [Field K] [NumberField K]

/-- A rational congruence modulo `D*n²` supplies an integral correction
idele whose `n`-th power cancels the prescribed bad-place components. -/
theorem exists_integral_power_correction
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (D n : ℕ) (hn : 0 < n)
    (hD : ∀ v ∈ S, (D : 𝓞 K) ∈ v.asIdeal)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hc : a - 1 ∈ rationalModulusIdeal (𝓞 K) (D * n^2)) :
    ∃ B : IdeleGroup K, IdeleGroup.fractionalIdeal B = 1 ∧
      ∀ v ∈ S, IdeleGroup.finiteComponent v
        (IdeleGroup.principalIdele K
          (Units.mk0 (a : K) (by exact_mod_cast ha)) * B^n) = 1 := by
  choose r hr using fun v : ↥S =>
    completed_principal_exists_unit_pow v.1 D n hn (hD v.1 v.2) hc
  let u (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      (v.adicCompletionIntegers K).units :=
    if h : v ∈ S then
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm (r ⟨v,h⟩)
    else 1
  let B : IdeleGroup K := (1, ⟨fun v => ((u v : (v.adicCompletion K)ˣ)⁻¹),
    Filter.Eventually.of_forall fun v =>
      (v.adicCompletionIntegers K).units.inv_mem (u v).property⟩)
  refine ⟨B, ?_, ?_⟩
  · apply MonoidHom.mem_ker.mp
    rw [IdeleGroup.fractionalIdeal_ker]
    intro v
    exact (v.adicCompletionIntegers K).units.inv_mem (u v).property
  · intro v hv
    apply Units.ext
    change ((a : K) : v.adicCompletion K) *
      (((u v : (v.adicCompletion K)ˣ)⁻¹ : (v.adicCompletion K)ˣ) :
        v.adicCompletion K)^n = 1
    have hroot : ((u v : (v.adicCompletion K)ˣ) : v.adicCompletion K)^n =
        ((a : K) : v.adicCompletion K) := by
      have h := congrArg (fun z : v.adicCompletionIntegers K =>
        (z : v.adicCompletion K)) (hr ⟨v,hv⟩)
      dsimp only [u]
      rw [dite_eq_left hv]
      change (((r ⟨v,hv⟩ : v.adicCompletionIntegers K) : v.adicCompletion K)^n) = _
      exact h
    rw [← hroot, ← mul_pow]
    simp

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
