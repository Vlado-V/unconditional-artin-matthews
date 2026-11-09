module

public import ArtinMatthews.GiantFixedResidueSieve
public import Mathlib.Data.Nat.Totient


set_option backward.privateInPublic true
@[expose] public section

/-! The exact local density for a fixed unit residue, including the
Euler factors of the modulus and the resulting totient normalization. -/
namespace ArtinMatthews
open Filter
open scoped Topology BigOperators
noncomputable section

theorem giantFixedResidueEuler_split (M : ℕ) {y : ℝ} (hM : 0 < M) (hy : (M:ℝ) ≤ y) :
    markedSieveEulerProduct y =
      (∏ p∈M.primeFactors,(1-1/(p:ℝ)))*giantFixedResidueEuler M y := by
  classical
  let P := Nat.primesLE ⌊y⌋₊
  let f (p : ℕ) := 1-1/(p:ℝ)
  have hy0 : 0≤y := (Nat.cast_nonneg M).trans hy
  have hQ : P.filter (fun p => p∣M) = M.primeFactors := by
    ext p
    simp only [P,Finset.mem_filter,Nat.mem_primesLE,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_,hp⟩,hd⟩
      exact ⟨hp,hd,hM.ne'⟩
    · rintro ⟨hp,hd,_⟩
      exact ⟨⟨(Nat.le_floor_iff hy0).mpr ((Nat.cast_le.mpr (Nat.le_of_dvd hM hd)).trans hy),
        hp⟩,hd⟩
  have hf : giantFixedResidueEuler M y = ∏ p∈P.filter (fun p => ¬p∣M),f p := by
    unfold giantFixedResidueEuler giantFixedResidueHitDensity
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : p∣M
    · simp only [ite_eq_left hp,sub_zero,ite_eq_right (not_not_intro hp)]
    · simp only [ite_eq_right hp,ite_eq_left hp,f]
  rw [hf,← hQ]
  exact (Finset.prod_filter_mul_prod_filter_not P (fun p => p∣M) f).symm

theorem giantFixedResidueEuler_div_eq (M : ℕ) {y : ℝ} (hM : 0 < M) (hy : (M:ℝ) ≤ y) :
    giantFixedResidueEuler M y/(M:ℝ) = markedSieveEulerProduct y/(M.totient:ℝ) := by
  have hφ := congrArg (fun t : ℚ => (t:ℝ)) (Nat.totient_eq_mul_prod_factors M)
  push_cast at hφ
  simp only [← one_div] at hφ
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hφ0 : (M.totient:ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hM).ne'
  apply (div_eq_div_iff hM0 hφ0).mpr
  rw [giantFixedResidueEuler_split M hM hy, hφ]
  ring

theorem giantFixedResidueEuler_power_log_tendsto (M : ℕ) (hM : 0 < M) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun x : ℝ => Real.log x * (giantFixedResidueEuler M (x^γ)/(M:ℝ)))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)/(γ*(M.totient:ℝ)))) := by
  have h := (markedSieveEulerProduct_power_log_tendsto hγ).div_const (M.totient:ℝ)
  rw [div_div] at h
  apply h.congr'
  filter_upwards [(tendsto_rpow_atTop hγ).eventually (eventually_ge_atTop (M:ℝ))] with x hx
  rw [giantFixedResidueEuler_div_eq M hM hx]
  ring

end
end ArtinMatthews
