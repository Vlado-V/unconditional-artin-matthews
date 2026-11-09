module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Elementary automorphism calculations for rational cubic radicals. -/

namespace ArtinMatthews

lemma cube_aut_ratio {K : Type*} [Field K] [Algebra ℚ K]
    (σ : K ≃ₐ[ℚ] K) {x : K} (hx : x ≠ 0) {a : ℚ}
    (ha : x ^ 3 = algebraMap ℚ K a) : (σ x / x) ^ 3 = 1 := by
  rw [div_pow, ← map_pow, ha, σ.commutes, div_self]
  rw [← ha]
  exact pow_ne_zero _ hx

lemma aut_cube_apply_of_fixed_cube_roots {K : Type*} [Field K] [Algebra ℚ K]
    (σ : K ≃ₐ[ℚ] K) (hfix : ∀ r : K, r ^ 3 = 1 → σ r = r)
    {x : K} {a : ℚ} (ha : x ^ 3 = algebraMap ℚ K a) : (σ ^ 3) x = x := by
  by_cases hx : x = 0
  · simp [hx]
  let r := σ x / x
  have hr : r ^ 3 = 1 := cube_aut_ratio σ hx ha
  have hσr : σ r = r := hfix r hr
  have hσx : σ x = r * x := by dsimp [r]; field_simp
  change σ (σ (σ x)) = x
  simp only [hσx, map_mul, hσr]
  calc
    r * (r * (r * x)) = r ^ 3 * x := by ring
    _ = x := by rw [hr, one_mul]

lemma conjugate_aut_apply_of_cubic_radical {K : Type*} [Field K] [Algebra ℚ K]
    (σ τ : K ≃ₐ[ℚ] K)
    (hfix : ∀ r : K, r ^ 3 = 1 → σ r = r)
    (hinv : ∀ r : K, r ^ 3 = 1 → τ r = r⁻¹)
    {x : K} {a : ℚ} (ha : x ^ 3 = algebraMap ℚ K a) :
    τ (σ (τ x)) = σ⁻¹ x := by
  by_cases hx : x = 0
  · simp [hx]
  let r := σ x / x
  let s := τ x / x
  have hr : r ^ 3 = 1 := cube_aut_ratio σ hx ha
  have hs : s ^ 3 = 1 := cube_aut_ratio τ hx ha
  have hr0 : r ≠ 0 := by intro hz; simp [hz] at hr
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hs
  have hσr : σ r = r := hfix r hr
  have hσs : σ s = s := hfix s hs
  have hτr : τ r = r⁻¹ := hinv r hr
  have hτs : τ s = s⁻¹ := hinv s hs
  have hσx : σ x = r * x := by dsimp [r]; field_simp
  have hτx : τ x = s * x := by dsimp [s]; field_simp
  have hleft : τ (σ (τ x)) = r⁻¹ * x := by
    rw [hτx, map_mul, hσs, hσx, map_mul, map_mul, hτs, hτr, hτx]
    field_simp
  have hright : σ⁻¹ x = r⁻¹ * x := by
    apply σ.injective
    rw [show σ (σ⁻¹ x) = x from σ.apply_symm_apply x, map_mul, map_inv₀, hσr, hσx]
    field_simp
  exact hleft.trans hright.symm

end ArtinMatthews
