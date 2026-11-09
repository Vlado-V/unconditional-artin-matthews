module

public import ArtinMatthews.SpectralHeightProfileBlocks
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


set_option backward.privateInPublic true
@[expose] public section

/-! The two explicit dyadic height budgets are summable for decay exponent
strictly larger than one. These are scalar estimates for the actual
annular cutoff construction. -/

noncomputable section
open Set
namespace ArtinMatthews

theorem spectralHeight_large_budget_summable {p : ℝ} (hp : 0 < p) :
    Summable (fun k : ℕ => ((2 : ℝ)^k)^(-p)*(1+2/(2 : ℝ)^k)) := by
  let q : ℝ := (2 : ℝ)^(-p)
  have hq₀ : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hp)
  have hg := (summable_geometric_of_lt_one hq₀ hq₁).mul_left 3
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hg
  intro k
  have hpow : 1 ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  have hfrac : 2/(2 : ℝ)^k ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) (-p) k]
  change q^k*(1+2/(2 : ℝ)^k) ≤ 3*q^k
  nlinarith [pow_nonneg hq₀ k]

theorem spectralHeight_small_budget_summable {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ => (4*((2 : ℝ)^(k+1))⁻¹)^p*
      (1+2/((2 : ℝ)^(k+1))⁻¹)) := by
  let q : ℝ := (2 : ℝ)^(-(p-1))
  have hq₀ : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg := ((summable_geometric_of_lt_one hq₀ hq₁).mul_right q).mul_left (3*(4 : ℝ)^p)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hg
  intro k
  let A : ℝ := ((2 : ℝ)^(k+1))⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hA₁ : A ≤ 1 := by
    dsimp only [A]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hfactor : 1+2/A ≤ 3/A := by
    apply (le_div_iff₀ hA).mpr
    field_simp [hA.ne']
    linarith
  have hpower : A^(p-1) = q^k*q := by
    dsimp only [A,q]
    rw [← Real.rpow_neg_eq_inv_rpow,← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),pow_succ]
  change (4*A)^p*(1+2/A) ≤ (3*(4 : ℝ)^p)*(q^k*q)
  calc
    _ = (4 : ℝ)^p*(A^p*(1+2/A)) := by rw [Real.mul_rpow (by norm_num) hA.le]; ring
    _ ≤ (4 : ℝ)^p*(A^p*(3/A)) := by gcongr
    _ = (3*(4 : ℝ)^p)*A^(p-1) := by rw [Real.rpow_sub_one hA.ne']; ring
    _ = _ := by rw [hpower]

theorem spectralHeightProfileBlock_large_bound (ρ : ℝ → ℝ) {p C A : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (hA : 0 < A)
    (hb : ∀ y, 0 < y → ‖ρ y‖ ≤ C*y^(-p)) (y : ℝ) :
    ‖spectralHeightProfileBlock A ρ y‖ ≤ C*A^(-p) := by
  apply spectralHeightProfileBlock_norm_le hA (by positivity) ρ _ y
  intro z hz
  exact (hb z (hA.trans_le hz.1)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hA hz.1 (neg_nonpos.mpr hp.le)) hC)

theorem spectralHeightProfileBlock_small_bound (ρ : ℝ → ℝ) {p C A : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hA : 0 < A)
    (hb : ∀ y, 0 < y → ‖ρ y‖ ≤ C*y^p) (y : ℝ) :
    ‖spectralHeightProfileBlock A ρ y‖ ≤ C*(4*A)^p := by
  apply spectralHeightProfileBlock_norm_le hA (by positivity) ρ _ y
  intro z hz
  exact (hb z (hA.trans_le hz.1)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hA.le.trans hz.1) hz.2 hp) hC)

end ArtinMatthews
