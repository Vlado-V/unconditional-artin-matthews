module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Set


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial cutoff mass gives an integrable reciprocal-power majorant. -/
namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

theorem spectralQuadraticMass_quartic_integrable
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (τ D : X → ℝ)
    (hτ : Measurable τ) (hτ₁ : ∀ x, 1 ≤ τ x) (hD : ∀ x, 0 ≤ D x)
    (C : ℝ) (hC : 0 ≤ C)
    (hcut : ∀ R : ℝ, 1 ≤ R →
      IntegrableOn D {x | τ x ≤ R} μ ∧
        (∫ x in {x | τ x ≤ R}, D x ∂μ) ≤ C * R ^ 2) :
    Integrable (fun x => D x / τ x ^ 4) μ := by
  let S (n : ℕ) := τ ⁻¹' Icc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))
  let F (x : X) := D x / τ x ^ 4
  have hS (n : ℕ) : MeasurableSet (S n) := hτ measurableSet_Icc
  have hsub (n : ℕ) : S n ⊆ {x | τ x ≤ (2 : ℝ) ^ (n + 1)} := fun _ hx => hx.2
  have hR (n : ℕ) : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hInt (n : ℕ) : IntegrableOn D (S n) μ := ((hcut _ (hR n)).1).mono_set (hsub n)
  have hF (n : ℕ) : IntegrableOn F (S n) μ := by
    have hmeas : AEStronglyMeasurable F (μ.restrict (S n)) := by
      have hm := (hInt n).aestronglyMeasurable.mul ((hτ.pow_const 4).inv.aestronglyMeasurable)
      apply hm.congr
      filter_upwards with x
      rfl
    apply ((hInt n).div_const (((2 : ℝ) ^ n) ^ 4)).mono' hmeas
    filter_upwards [ae_restrict_mem (μ := μ) (hS n)] with x hx
    change ‖D x / τ x ^ 4‖ ≤ D x / ((2 : ℝ) ^ n) ^ 4
    rw [Real.norm_of_nonneg (div_nonneg (hD x) (by positivity))]
    exact div_le_div_of_nonneg_left (hD x) (by positivity)
      (pow_le_pow_left₀ (by positivity) hx.1 4)
  have hbound (n : ℕ) :
      (∫ x in S n, ‖F x‖ ∂μ) ≤ (4 * C) * (1 / 4 : ℝ) ^ n := by
    have hM : (∫ x in S n, D x ∂μ) ≤ C * ((2 : ℝ) ^ (n + 1)) ^ 2 :=
      (setIntegral_mono_set (hcut _ (hR n)).1 (ae_of_all _ hD)
        (ae_of_all _ (hsub n))).trans (hcut _ (hR n)).2
    have hpoint : ∀ᵐ x ∂μ.restrict (S n),
        ‖F x‖ ≤ D x / ((2 : ℝ) ^ n) ^ 4 := by
      filter_upwards [ae_restrict_mem (μ := μ) (hS n)] with x hx
      change ‖D x / τ x ^ 4‖ ≤ _
      rw [Real.norm_of_nonneg (div_nonneg (hD x) (by positivity))]
      exact div_le_div_of_nonneg_left (hD x) (by positivity)
        (pow_le_pow_left₀ (by positivity) hx.1 4)
    calc
      _ ≤ ∫ x in S n, D x / ((2 : ℝ) ^ n) ^ 4 ∂μ :=
        integral_mono_ae (hF n).norm ((hInt n).div_const _) hpoint
      _ = (∫ x in S n, D x ∂μ) / ((2 : ℝ) ^ n) ^ 4 := integral_div _ _
      _ ≤ (C * ((2 : ℝ) ^ (n + 1)) ^ 2) / ((2 : ℝ) ^ n) ^ 4 :=
        div_le_div_of_nonneg_right hM (by positivity)
      _ = _ := by
        have hp : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
          rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
          norm_num
        rw [div_pow, one_pow, ← hp, pow_succ]
        field_simp
        ring
  have hgeom : Summable (fun n : ℕ => (4 * C) * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  have hsum : Summable (fun n : ℕ => ∫ x in S n, ‖F x‖ ∂μ) :=
    hgeom.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hbound
  have hcover : (⋃ n : ℕ, S n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (hτ₁ x) (by norm_num : (1 : ℝ) < 2)
    exact mem_iUnion.mpr ⟨n, hn, hn'.le⟩
  simpa only [hcover, integrableOn_univ] using
    integrableOn_iUnion_of_summable_integral_norm hF hsum

end
end ArtinMatthews
