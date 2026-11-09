module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Centered Abel summation retains the literal continuous main term. -/
namespace ArtinMatthews
open Finset MeasureTheory
noncomputable section

theorem marked_centered_abel_bound (c : ℕ → ℂ) (m : ℂ) (φ φ' : ℝ → ℂ)
    {a b D M N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.Icc a b))
    (hvalue : ∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N)
    (hpartial : ∀ t ∈ Set.Icc a b,
      ‖(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - m * (t : ℂ)‖ ≤ D) :
    ‖(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * c n) - m * (∫ t in a..b, φ t)‖ ≤
      D * (2 * M + N * (b - a)) := by
  let E := fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) - m * (t : ℂ)
  have hdi : IntegrableOn (deriv φ) (Set.Icc a b) :=
    (hφ'.congr (fun t ht => (hφ t ht).deriv)).integrableOn_Icc
  have hi : IntervalIntegrable φ' volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hφ'.integrableOn_Icc
  have hsi : IntervalIntegrable
      (fun t : ℝ => φ' t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_mul_sum_Icc c ha hφ'.integrableOn_Icc)
  have hmi : IntervalIntegrable (fun t : ℝ => φ' t * (m * (t : ℂ))) volume a b :=
    hi.mul_continuousOn (continuous_const.mul Complex.continuous_ofReal).continuousOn
  have hs := sum_mul_eq_sub_sub_integral_mul c ha hab
    (fun t ht => (hφ t ht).differentiableAt) hdi
  rw [← intervalIntegral.integral_of_le hab] at hs
  have hs' : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * c n) =
      φ b * (∑ n ∈ Icc 0 ⌊b⌋₊, c n) - φ a * (∑ n ∈ Icc 0 ⌊a⌋₊, c n) -
        ∫ t in a..b, φ' t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n := by
    rw [hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [(hφ t (Set.uIcc_of_le hab ▸ ht)).deriv]
  have hm := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := φ) (u' := φ') (v := fun t : ℝ => m * (t : ℂ)) (v' := fun _ => m)
    (fun t ht => hφ t (Set.uIcc_of_le hab ▸ ht))
    (fun t _ => by simpa using ((hasDerivAt_id t).ofReal_comp).const_mul m)
    hi (intervalIntegrable_const)
  rw [intervalIntegral.integral_mul_const] at hm
  have heq : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * c n) - m * (∫ t in a..b, φ t) =
      φ b * E b - φ a * E a - ∫ t in a..b, φ' t * E t := by
    have hei : (∫ t in a..b, φ' t * E t) =
        (∫ t in a..b, φ' t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) -
        ∫ t in a..b, φ' t * (m * (t : ℂ)) := by
      simp only [E, mul_sub]
      exact intervalIntegral.integral_sub hsi hmi
    rw [hs', hei, mul_comm m, hm]
    dsimp only [E]
    ring
  have hint : ‖∫ t in a..b, φ' t * E t‖ ≤ N * D * (b - a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => φ' t * E t) (C := N * D)
      (fun t ht => by
        have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc ht
        rw [norm_mul]
        exact mul_le_mul (hderiv t ht') (hpartial t ht') (norm_nonneg _) hN)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hend (t : ℝ) (ht : t ∈ Set.Icc a b) : ‖φ t * E t‖ ≤ M * D := by
    rw [norm_mul]
    exact mul_le_mul (hvalue t ht) (hpartial t ht) (norm_nonneg _) hM
  rw [heq]
  calc
    _ ≤ ‖φ b * E b‖ + ‖φ a * E a‖ + ‖∫ t in a..b, φ' t * E t‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ M * D + M * D + N * D * (b - a) :=
      add_le_add (add_le_add (hend b ⟨hab, le_rfl⟩) (hend a ⟨le_rfl, hab⟩)) hint
    _ = _ := by ring

end
end ArtinMatthews
