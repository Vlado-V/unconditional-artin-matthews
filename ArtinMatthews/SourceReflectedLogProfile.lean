module

public import ArtinMatthews.SourceReflectedAngularFourier
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SourceReflectedFourierL1
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Mellin.LogProfiles


set_option backward.privateInPublic true
@[expose] public section

/-! The literal logarithmic cutoff of a reflected profile, with the two
ends retained in its Fourier L¹ cost. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set
open scoped FourierTransform SchwartzMap BigOperators ContDiff
noncomputable section

private def reflectedWindow : ℝ := 2 * Real.log 2
private def reflectedSupport : ℝ := reflectedWindow + 1

private theorem reflectedWindow_nonneg : 0 ≤ reflectedWindow :=
  mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))

private theorem reflectedSupport_nonneg : 0 ≤ reflectedSupport :=
  add_nonneg reflectedWindow_nonneg zero_le_one

private theorem reflectedCutoff_exists : ∃ ρ : ℝ → ℂ, HasCompactSupport ρ ∧ ContDiff ℝ ∞ ρ ∧
    (∀ s, |s| ≤ reflectedWindow → ρ s = 1) ∧ tsupport ρ ⊆ Icc (-reflectedSupport) reflectedSupport ∧
    ρ 0 = 1 :=
  OAI.FourierBridge.exists_complex_smooth_cutoff reflectedWindow reflectedWindow_nonneg

/-- A single smooth cutoff which equals one on all source dyad log ratios. -/
def sourceReflectedDyadCutoff : ℝ → ℂ := reflectedCutoff_exists.choose

private theorem reflectedCutoff_compact : HasCompactSupport sourceReflectedDyadCutoff :=
  reflectedCutoff_exists.choose_spec.1

private theorem reflectedCutoff_smooth : ContDiff ℝ ∞ sourceReflectedDyadCutoff :=
  reflectedCutoff_exists.choose_spec.2.1

private theorem reflectedCutoff_support :
    tsupport sourceReflectedDyadCutoff ⊆ Icc (-reflectedSupport) reflectedSupport :=
  reflectedCutoff_exists.choose_spec.2.2.2.1

theorem sourceReflectedDyadCutoff_one (x : ℝ) (hx : x ∈ Icc (-(2 * Real.log 2)) (Real.log 2)) :
    sourceReflectedDyadCutoff x = 1 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  apply reflectedCutoff_exists.choose_spec.2.2.1
  change |x| ≤ 2 * Real.log 2
  exact abs_le.mpr ⟨hx.1, hx.2.trans (by linarith)⟩

/-- The actual compact log profile ρ(x) Φ(u exp(x)). -/
def sourceReflectedLogProfile (Φ : ℝ → ℂ) (hΦ : ContDiff ℝ ∞ (fun s : ℝ => Φ (Real.exp s)))
    (u : ℝ) : 𝓢(ℝ, ℂ) := by
  let f (x : ℝ) := sourceReflectedDyadCutoff x * Φ (Real.exp (x + Real.log u))
  have hc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((Function.support_mul_subset_left _ _).trans ((subset_tsupport _).trans reflectedCutoff_support))
  have hs : ContDiff ℝ ∞ f := reflectedCutoff_smooth.mul
    (hΦ.comp (contDiff_id.add contDiff_const))
  exact hc.toSchwartzMap hs

theorem sourceReflectedLogProfile_apply (Φ : ℝ → ℂ)
    (hΦ : ContDiff ℝ ∞ (fun s : ℝ => Φ (Real.exp s))) {u : ℝ} (hu : 0 < u) (x : ℝ) :
    sourceReflectedLogProfile Φ hΦ u x = sourceReflectedDyadCutoff x * Φ (u * Real.exp x) := by
  change sourceReflectedDyadCutoff x * Φ (Real.exp (x + Real.log u)) = _
  rw [Real.exp_add, Real.exp_log hu, mul_comm (Real.exp x)]

private theorem reflectedLogProfile_support (Φ : ℝ → ℂ)
    (hΦ : ContDiff ℝ ∞ (fun s : ℝ => Φ (Real.exp s))) (u : ℝ) :
    tsupport (sourceReflectedLogProfile Φ hΦ u) ⊆ Icc (-reflectedSupport) reflectedSupport :=
  tsupport_mul_subset_left.trans reflectedCutoff_support

private def reflectedCutoffCost : ℝ := ∑ i ∈ Finset.range 3,
  (SchwartzMap.seminorm ℝ 0 i) (reflectedCutoff_compact.toSchwartzMap reflectedCutoff_smooth)

private theorem reflectedCutoffCost_nonneg : 0 ≤ reflectedCutoffCost :=
  Finset.sum_nonneg fun _ _ => apply_nonneg _ _

private theorem reflectedCutoff_derivative (i : ℕ) (hi : i ≤ 2) (x : ℝ) :
    ‖iteratedFDeriv ℝ i sourceReflectedDyadCutoff x‖ ≤ reflectedCutoffCost :=
  (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
    (reflectedCutoff_compact.toSchwartzMap reflectedCutoff_smooth) i x).trans
      (Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega)))

private def reflectedShiftCost (α A : ℝ) :=
  max (Real.exp (α * reflectedSupport)) (Real.exp (A * reflectedSupport))

private theorem reflectedShiftCost_nonneg (α A : ℝ) : 0 ≤ reflectedShiftCost α A :=
  (Real.exp_pos _).le.trans (le_max_left _ _)

private theorem reflected_exponential_shift (α A : ℝ) (hα : 0 ≤ α) (hA : 0 ≤ A)
    {u : ℝ} (hu : 0 < u) (x : ℝ) (hx : x ∈ Icc (-reflectedSupport) reflectedSupport) :
    min (Real.exp (α * (x + Real.log u))) (Real.exp (-A * (x + Real.log u))) ≤
      reflectedShiftCost α A * min (u ^ α) (u ^ (-A)) := by
  rw [mul_min_of_nonneg _ _ (reflectedShiftCost_nonneg α A)]
  apply min_le_min
  · rw [mul_add, Real.exp_add, mul_comm α (Real.log u), ← Real.rpow_def_of_pos hu]
    exact mul_le_mul_of_nonneg_right
      ((Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hα)).trans (le_max_left _ _))
      (Real.rpow_nonneg hu.le _)
  · rw [mul_add, Real.exp_add, mul_comm (-A) (Real.log u), ← Real.rpow_def_of_pos hu]
    have hneg : -x ≤ reflectedSupport := by linarith [hx.1]
    have h := mul_le_mul_of_nonneg_left hneg hA
    rw [mul_neg, ← neg_mul] at h
    exact mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr h).trans (le_max_right _ _))
      (Real.rpow_nonneg hu.le _)

private theorem reflectedLogProfile_derivative (Φ : ℝ → ℂ)
    (hΦ : ContDiff ℝ ∞ (fun s : ℝ => Φ (Real.exp s)))
    {α A M : ℝ} (hα : 0 ≤ α) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hderiv : ∀ i ≤ 2, ∀ s : ℝ, ‖iteratedFDeriv ℝ i (fun t : ℝ => Φ (Real.exp t)) s‖ ≤
      M * min (Real.exp (α * s)) (Real.exp (-A * s)))
    {u : ℝ} (hu : 0 < u) (i : ℕ) (hi : i ≤ 2) (x : ℝ)
    (hx : x ∈ Icc (-reflectedSupport) reflectedSupport) :
    ‖iteratedFDeriv ℝ i (sourceReflectedLogProfile Φ hΦ u) x‖ ≤
      (4 * reflectedCutoffCost * (M * reflectedShiftCost α A)) * min (u ^ α) (u ^ (-A)) := by
  let Q := min (u ^ α) (u ^ (-A))
  have hQ : 0 ≤ Q := le_min (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hu.le _)
  let H (x : ℝ) := Φ (Real.exp (x + Real.log u))
  have hH : ContDiff ℝ ∞ H := hΦ.comp (contDiff_id.add contDiff_const)
  have hD (n : ℕ) (hn : n ≤ 2) : ‖iteratedFDeriv ℝ n H x‖ ≤ (M * reflectedShiftCost α A) * Q := by
    change ‖iteratedFDeriv ℝ n (fun z : ℝ => Φ (Real.exp (z + Real.log u))) x‖ ≤ _
    rw [iteratedFDeriv_comp_add_right (f := fun t : ℝ => Φ (Real.exp t))]
    exact (hderiv n hn (x + Real.log u)).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (reflected_exponential_shift α A hα hA hu x hx) hM)
  change ‖iteratedFDeriv ℝ i (fun x => sourceReflectedDyadCutoff x * H x) x‖ ≤ _
  apply (norm_iteratedFDeriv_mul_le reflectedCutoff_smooth hH x (n := i) (by simp)).trans
  let B := reflectedCutoffCost * ((M * reflectedShiftCost α A) * Q)
  have hB : 0 ≤ B := mul_nonneg reflectedCutoffCost_nonneg
    (mul_nonneg (mul_nonneg hM (reflectedShiftCost_nonneg α A)) hQ)
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hj2 : j ≤ 2 := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hi
      have hsub : i - j ≤ 2 := (Nat.sub_le i j).trans hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (reflectedCutoff_derivative j hj2 x) (hD (i - j) hsub) (norm_nonneg _)
          reflectedCutoffCost_nonneg) (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ i * B := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose i
    _ ≤ 4 * B := mul_le_mul_of_nonneg_right
      ((pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hi).trans_eq (by norm_num)) hB
    _ = _ := by dsimp only [B, Q]; ring

/-- Smooth source log derivatives through order two yield the actual
angular Fourier inversion on the source dyad, at a uniform two-ended
L¹ cost. The coefficient is the Fourier transform of the literal cutoff. -/
theorem sourceReflectedLogFourier_exists {α A M : ℝ} (hα : 0 ≤ α) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : ℝ → ℂ)
      (hΦ : ContDiff ℝ ∞ (fun s : ℝ => Φ (Real.exp s))),
      (∀ i ≤ 2, ∀ s : ℝ, ‖iteratedFDeriv ℝ i (fun t : ℝ => Φ (Real.exp t)) s‖ ≤
        M * min (Real.exp (α * s)) (Real.exp (-A * s))) →
      ∀ u : ℝ, 0 < u →
      let g := sourceReflectedFourierCoefficient (sourceReflectedLogProfile Φ hΦ u)
      Integrable g ∧
        (∀ x ∈ Icc (-(2 * Real.log 2)) (Real.log 2),
          Φ (u * Real.exp x) = ∫ τ : ℝ, g τ * sourceReflectedFourierPhase τ x) ∧
        (∫ τ : ℝ, ‖g τ‖) ≤ C * min (u ^ α) (u ^ (-A)) := by
  let B := 4 * reflectedCutoffCost * (M * reflectedShiftCost α A)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) reflectedCutoffCost_nonneg)
    (mul_nonneg hM (reflectedShiftCost_nonneg α A))
  refine ⟨13 * Real.pi * ((2 * reflectedSupport) * B),
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (mul_nonneg (mul_nonneg (by norm_num) reflectedSupport_nonneg) hB), ?_⟩
  intro Φ hΦ hd u hu
  let f := sourceReflectedLogProfile Φ hΦ u
  refine ⟨sourceReflectedFourierCoefficient_integrable f, ?_, ?_⟩
  · intro x hx
    have he : f x = Φ (u * Real.exp x) := by
      rw [show f = sourceReflectedLogProfile Φ hΦ u from rfl, sourceReflectedLogProfile_apply Φ hΦ hu,
        sourceReflectedDyadCutoff_one x hx, one_mul]
    exact he.symm.trans (sourceReflectedFourierCoefficient_inverse f x)
  · have h := sourceReflectedFourierCoefficient_L1_of_compact f reflectedSupport_nonneg
      (reflectedLogProfile_support Φ hΦ u)
      (fun i hi x hx => reflectedLogProfile_derivative Φ hΦ hα hA hM hd hu i hi x hx)
    simpa only [B, mul_assoc] using h

end
end ArtinMatthews.SourceReflection
