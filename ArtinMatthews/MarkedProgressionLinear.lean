module

public import ArtinMatthews.MarkedActualMomentProgressions
public import ArtinMatthews.MarkedProgressionFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Bounded, varying finite linear combinations of actual progression
estimates. Linearity and the triangle inequality apply to the original
finite sums, including signed coefficients and their evolving means. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Asymptotics Topology

theorem markedProgressionDiscrepancy_nonneg (H : ℕ → ℝ) (M : ℝ)
    (Φ : ℝ → ℝ) (T x : ℝ) (R : ℕ) :
    0 ≤ markedProgressionDiscrepancy H M Φ T x R :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The finite linear-combination inequality retains each actual absolute
coefficient. Neither the functions nor their proposed means need be positive. -/
theorem markedProgressionDiscrepancy_linear_le {ι : Type*} (J : Finset ι)
    (b M : ι → ℝ) (H : ι → ℕ → ℝ) (Φ : ℝ → ℝ) (T x : ℝ) (R : ℕ) :
    markedProgressionDiscrepancy (fun u => ∑ i ∈ J, b i * H i u)
      (∑ i ∈ J, b i * M i) Φ T x R ≤
        ∑ i ∈ J, |b i| * markedProgressionDiscrepancy (H i) (M i) Φ T x R := by
  exact marked_family_summed_error_le (Finset.Icc 1 R)
    (fun r => (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1)) J
    (fun u => Φ ((u : ℝ) / x)) b M H
    (fun r => (x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ))

/-- Arbitrary bounded evolving coefficients preserve a common little-o
progression estimate for a fixed finite family. -/
theorem markedProgressionDiscrepancy_linear_isLittleO {ι : Type*} (J : Finset ι)
    (b M : ℝ → ι → ℝ) (H : ℝ → ι → ℕ → ℝ) (Φ : ℝ → ℝ) (T : ℝ)
    (R : ℝ → ℕ) (g : ℝ → ℝ) (C : ℝ)
    (hb : ∀ᶠ x : ℝ in atTop, ∀ i ∈ J, |b x i| ≤ C)
    (herror : ∀ i ∈ J, (fun x : ℝ =>
      markedProgressionDiscrepancy (H x i) (M x i) Φ T x (R x)) =o[atTop] g) :
    (fun x : ℝ => markedProgressionDiscrepancy (fun u => ∑ i ∈ J, b x i * H x i u)
      (∑ i ∈ J, b x i * M x i) Φ T x (R x)) =o[atTop] g := by
  have hsum : (fun x : ℝ => ∑ i ∈ J,
      markedProgressionDiscrepancy (H x i) (M x i) Φ T x (R x)) =o[atTop] g := by
    apply (Asymptotics.IsLittleO.sum herror).congr' _ Filter.EventuallyEq.rfl
    filter_upwards [] with x
    simp only [Finset.sum_apply]
  have hbound : (fun x : ℝ => markedProgressionDiscrepancy
      (fun u => ∑ i ∈ J, b x i * H x i u) (∑ i ∈ J, b x i * M x i) Φ T x (R x)) =O[atTop]
      (fun x : ℝ => ∑ i ∈ J, markedProgressionDiscrepancy (H x i) (M x i) Φ T x (R x)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hb] with x hbx
    rw [Real.norm_of_nonneg (markedProgressionDiscrepancy_nonneg _ _ _ _ _ _),
      Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ =>
        markedProgressionDiscrepancy_nonneg (H x i) (M x i) Φ T x (R x)))]
    apply (markedProgressionDiscrepancy_linear_le J (b x) (M x) (H x) Φ T x (R x)).trans
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hbx i hi)
      (markedProgressionDiscrepancy_nonneg (H x i) (M x i) Φ T x (R x)))
  exact hbound.trans_isLittleO hsum

/-- The form used for the all-logarithmic marked progression estimates. -/
theorem markedProgressionDiscrepancy_linear_all_log {ι : Type*} (J : Finset ι)
    (b M : ℝ → ι → ℝ) (H : ℝ → ι → ℕ → ℝ) (Φ : ℝ → ℝ) (T c A C : ℝ)
    (hb : ∀ᶠ x : ℝ in atTop, ∀ i ∈ J, |b x i| ≤ C)
    (herror : ∀ i ∈ J, (fun x : ℝ =>
      markedProgressionDiscrepancy (H x i) (M x i) Φ T x ⌊x ^ c⌋₊) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A))) :
    (fun x : ℝ => markedProgressionDiscrepancy (fun u => ∑ i ∈ J, b x i * H x i u)
      (∑ i ∈ J, b x i * M x i) Φ T x ⌊x ^ c⌋₊) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) :=
  markedProgressionDiscrepancy_linear_isLittleO J b M H Φ T
    (fun x => ⌊x ^ c⌋₊) (fun x => x * (Real.log x) ^ (-A)) C hb herror

/-- The constant function has the actual progression estimate, obtained
from the empty marking array. Its mean is exactly one. -/
theorem markedProgressionDiscrepancy_one_all_log (c A : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (Φ : ℝ → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => markedProgressionDiscrepancy (fun _ => 1) 1 Φ T x ⌊x ^ c⌋₊) =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have h := marked_actual_first_moment_progressions (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) c A hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0
  have hw (P : Fin 0 → Finset ℕ) (V : Fin 0 → ℝ) :
      divisorWeight ∅ P V = fun _ => 1 := by
    funext u
    simp [divisorWeight]
  simpa only [hw, independentArrayMean_eq, Finset.univ_eq_empty, Finset.prod_empty] using h

end ArtinMatthews
