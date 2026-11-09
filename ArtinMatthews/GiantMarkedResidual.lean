module

public import ArtinMatthews.GiantMarkedInsertion
public import ArtinMatthews.MarkedProgressionFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Actual progression bounds after summing a disjoint finite giant-prime
window. The exact reciprocal window mass stays in every model/tail error. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

noncomputable def giantWindowDivisorCount (G : Finset ℕ) (u : ℕ) : ℝ :=
  ∑ ell ∈ G, if ell ∣ u then (1 : ℝ) else 0

theorem giant_marked_single_residual (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    {ell : ℕ} (hell : ell.Prime) (hellP : ell ∉ P)
    (hθell : 0 ≤ θ ell ∧ θ ell ≤ 1)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ))
    (hellmin : y ≤ ell) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
        Φ ((u : ℝ) / x) * ((if ell ∣ u then (1 : ℝ) else 0) *
          markedWeightedResidual P S θ u)) -
        ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) *
          ((1 / (ell : ℝ)) * markedWeightedModel P S θ)|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) +
      ((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (1 / ((ell : ℝ) * (∏ p ∈ S, p : ℕ))) *
        ((((S.card + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)) := by
  classical
  have hS' : ell ∉ S := fun hs => hellP (hS hs)
  have hg := marked_weighted_residual_rescaled_quantitative (insert ell P) (insert ell S)
    (fun p hp => (Finset.mem_insert.mp hp).elim (fun h => h ▸ hell) (hP p))
    (Finset.insert_subset_insert ell hS) θ
    (fun p hp => (Finset.mem_insert.mp hp).elim (fun h => h ▸ hθell) (hθ p)) m R
    hy (fun p hp => (Finset.mem_insert.mp hp).elim (fun h => h ▸ hellmin) (hmin p)) hV
    (by simpa only [marked_insert_selected_sdiff P S hellP] using hmass)
    Φ hx hT hΦ hderiv hΦT hΦ0
  simpa only [markedWeightedResidual_insert_selected P S hS θ hellP,
    markedWeightedModel_insert_selected P S hS θ hellP,
    marked_insert_selected_sdiff P S hellP, Finset.card_insert_of_notMem hS',
    Finset.prod_insert hS', Nat.cast_mul] using hg

/-- A genuine finite arithmetic estimate; no distribution error is assumed. -/
theorem giant_marked_window_residual (G P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    (hG : ∀ ell ∈ G, ell.Prime) (hdis : Disjoint G P)
    (hθG : ∀ ell ∈ G, 0 ≤ θ ell ∧ θ ell ≤ 1)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ))
    (hGmin : ∀ ell ∈ G, y ≤ (ell : ℝ)) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
        Φ ((u : ℝ) / x) * (giantWindowDivisorCount G u * markedWeightedResidual P S θ u)) -
        ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) *
          ((∑ ell ∈ G, 1 / (ell : ℝ)) * markedWeightedModel P S θ)|) ≤
      ((R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1))) * G.card +
      (((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (1 / (∏ p ∈ S, p : ℕ)) *
        ((((S.card + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) *
        (∑ ell ∈ G, 1 / (ell : ℝ)) := by
  classical
  have hterm (ell : ℕ) (hell : ell ∈ G) := giant_marked_single_residual P S hP hS θ hθ m R
    (hG ell hell) (fun hp => Finset.disjoint_left.mp hdis hell hp) (hθG ell hell)
    hy hmin (hGmin ell hell) hV hmass Φ hx hT hΦ hderiv hΦT hΦ0
  have hfam := marked_family_summed_error_of_bounds (Finset.Icc 1 R)
    (fun r => (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1)) G
    (fun u => Φ ((u : ℝ) / x)) (fun _ => (1 : ℝ))
    (fun ell => (1 / (ell : ℝ)) * markedWeightedModel P S θ)
    (fun ell u => (if ell ∣ u then (1 : ℝ) else 0) * markedWeightedResidual P S θ u)
    (fun r => (x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) (fun ell => (ell : ℝ))
    ((R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
      (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
        (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)))
    (((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
      (1 / (∏ p ∈ S, p : ℕ)) *
      ((((S.card + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
        2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)))
    (by intro ell hell; convert hterm ell hell using 1; ring)
  simpa only [one_mul, abs_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.sum_mul, giantWindowDivisorCount] using hfam

end ArtinMatthews
