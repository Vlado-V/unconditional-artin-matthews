module

public import ArtinMatthews.PrimeExtractionMellinProfile
public import ArtinMatthews.PrimeExtractionMellinTail
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Finite bilinear interchange and exact Mellin phase separation for the
actual smooth cutoff. The coefficient matrix may remain coupled. -/

noncomputable section
namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff

def primeExtractionBilinearPhaseSum (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ M, ∑ n ∈ N, A m n * primeExtractionMellinPhase t m * primeExtractionMellinPhase t n

def primeExtractionBilinearMass (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) : ℝ :=
  ∑ m ∈ M, ∑ n ∈ N, ‖A m n‖

theorem primeExtractionBilinearMass_nonneg (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) :
    0 ≤ primeExtractionBilinearMass M N A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem primeExtractionBilinearPhaseSum_norm_le (M N : Finset ℕ)
    (A : ℕ → ℕ → ℂ) (t : ℝ) :
    ‖primeExtractionBilinearPhaseSum M N A t‖ ≤ primeExtractionBilinearMass M N A := by
  unfold primeExtractionBilinearPhaseSum primeExtractionBilinearMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m _
  apply (norm_sum_le _ _).trans_eq
  simp only [norm_mul, primeExtractionMellinPhase_norm, mul_one]

theorem primeExtraction_bilinear_phase_identity (f : ℝ → ℂ)
    (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) {x : ℝ} (hx : 0 < x)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n) (t : ℝ) :
    (∑ m ∈ M, ∑ n ∈ N, A m n *
      (f t * primeExtractionMellinPhase t (((m*n : ℕ) : ℝ)/x))) =
      f t * primeExtractionMellinPhase (-t) x * primeExtractionBilinearPhaseSum M N A t := by
  classical
  unfold primeExtractionBilinearPhaseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.cast_mul, primeExtractionMellinPhase_mul_div t
    (by exact_mod_cast hM m hm) (by exact_mod_cast hN n hn) hx]
  ring

theorem primeExtraction_mellin_integrand_integrable (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    Integrable (fun t : ℝ => f t * primeExtractionMellinPhase t y) :=
  f.integrable.mul_bdd (primeExtractionMellinPhase_continuous y).aestronglyMeasurable
    (Eventually.of_forall (fun t => (primeExtractionMellinPhase_norm t y).le))

theorem primeExtraction_bilinear_integrable (f : SchwartzMap ℝ ℂ)
    (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) {x : ℝ} (hx : 0 < x)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n) :
    Integrable (fun t : ℝ => f t * primeExtractionMellinPhase (-t) x *
      primeExtractionBilinearPhaseSum M N A t) := by
  have hi : Integrable (fun t : ℝ => ∑ m ∈ M, ∑ n ∈ N,
      A m n * (f t * primeExtractionMellinPhase t (((m*n : ℕ) : ℝ)/x))) :=
    integrable_finsetSum M (fun m _ => integrable_finsetSum N (fun n _ =>
      (primeExtraction_mellin_integrand_integrable f _).const_mul (A m n)))
  exact hi.congr (Eventually.of_forall (primeExtraction_bilinear_phase_identity f M N A hx hM hN))

/-- Finite bilinear sums may be interchanged with the actual Mellin
integral on any frequency set, with integrability proved term by term. -/
theorem primeExtraction_bilinear_setIntegral (f : SchwartzMap ℝ ℂ)
    (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) (S : Set ℝ) {x : ℝ} (hx : 0 < x)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n) :
    (∑ m ∈ M, ∑ n ∈ N, A m n *
      (∫ t : ℝ in S, f t * primeExtractionMellinPhase t (((m*n : ℕ) : ℝ)/x))) =
      ∫ t : ℝ in S, f t * primeExtractionMellinPhase (-t) x *
        primeExtractionBilinearPhaseSum M N A t := by
  classical
  have hi (m n : ℕ) : IntegrableOn (fun t : ℝ => A m n *
      (f t * primeExtractionMellinPhase t (((m*n : ℕ) : ℝ)/x))) S :=
    ((primeExtraction_mellin_integrand_integrable f _).const_mul (A m n)).integrableOn
  calc
    _ = ∑ m ∈ M, ∑ n ∈ N, ∫ t : ℝ in S,
        A m n * (f t * primeExtractionMellinPhase t (((m*n : ℕ) : ℝ)/x)) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_const_mul]
    _ = ∫ t : ℝ in S, ∑ m ∈ M, ∑ n ∈ N,
        A m n * (f t * primeExtractionMellinPhase t (((m*n : ℕ) : ℝ)/x)) := by
      rw [integral_finsetSum M (fun m _ => integrable_finsetSum N (fun n _ => hi m n))]
      apply Finset.sum_congr rfl
      intro m _
      rw [integral_finsetSum N (fun n _ => hi m n)]
    _ = _ := integral_congr_ae
      (Eventually.of_forall (primeExtraction_bilinear_phase_identity f M N A hx hM hN))

/-- Exact separation for the constructed Schwartz logarithmic profile,
in the `exp(2π i t log y)` convention and Lebesgue measure `dt`. -/
theorem primeExtraction_bilinear_mellin (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ)
    (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) {x : ℝ} (hx : 0 < x)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n) :
    (∑ m ∈ M, ∑ n ∈ N, A m n * Φ (((m*n : ℕ) : ℝ)/x)) =
      ∫ t : ℝ, (𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t *
        primeExtractionMellinPhase (-t) x * primeExtractionBilinearPhaseSum M N A t := by
  classical
  let f : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)
  calc
    _ = ∑ m ∈ M, ∑ n ∈ N, A m n *
        (∫ t : ℝ in Set.univ, f t * primeExtractionMellinPhase t (((m*n : ℕ) : ℝ)/x)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      have hy : 0 < (((m*n : ℕ) : ℝ)/x) :=
        div_pos (by exact_mod_cast Nat.mul_pos (hM m hm) (hN n hn)) hx
      simp only [Measure.restrict_univ]
      rw [primeExtraction_mellin_inversion Φ ha hsupp hΦ hy]
    _ = _ := by
      simpa only [Measure.restrict_univ] using primeExtraction_bilinear_setIntegral f M N A
        Set.univ hx hM hN

end ArtinMatthews
