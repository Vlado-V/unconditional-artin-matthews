module

public import ArtinMatthews.PrimeExtractionBilinearCoefficient
public import ArtinMatthews.PrimeExtractionDirectReduction
public import ArtinMatthews.PrimeExtractionDyadicSupport
public import ArtinMatthews.PrimeExtractionMellinBilinear
public import ArtinMatthews.PrimeExtractionDyadicMass
public import ArtinMatthews.PrimeExtractionMellinBilinearTail
public import ArtinMatthews.PrimeExtractionRectangle
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Mellin separation on the retained actual dyadic boxes. The error uses
the sum of their masses, of order N log² N, rather than the full rectangle. -/

noncomputable section
namespace ArtinMatthews

open Filter MeasureTheory OAI.SevenEighths
open scoped BigOperators FourierTransform SchwartzMap ContDiff

theorem primeExtraction_complexCutoff_support (Φ : ℝ → ℝ) {a b : ℝ}
    (hsupp : Function.support Φ ⊆ Set.Icc a b) :
    Function.support (fun y => (Φ y : ℂ)) ⊆ Set.Icc a b := by
  intro y hy
  apply hsupp
  intro heq
  exact hy (by simp only [heq, Complex.ofReal_zero])

def primeExtractionRealLogProfile (Φ : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ) :
    SchwartzMap ℝ ℂ :=
  primeExtractionLogProfile (fun y => (Φ y : ℂ)) ha
    (primeExtraction_complexCutoff_support Φ hsupp) (Complex.ofRealCLM.contDiff.comp hΦ)

def markedExtractionDyadicMellin {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a T : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    (γ : ℝ) (j : ℕ) (H x : ℝ) : ℂ :=
  ∑ kl ∈ primeExtractionDyadicActive ⌊T * x⌋₊,
    ∫ t : ℝ in Set.Icc (-H) H,
      (𝓕 (primeExtractionRealLogProfile Φ ha hsupp hΦ)) t *
        primeExtractionMellinPhase (-t) x *
          primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock ⌊T * x⌋₊ kl.1)
            (primeExtractionDyadicBlock ⌊T * x⌋₊ kl.2)
            (markedExtractionBilinearCoefficient e η χ G γ j x) t

theorem markedDirectTupleThetaSum_dyadic {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a T x : ℝ}
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hx : 0 < x)
    (γ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    markedDirectTupleThetaSum e η χ G Φ T γ j x =
      ∑ kl ∈ primeExtractionDyadicActive ⌊T * x⌋₊,
        ∑ m ∈ primeExtractionDyadicBlock ⌊T * x⌋₊ kl.1,
          ∑ n ∈ primeExtractionDyadicBlock ⌊T * x⌋₊ kl.2,
            markedExtractionBilinearCoefficient e η χ G γ j x m n *
              (Φ (((m * n : ℕ) : ℝ) / x) : ℂ) := by
  rw [markedDirectTupleThetaSum_rectangle e η χ G Φ hsupp hx γ hj]
  apply prime_extraction_dyadic_supported_sum
  intro m n hmn
  rw [prime_extraction_cutoff_zero_of_product_gt Φ hsupp hx hmn]
  simp

/-- Actual boxwise Mellin truncation with all arithmetic coefficient
bounds discharged. The fixed Fourier moment controls every height H>0. -/
theorem markedExtractionDyadicMellin_error {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    (γ : ℝ) {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ H : ℝ, 0 < H →
      ‖markedDirectTupleThetaSum e η χ G Φ T γ j x -
        markedExtractionDyadicMellin e η χ G Φ ha hsupp hΦ γ j H x‖ ≤
      ((∫ t : ℝ, |t| ^ k * ‖(𝓕 (primeExtractionRealLogProfile Φ ha hsupp hΦ)) t‖) / H ^ k) *
        ((2 / Real.log 2) ^ Fintype.card ι * CG * (2 : ℝ) ^ j) * (⌊T*x⌋₊ : ℝ) *
          (1 + Real.log ((⌊T*x⌋₊ : ℝ) + 1) / Real.log 2) ^ 2 := by
  let C := (2 / Real.log 2) ^ Fintype.card ι * CG * (2 : ℝ) ^ j
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [markedExtractionBilinearCoefficient_bound e he η χ G hCG hG γ hj,
    eventually_gt_atTop (0 : ℝ)] with x hA hx
  intro H hH
  let f : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionRealLogProfile Φ ha hsupp hΦ)
  let D := (∫ t : ℝ, |t| ^ k * ‖f t‖) / H ^ k
  have hD : 0 ≤ D := div_nonneg
    (integral_nonneg (fun t => mul_nonneg (pow_nonneg (abs_nonneg t) _) (norm_nonneg _)))
    (pow_pos hH _).le
  have hpos (l : ℕ) : ∀ n ∈ primeExtractionDyadicBlock ⌊T*x⌋₊ l, 0 < n := by
    intro n hn
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  rw [markedDirectTupleThetaSum_dyadic e η χ G Φ hsupp hx γ hj]
  unfold markedExtractionDyadicMellin
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ kl ∈ primeExtractionDyadicActive ⌊T*x⌋₊,
        ‖(∑ m ∈ primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1,
          ∑ n ∈ primeExtractionDyadicBlock ⌊T*x⌋₊ kl.2,
            markedExtractionBilinearCoefficient e η χ G γ j x m n * (Φ (((m*n : ℕ) : ℝ)/x) : ℂ)) -
          ∫ t : ℝ in Set.Icc (-H) H, f t * primeExtractionMellinPhase (-t) x *
            primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1)
              (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.2)
              (markedExtractionBilinearCoefficient e η χ G γ j x) t‖ := norm_sum_le _ _
    _ ≤ ∑ kl ∈ primeExtractionDyadicActive ⌊T*x⌋₊, D *
        primeExtractionBilinearMass (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1)
          (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.2)
          (markedExtractionBilinearCoefficient e η χ G γ j x) := by
      apply Finset.sum_le_sum
      intro kl _
      exact primeExtraction_bilinear_mellin_truncation (fun y => (Φ y : ℂ)) ha
        (primeExtraction_complexCutoff_support Φ hsupp) (Complex.ofRealCLM.contDiff.comp hΦ)
        _ _ _ k hH hx (hpos _) (hpos _)
    _ = D * ∑ kl ∈ primeExtractionDyadicActive ⌊T*x⌋₊,
        primeExtractionBilinearMass (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1)
          (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.2)
          (markedExtractionBilinearCoefficient e η χ G γ j x) := (Finset.mul_sum ..).symm
    _ ≤ D * (C * (⌊T*x⌋₊ : ℝ) * (1 + Real.log ((⌊T*x⌋₊ : ℝ)+1)/Real.log 2)^2) :=
      mul_le_mul_of_nonneg_left (primeExtractionDyadicTotal_mass_le _ _ hC
        (fun _ _ m _ n _ => hA m n)) hD
    _ = _ := by dsimp [C, D, f]; ring

end ArtinMatthews
