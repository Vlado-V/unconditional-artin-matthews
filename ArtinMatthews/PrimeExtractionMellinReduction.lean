module

public import ArtinMatthews.PrimeExtractionRelevantMellin
public import ArtinMatthews.PrimeExtractionDyadicLogGrowth
public import ArtinMatthews.PrimeExtractionLogMomentDecay
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
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! Actual arithmetic prime extraction reduced, with every logarithmic
saving, to separated Mellin sums on the admissible dyadic boxes. -/

noncomputable section
namespace ArtinMatthews

open Filter MeasureTheory OAI.SevenEighths
open scoped BigOperators FourierTransform SchwartzMap ContDiff Asymptotics

theorem markedExtractionRelevantMellin_error_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    (γ : ℝ) {j : ℕ} (hj : 2 ≤ j) (A : ℝ) :
    (fun x => markedDirectTupleThetaSum e η χ G Φ T γ j x -
      markedExtractionRelevantMellin e η χ G Φ ha hsupp hΦ γ j (Real.log x) x) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  apply prime_extraction_all_log_moments_isLittleO
  intro k
  let M := ∫ t : ℝ, |t|^k * ‖(𝓕 (primeExtractionRealLogProfile Φ ha hsupp hΦ)) t‖
  let C := (2 / Real.log 2)^Fintype.card ι * CG * (2 : ℝ)^j
  have hM : 0 ≤ M := integral_nonneg (fun t =>
    mul_nonneg (pow_nonneg (abs_nonneg t) _) (norm_nonneg _))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨M*C*T*(1+2/Real.log 2)^2, ?_⟩
  filter_upwards [markedExtractionRelevantMellin_error e he η χ G hCG hG Φ ha hsupp hΦ γ hj k,
    primeExtractionDyadicFloorLogGrowth T hT, eventually_gt_atTop (1 : ℝ)] with x hE hN hx
  have hl : 0 < Real.log x := Real.log_pos hx
  calc
    _ ≤ (M / (Real.log x)^k) * C * (⌊T*x⌋₊ : ℝ) *
        (1+Real.log ((⌊T*x⌋₊ : ℝ)+1)/Real.log 2)^2 := hE _ hl
    _ = (M*C/(Real.log x)^k) * ((⌊T*x⌋₊ : ℝ) *
        (1+Real.log ((⌊T*x⌋₊ : ℝ)+1)/Real.log 2)^2) := by ring
    _ ≤ (M*C/(Real.log x)^k) * (T*(1+2/Real.log 2)^2*x*(Real.log x)^2) :=
      mul_le_mul_of_nonneg_left hN (div_nonneg (mul_nonneg hM hC) (pow_pos hl _).le)
    _ = _ := by ring

/-- The actual rough composite theta sum is now reduced to the actual
separated bilinear phase sums. No analytic cancellation is assumed here;
the remaining sums are displayed explicitly in RelevantMellin. -/
theorem markedActualCompositeThetaSum_relevant_mellin_reduction
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, 0 < e i)
    (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) {a T γ : ℝ} (ha : 0 < a) (hT : 0 ≤ T) (hγ : 0 < γ)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ) (A : ℝ) :
    (fun x => markedActualCompositeThetaSum e η χ G Φ T γ x -
      ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊,
        markedExtractionRelevantMellin e η χ G Φ ha hsupp hΦ γ j (Real.log x) x) =o[atTop]
          (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have hcompact : HasCompactSupport Φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have h₁ := markedActualCompositeThetaSum_direct_reduction
    e he η χ G hCG hG Φ hcompact hΦ hT hγ A
  have h₂ : (fun x => ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊,
      (markedDirectTupleThetaSum e η χ G Φ T γ j x -
        markedExtractionRelevantMellin e η χ G Φ ha hsupp hΦ γ j (Real.log x) x)) =o[atTop]
          (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
    apply (Asymptotics.IsLittleO.sum (fun j (hj : j ∈ Finset.Icc 2 ⌈2/γ⌉₊) =>
      markedExtractionRelevantMellin_error_isLittleO e he η χ G hCG hG Φ ha hT hsupp hΦ γ
        (Finset.mem_Icc.mp hj).1 A)).congr' _ Filter.EventuallyEq.rfl
    filter_upwards [] with x
    simp only [Finset.sum_apply]
  apply (h₁.add h₂).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [] with x
  simp only [Finset.sum_sub_distrib]
  ring

end ArtinMatthews
