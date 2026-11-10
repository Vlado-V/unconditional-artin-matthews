module

public import ArtinMatthews.PrimeExtractionCompositeError
public import ArtinMatthews.PrimeExtractionCutoffShift
public import ArtinMatthews.PrimeExtractionBilinearExpansion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual composite sum reduced to normalized tuple sums with the
unshifted smooth cutoff, ready for exact Mellin separation. -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators Asymptotics ContDiff

noncomputable def markedDirectTupleThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊T * x⌋₊,
    ((Φ ((n : ℝ) / x) : ℂ) * (literalMarkedArrayWeight e x (n - 1) : ℂ) * G x (n - 1)) *
      (roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n (x ^ γ) / j.factorial)

theorem markedExpandedCompositeThetaSum_sub_direct_eq {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) :
    markedExpandedCompositeThetaSum e η χ G Φ T γ x -
      (∑ j ∈ Finset.Icc 2 ⌈2 / γ⌉₊, markedDirectTupleThetaSum e η χ G Φ T γ j x) =
        ∑ j ∈ Finset.Icc 2 ⌈2 / γ⌉₊, markedTupleCutoffShift e η χ G Φ T γ j x := by
  classical
  unfold markedExpandedCompositeThetaSum roughCompositeCoefficient
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold markedDirectTupleThetaSum markedTupleCutoffShift
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold markedExtractionWeight
  push_cast
  ring

theorem markedExpandedCompositeThetaSum_sub_direct_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hsupp : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ)
    {T : ℝ} (hT : 0 ≤ T) (γ : ℝ) (A : ℝ) :
    (fun x => markedExpandedCompositeThetaSum e η χ G Φ T γ x -
      ∑ j ∈ Finset.Icc 2 ⌈2 / γ⌉₊, markedDirectTupleThetaSum e η χ G Φ T γ j x) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have hs : (fun x => ∑ j ∈ Finset.Icc 2 ⌈2 / γ⌉₊,
      markedTupleCutoffShift e η χ G Φ T γ j x) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
    apply (Asymptotics.IsLittleO.sum
      (fun j (_hj : j ∈ Finset.Icc 2 ⌈2 / γ⌉₊) =>
        markedTupleCutoffShift_isLittleO e he η χ G hCG hG Φ hsupp hΦ hT γ j A)).congr'
      _ Filter.EventuallyEq.rfl
    filter_upwards [] with x
    simp only [Finset.sum_apply]
  apply hs.congr' _ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun x => (markedExpandedCompositeThetaSum_sub_direct_eq
    e η χ G Φ T γ x).symm)

/-- Complete arithmetic and cutoff reduction for the actual rough composite
sum. The remaining work is cancellation of the displayed direct tuple sums. -/
theorem markedActualCompositeThetaSum_direct_reduction {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hsupp : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ)
    {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) (A : ℝ) :
    (fun x => markedActualCompositeThetaSum e η χ G Φ T γ x -
      ∑ j ∈ Finset.Icc 2 ⌈2 / γ⌉₊, markedDirectTupleThetaSum e η χ G Φ T γ j x) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have h₁ := markedActualCompositeThetaSum_sub_expansion_isLittleO
    e he η χ G hCG hG Φ hΦ.continuous hT hγ A
  have h₂ := markedExpandedCompositeThetaSum_sub_direct_isLittleO
    e he η χ G hCG hG Φ hsupp hΦ hT γ A
  apply (h₁.add h₂).congr' _ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun x => by ring)

/-- Exact hyperbola form of each direct tuple sum, including its factorial
normalization and the predecessor core evaluated at m*v-1. -/
theorem markedDirectTupleThetaSum_bilinear {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    markedDirectTupleThetaSum e η χ G Φ T γ j x =
      (∑ mn ∈ (Finset.Ioc 0 ⌊T * x⌋₊ ×ˢ Finset.Ioc 0 ⌊T * x⌋₊).filter
          (fun mn => mn.1 * mn.2 ≤ ⌊T * x⌋₊),
        (Φ (((mn.1 * mn.2 : ℕ) : ℝ) / x) : ℂ) *
          (literalMarkedArrayWeight e x (mn.1 * mn.2 - 1) : ℂ) * G x (mn.1 * mn.2 - 1) *
          roughPrimeFirstCoefficient (fun p => idealThetaCoeff η p * χ p) (x ^ γ) mn.1 *
          roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) (j - 1) mn.2 (x ^ γ)) /
        j.factorial := by
  let a (p : ℕ) := idealThetaCoeff η p * χ p
  let w (n : ℕ) := (Φ ((n : ℝ) / x) : ℂ) * (literalMarkedArrayWeight e x (n - 1) : ℂ) * G x (n - 1)
  have h := roughPrimeTupleCoefficient_bilinear_expansion a (j - 1) ⌊T * x⌋₊ (x ^ γ) w
  rw [Nat.sub_add_cancel hj] at h
  unfold markedDirectTupleThetaSum
  simp only [← mul_div_assoc, ← Finset.sum_div]
  exact congrArg (fun z : ℂ => z / j.factorial) h

end ArtinMatthews
