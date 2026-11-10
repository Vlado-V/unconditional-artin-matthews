module

public import ArtinMatthews.PrimeExtractionBilinearCoefficient
public import ArtinMatthews.PrimeExtractionMellinBilinear
public import ArtinMatthews.PrimeExtractionRoughSupport
public import ArtinMatthews.PrimeExtractionTupleBounds
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal separated coefficients to which the marked bilinear criterion
applies. The Mellin normalization is exp(2*pi*i*t*log n). -/

noncomputable section
namespace ArtinMatthews

open OAI.SevenEighths
open scoped BigOperators

def primeExtractionFirstPhaseCoefficient (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (z t : ℝ) (m : ℕ) : ℂ :=
  roughPrimeFirstCoefficient (fun p => idealThetaCoeff η p * χ p) z m *
    primeExtractionMellinPhase t m

def primeExtractionSecondPhaseCoefficient (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (j : ℕ) (z t : ℝ) (n : ℕ) : ℂ :=
  (roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) (j-1) n z / j.factorial) *
    primeExtractionMellinPhase t n

theorem primeExtractionFirstPhaseCoefficient_norm_le (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (z t : ℝ) (m : ℕ) :
    ‖primeExtractionFirstPhaseCoefficient η χ z t m‖ ≤ 2 := by
  simpa only [primeExtractionFirstPhaseCoefficient, norm_mul,
    primeExtractionMellinPhase_norm, mul_one] using roughThetaFirstCoefficient_norm_le η χ z m

theorem primeExtractionSecondPhaseCoefficient_norm_le (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (j : ℕ) (z t : ℝ) (n : ℕ) :
    ‖primeExtractionSecondPhaseCoefficient η χ j z t n‖ ≤ (2 : ℝ)^(j-1) := by
  simpa only [primeExtractionSecondPhaseCoefficient, norm_mul,
    primeExtractionMellinPhase_norm, mul_one] using
      roughThetaTupleCoefficient_div_larger_factorial_norm_le η χ j n z

theorem primeExtractionFirstPhaseCoefficient_support (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) {z t : ℝ} {m : ℕ}
    (hm : primeExtractionFirstPhaseCoefficient η χ z t m ≠ 0) :
    m.Prime ∧ z < (m : ℝ) ∧ MarkedRoughAbove z m := by
  have hp := roughPrimeFirstCoefficient_support _ (mul_ne_zero_iff.mp hm).1
  refine ⟨hp.1, hp.2, ?_⟩
  intro p hprime hpd
  have hpm : p = m := (Nat.dvd_prime hp.1).mp hpd |>.resolve_left hprime.ne_one
  simpa only [hpm] using hp.2

theorem primeExtractionSecondPhaseCoefficient_support (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (j : ℕ) {z t : ℝ} {n : ℕ}
    (hn : primeExtractionSecondPhaseCoefficient η χ j z t n ≠ 0) :
    n ≠ 0 ∧ MarkedRoughAbove z n ∧ n.primeFactorsList.length = j-1 :=
  roughPrimeTupleCoefficient_support _ _ _ _
    (div_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1

theorem markedExtractionBilinearPhaseSum_separated {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (γ : ℝ) (j : ℕ) (x t : ℝ) (M N : Finset ℕ) :
    primeExtractionBilinearPhaseSum M N (markedExtractionBilinearCoefficient e η χ G γ j x) t =
      ∑ m ∈ M, ∑ n ∈ N,
        primeExtractionFirstPhaseCoefficient η χ (x^γ) t m *
          primeExtractionSecondPhaseCoefficient η χ j (x^γ) t n *
            G x (m*n-1) * (literalMarkedArrayWeight e x (m*n-1) : ℂ) := by
  unfold primeExtractionBilinearPhaseSum
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  unfold markedExtractionBilinearCoefficient primeExtractionFirstPhaseCoefficient
    primeExtractionSecondPhaseCoefficient
  ring

theorem primeExtractionMellinPhase_eq_markedLogTwist (t : ℝ) (n : ℕ) :
    primeExtractionMellinPhase t n = markedLogTwist n (2*Real.pi*t) := by
  unfold primeExtractionMellinPhase markedLogTwist
  congr 1
  push_cast
  ring

theorem primeExtractionFirstPhaseCoefficient_twistedSum (η : HeckeFamily.Character)
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ϑ : DirichletCharacter ℂ r)
    (z t s : ℝ) (S : Finset ℕ) :
    markedTwistedSum S (primeExtractionFirstPhaseCoefficient η χ z t) ϑ s =
      ∑ m ∈ S, roughPrimeFirstCoefficient (fun p => idealThetaCoeff η p * χ p) z m *
        ϑ m * markedLogTwist m (s + 2*Real.pi*t) := by
  unfold markedTwistedSum
  apply Finset.sum_congr rfl
  intro m _
  unfold primeExtractionFirstPhaseCoefficient
  rw [primeExtractionMellinPhase_eq_markedLogTwist]
  have ht : markedLogTwist m (s + 2*Real.pi*t) =
      markedLogTwist m (2*Real.pi*t) * markedLogTwist m s := by
    unfold markedLogTwist
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [ht]
  ring

end ArtinMatthews
