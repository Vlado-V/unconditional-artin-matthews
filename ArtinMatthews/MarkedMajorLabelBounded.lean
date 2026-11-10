module

public import ArtinMatthews.MarkedMajorLabelMeanConjugate
public import ArtinMatthews.MarkedMajorEnergyBounded
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

/-! Nonquantitative global bounds for the finite actual endpoint sums.
These witnesses justify weighted integration; their size is never used. -/
namespace ArtinMatthews
open Finset

theorem markedMajorLabelPolynomial_bounded {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedMajorLabelPolynomial bands cutoff χb θ Y t‖ ≤ B := by
  let a := fun (s : ℕ) => cutoff ((s:ℝ)/Y)*Complex.exp (((-2*Real.pi*θ*(s:ℝ)/Y:ℝ):ℂ)*Complex.I)*
    (markedMajorLabelMass bands:ℂ)*χb s
  refine ⟨‖(Y:ℂ)⁻¹‖*∑ s ∈ markedMajorLabelSet bands,‖a s‖,?_⟩
  intro t
  unfold markedMajorLabelPolynomial
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact markedNaturalPolynomial_norm_le (markedMajorLabelSet bands) a t

theorem markedMajorLabelEndpoint_bounded {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t‖ ≤ B := by
  obtain ⟨A,hA⟩ := markedMajorLabelPolynomial_bounded bands cutoff χb θ Y
  obtain ⟨B,hB⟩ := marked_centered_sum_bounded χ W modulation H u v
  obtain ⟨C,hC⟩ := marked_dyadic_sum_bounded l r U β
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨A*B*C,?_⟩
  intro t
  unfold markedMajorLabelEndpoint
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul (hA t) (hB t) (norm_nonneg _) hA0)
    (hC t) (norm_nonneg _) (mul_nonneg hA0 hB0)

theorem markedMajorLabelConjugateEndpoint_bounded {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t‖ ≤ B := by
  simp only [markedMajorLabelConjugateEndpoint_eq]
  exact markedMajorLabelEndpoint_bounded bands cutoff χb θ Y χ W (-modulation) H u v U l r β

theorem markedMajorLabelConjugateEndpoint_continuous {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    Continuous (markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β) := by
  have he : markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β =
      markedMajorLabelEndpoint bands cutoff χb θ Y χ W (-modulation) H u v U l r β := by
    funext t
    exact markedMajorLabelConjugateEndpoint_eq bands cutoff χb θ Y χ W modulation H u v U l r β t
  rw [he]
  exact markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W (-modulation) H u v U l r β

end ArtinMatthews
