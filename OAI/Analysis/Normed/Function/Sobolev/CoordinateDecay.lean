module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Normed.Function.Sobolev.WeakFourier
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
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
public import OAI.Analysis.Normed.Function.Sobolev.WeakIterated


set_option backward.privateInPublic true
@[expose] public section

open OAI.Analysis.Fourier.Wave

open Set _root_.MeasureTheory FourierTransform Filter InnerProductSpace
open scoped Topology BigOperators
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

/-- One coordinate detects the Euclidean norm, with a deliberately non-sharp
dimension factor. -/
theorem exists_large_coordinate {d : ℕ} (hd : 0 < d) (ξ : Space d) :
    ∃ i : Fin d, ‖ξ‖ ≤ (d : ℝ) * |ξ i| := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun j : Fin d ↦ |ξ j|) hne
  refine ⟨i, ?_⟩
  have heq : (∑ j : Fin d, EuclideanSpace.single j (ξ j)) = ξ := by
    ext j
    simp
  calc
    ‖ξ‖ = ‖∑ j : Fin d, EuclideanSpace.single j (ξ j)‖ := congrArg norm heq.symm
    _ ≤ ∑ j : Fin d, ‖EuclideanSpace.single j (ξ j)‖ := norm_sum_le _ _
    _ = ∑ j : Fin d, |ξ j| := by simp
    _ ≤ ∑ _j : Fin d, |ξ i| := Finset.sum_le_sum fun j hj ↦ hmax j hj
    _ = (d : ℝ) * |ξ i| := by simp

/-- Genuine iterated derivatives in one coordinate give decay in that
coordinate. -/
theorem coordinate_fourier_decay {d k : ℕ} (i : Fin d)
    (U : ℕ → Space d → ℝ) {K : Set (Space d)} (hK : IsCompact K)
    (hUK : ∀ j ≤ k, ∀ᵐ x, x ∉ K → U j x = 0)
    (hUi : ∀ j ≤ k, Integrable (U j))
    (hUD : ∀ j < k, OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume
      (EuclideanSpace.single i 1) (U j) (U (j + 1)))
    (ξ : Space d) :
    |ξ i| ^ k * ‖realFourier (U 0) ξ‖ ≤ ∫ x, ‖U k x‖ := by
  have he := norm_multiplier_iterated_weakDerivative
    (EuclideanSpace.single i 1) U hK hUK hUi hUD ξ
  have hi : inner ℝ (EuclideanSpace.single i 1) ξ = ξ i := by
    simpa using! EuclideanSpace.inner_single_left i (1 : ℝ) ξ
  rw [hi] at he
  apply le_trans _ he
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply pow_le_pow_left₀ (abs_nonneg _)
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  nlinarith [abs_nonneg (ξ i)]

/-- Combining coordinate decay with a uniform bound gives radial polynomial
decay. Only positivity of the dimension is needed. -/
theorem polynomial_decay_of_coordinate_bounds {d k : ℕ} (hd : 0 < d)
    (F : Space d → ℂ) {N M : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hbound : ∀ ξ, ‖F ξ‖ ≤ N)
    (hcoord : ∀ i : Fin d, ∀ ξ, |ξ i| ^ k * ‖F ξ‖ ≤ M) :
    ∀ ξ, (1 + ‖ξ‖) ^ k * ‖F ξ‖ ≤ 2 ^ k * (N + (d : ℝ) ^ k * M) := by
  intro ξ
  have hradial : ‖ξ‖ ^ k * ‖F ξ‖ ≤ (d : ℝ) ^ k * M := by
    obtain ⟨i, hi⟩ := exists_large_coordinate hd ξ
    calc
      ‖ξ‖ ^ k * ‖F ξ‖ ≤ ((d : ℝ) * |ξ i|) ^ k * ‖F ξ‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hi k) (norm_nonneg _)
      _ = (d : ℝ) ^ k * (|ξ i| ^ k * ‖F ξ‖) := by rw [mul_pow]; ring
      _ ≤ (d : ℝ) ^ k * M := mul_le_mul_of_nonneg_left (hcoord i ξ) (by positivity)
  by_cases hsmall : ‖ξ‖ ≤ 1
  · calc
      (1 + ‖ξ‖) ^ k * ‖F ξ‖ ≤ 2 ^ k * N := by
        apply mul_le_mul _ (hbound ξ) (norm_nonneg _) (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * (N + (d : ℝ) ^ k * M) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hlarge : 1 ≤ ‖ξ‖ := (lt_of_not_ge hsmall).le
    calc
      (1 + ‖ξ‖) ^ k * ‖F ξ‖ ≤ (2 * ‖ξ‖) ^ k * ‖F ξ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * (‖ξ‖ ^ k * ‖F ξ‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ k * ((d : ℝ) ^ k * M) :=
        mul_le_mul_of_nonneg_left hradial (by positivity)
      _ ≤ 2 ^ k * (N + (d : ℝ) ^ k * M) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hN) (by positivity)

end OAI.Analysis.Normed.Function.Sobolev
