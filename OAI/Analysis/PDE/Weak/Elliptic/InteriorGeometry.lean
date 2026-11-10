module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

noncomputable section
open Set _root_.MeasureTheory Filter Metric
open scoped Topology
namespace OAI.Analysis.PDE.Weak

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_small_backward_shifts {S Ω : Set X} (hS : IsCompact S)
    (hΩ : IsOpen Ω) (hsub : S ⊆ Ω) (v : X) (hv : ‖v‖ ≤ 1) :
    ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 0) ∧ (∀ n, s n ≠ 0) ∧
      ∀ n, (fun x ↦ x + (-s n) • v) ⁻¹' S ⊆ Ω := by
  obtain ⟨δ, hδ, hthick⟩ := hS.exists_cthickening_subset_open hΩ hsub
  let s : ℕ → ℝ := fun n ↦ δ / ((n : ℝ) + 1)
  have hspos : ∀ n, 0 < s n := fun n ↦ div_pos hδ (by positivity)
  have hsbound : ∀ n, s n ≤ δ := by
    intro n
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  refine ⟨s, ?_, fun n ↦ (hspos n).ne', ?_⟩
  · have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    simpa [s, div_eq_mul_inv] using ht
  · intro n x hx
    change x + (-s n) • v ∈ S at hx
    apply hthick
    apply closedBall_subset_cthickening hx δ
    change dist x (x + (-s n) • v) ≤ δ
    simp only [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hspos n)]
    exact (mul_le_mul_of_nonneg_left hv (hspos n).le).trans (by simpa using hsbound n)

end OAI.Analysis.PDE.Weak
