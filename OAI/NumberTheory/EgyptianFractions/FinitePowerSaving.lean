module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

namespace OAI
noncomputable section
namespace Problem337

/-- A finite collection of eventual power-saving estimates admits a single
positive saving, coefficient, and threshold. Auxiliary parameters are left
arbitrary, so an interval and a reciprocal-phase numerator can be included. -/
theorem finite_uniform_rpow_saving {ι α : Type*} (s : Finset ι)
    (f : ι → ℝ → α → ℝ) (P : ι → ℝ → α → Prop) (p : ℝ)
    (h : ∀ i ∈ s, ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ,
      ∀ U : ℝ, T ≤ U → ∀ z : α, P i U z → f i U z ≤ A * U ^ (p - δ)) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ, 1 ≤ T ∧
      ∀ i ∈ s, ∀ U : ℝ, T ≤ U → ∀ z : α,
        P i U z → f i U z ≤ A * U ^ (p - δ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, 1, by norm_num, by norm_num, 1, le_rfl, ?_⟩
    simp
  | @insert a s ha ih =>
    obtain ⟨A, δ, hA, hδ, T, hbound⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨B, ε, hB, hε, V, hV, hrest⟩ :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨max A B, min δ ε, lt_of_lt_of_le hA (le_max_left _ _),
      lt_min hδ hε, max T V, le_trans hV (le_max_right _ _), ?_⟩
    intro i hi U hU z hz
    have hUT : T ≤ U := le_trans (le_max_left _ _) hU
    have hUV : V ≤ U := le_trans (le_max_right _ _) hU
    have hU1 : 1 ≤ U := le_trans hV hUV
    have hpow : 0 ≤ U ^ (p - min δ ε) := Real.rpow_nonneg (by linarith) _
    rcases Finset.mem_insert.mp hi with hia | hi
    · subst i
      calc
        f a U z ≤ A * U ^ (p - δ) := hbound U hUT z hz
        _ ≤ A * U ^ (p - min δ ε) := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          apply Real.rpow_le_rpow_of_exponent_le hU1
          exact sub_le_sub_left (min_le_left δ ε) p
        _ ≤ max A B * U ^ (p - min δ ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
    · calc
        f i U z ≤ B * U ^ (p - ε) := hrest i hi U hUV z hz
        _ ≤ B * U ^ (p - min δ ε) := by
          apply mul_le_mul_of_nonneg_left _ hB.le
          apply Real.rpow_le_rpow_of_exponent_le hU1
          exact sub_le_sub_left (min_le_right δ ε) p
        _ ≤ max A B * U ^ (p - min δ ε) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

/-- Uniformisation over the bounded collection of derivative orders used for
reciprocal phases. This also covers an empty order interval. -/
theorem finite_derivative_order_power_saving {α : Type*} (Q : ℕ)
    (f : ℕ → ℝ → α → ℝ) (P : ℕ → ℝ → α → Prop)
    (h : ∀ k : ℕ, 4 ≤ k → k ≤ Q →
      ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ,
        ∀ U : ℝ, T ≤ U → ∀ z : α, P k U z → f k U z ≤ A * U ^ (1 - δ)) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ, 1 ≤ T ∧
      ∀ k : ℕ, 4 ≤ k → k ≤ Q → ∀ U : ℝ, T ≤ U → ∀ z : α,
        P k U z → f k U z ≤ A * U ^ (1 - δ) := by
  obtain ⟨A, δ, hA, hδ, T, hT, hb⟩ :=
    finite_uniform_rpow_saving (Finset.Icc 4 Q) f P 1
      (fun k hk => h k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  exact ⟨A, δ, hA, hδ, T, hT, fun k hk hQ => hb k (Finset.mem_Icc.mpr ⟨hk, hQ⟩)⟩

end Problem337

end

end OAI
