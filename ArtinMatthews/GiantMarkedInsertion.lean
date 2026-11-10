module

public import ArtinMatthews.MarkedProgressionWeightedModel
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

/-! Inserting a giant prime as an additional selected divisor leaves the
small-band residual unchanged and multiplies its Euler mean by 1/ell. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

theorem marked_insert_selected_sdiff (P S : Finset ℕ) {ell : ℕ} (h : ell ∉ P) :
    insert ell P \ insert ell S = P \ S := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨hp | hp, hn⟩
    · exact (hn (Or.inl hp)).elim
    · exact ⟨hp, fun hs => hn (Or.inr hs)⟩
  · rintro ⟨hp, hn⟩
    exact ⟨Or.inr hp, fun hh => hh.elim (fun heq => h (heq ▸ hp)) hn⟩

theorem marked_insert_selected_active (P S : Finset ℕ) (hS : S ⊆ P) (ell u : ℕ) :
    insert ell S ⊆ activeDivisors (insert ell P) u ↔
      ell ∣ u ∧ S ⊆ activeDivisors P u := by
  constructor
  · intro hs
    refine ⟨(Finset.mem_filter.mp (hs (Finset.mem_insert_self _ _))).2, ?_⟩
    intro p hp
    exact Finset.mem_filter.mpr ⟨hS hp,
      (Finset.mem_filter.mp (hs (Finset.mem_insert_of_mem hp))).2⟩
  · rintro ⟨hdiv, hs⟩ p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hdiv⟩
    · obtain ⟨hpP, hpu⟩ := Finset.mem_filter.mp (hs hp)
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hpP, hpu⟩

theorem markedWeightedResidual_insert_selected (P S : Finset ℕ) (hS : S ⊆ P)
    (θ : ℕ → ℝ) {ell : ℕ} (h : ell ∉ P) (u : ℕ) :
    markedWeightedResidual (insert ell P) (insert ell S) θ u =
      (if ell ∣ u then (1 : ℝ) else 0) * markedWeightedResidual P S θ u := by
  classical
  unfold markedWeightedResidual
  rw [marked_insert_selected_sdiff P S h]
  simp only [marked_insert_selected_active P S hS]
  by_cases hd : ell ∣ u <;> by_cases hs : S ⊆ activeDivisors P u <;> simp [hd, hs]

theorem markedWeightedModel_insert_selected (P S : Finset ℕ) (hS : S ⊆ P)
    (θ : ℕ → ℝ) {ell : ℕ} (h : ell ∉ P) :
    markedWeightedModel (insert ell P) (insert ell S) θ =
      (1 / (ell : ℝ)) * markedWeightedModel P S θ := by
  classical
  have hS' : ell ∉ S := fun hs => h (hS hs)
  simp only [markedWeightedModel, marked_insert_selected_sdiff P S h,
    Finset.prod_insert hS', Nat.cast_mul]
  ring

end ArtinMatthews
