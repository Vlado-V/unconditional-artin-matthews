module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedRow
public import ArtinMatthews.MarkedMinorArcRawEdgeChoiceCauchy
public import ArtinMatthews.MarkedMinorArcRawEdgeChargedPositive
public import ArtinMatthews.MarkedMinorArcRawEdgeEnergyReduction
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact column evaluation for the full literal edge Cauchy energy.
The column is the concrete reversed row with exchanged storage/promotion
charges, derived on the actual factorial symmetric memory space. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgeChoiceReverseEnergy_sum_eq_swapped_row
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z active, MarkedRawMemorySymmetric (fun m => χ (z,(active,m))))
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m)))) :
    (∑ s, markedRawStateMass ν s *
      markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s) =
      ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2 *
        markedRawEdgeChargedWeightedAbsRow ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ
          (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target)
          v₀ s (fun _ => 1) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  apply Complex.ofReal_injective
  rw [markedRawEdgeChoiceReverseEnergy_sum_eq_reversed_action ν V hZ ψ η d₀ Y Q ρ v₀ χ f hχ hf]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro s _
  have hrow := markedRawEdgeChargedWeightedAbsRow_mul_weight_eq_apply ν
    (fun _ => 1) (fun j => (V j)⁻¹) hν (fun _ => zero_le_one)
    (fun j => (inv_pos.mpr (hV j)).le) hZ
    (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target) hv₀ s
  simp only [Complex.ofReal_one] at hrow
  rw [← hrow]
  have hw : (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (markedRawMemorySchurWeight_pos hv₀ s.2.2).ne'
  rw [Complex.ofReal_div]
  field_simp [hw]

end
end ArtinMatthews
