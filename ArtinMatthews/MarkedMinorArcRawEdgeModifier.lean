module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedRow
public import ArtinMatthews.MarkedMinorArcRawEdgeChoiceCauchy
public import ArtinMatthews.MarkedChoiceModifierCauchy
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgePromotionBound
public import ArtinMatthews.MarkedMinorArcRawEdgeEnergyColumn
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Bounded modifiers of literal edge choices retain the proved crude
absolute Schur majorant. The signed good-edge saving is used separately
on untouched edges only. -/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeModifiedApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (modifier : (s : MarkedRawState P (pads+1) B Z) → MarkedRawEdgeChoice hZ s → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ c : MarkedRawEdgeChoice hZ s, (markedRawEdgeChoicePrimeMass ν V hZ s c:ℂ)*
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c *
      (modifier s c*f (markedRawEdgeTargetState hZ s c))

theorem markedRawEdgeModifiedApply_choice_cauchy
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (modifier : (s : MarkedRawState P (pads+1) B Z) → MarkedRawEdgeChoice hZ s → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (hm : ∀ c, ‖modifier s c‖ ≤ 1) :
    ‖markedRawEdgeModifiedApply ν V hZ ψ η d₀ Y Q ρ χ modifier f s‖ ^ 2 ≤
      markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s (fun _ => 1) *
        markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s := by
  classical
  have hmass (c : MarkedRawEdgeChoice hZ s) :
      ‖(markedRawEdgeChoicePrimeMass ν V hZ s c : ℂ) *
        markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖ =
        markedRawEdgeChoicePrimeMass ν V hZ s c *
          ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s c)]
  have h := markedChoiceModifier_finite_cauchy
    (fun c : MarkedRawEdgeChoice hZ s => (markedRawEdgeChoicePrimeMass ν V hZ s c : ℂ) *
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c)
    (fun c => f (markedRawEdgeTargetState hZ s c)) (modifier s)
    (fun c => markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c) /
      markedRawMemorySchurWeight v₀ s.2.2)
    (fun _ => div_pos (markedRawMemorySchurWeight_pos hv₀ _)
      (markedRawMemorySchurWeight_pos hv₀ _)) hm
  simp only [hmass] at h
  convert h using 1
  congr 1
  unfold markedRawEdgeCrudeWeightedAbsRow markedRawEdgeChoiceReverseEnergy
  simp only [one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  field_simp [(markedRawMemorySchurWeight_pos hv₀ s.2.2).ne',
    (markedRawMemorySchurWeight_pos hv₀ (markedRawEdgeTargetMemory hZ s c)).ne']


theorem markedRawEdgeModifiedApply_energy_le_of_rows
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) {v₀ R : ℝ} (hv₀ : 0 < v₀) (hR : 0 ≤ R)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (modifier : (s : MarkedRawState P (pads+1) B Z) → MarkedRawEdgeChoice hZ s → ℂ)
    (hm : ∀ s c, ‖modifier s c‖ ≤ 1)
    (hχ : ∀ z active, MarkedRawMemorySymmetric (fun m => χ (z,(active,m))))
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m))))
    (hrow : ∀ s, markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s (fun _ => 1) ≤ R)
    (hcolumn : ∀ s, markedRawEdgeChargedWeightedAbsRow ν (fun _ => 1)
      (fun j => ((V j)⁻¹ : ℝ)) hZ
      (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target)
      v₀ s (fun _ => 1) ≤ R) :
    (∑ s, markedRawStateMass ν s * ‖markedRawEdgeModifiedApply ν V hZ ψ η d₀ Y Q ρ χ modifier f s‖ ^ 2) ≤
      R ^ 2 * ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2 := by
  classical
  calc
    _ ≤ R * ∑ s, markedRawStateMass ν s *
        markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      have hc := markedRawEdgeModifiedApply_choice_cauchy ν V hν hV hZ ψ η d₀ Y Q ρ hv₀ χ f modifier s (hm s)
      have he := markedRawEdgeChoiceReverseEnergy_nonneg ν V hν hV hZ ψ η d₀ Y Q ρ hv₀ χ f s
      calc
        _ ≤ markedRawStateMass ν s *
            (markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s (fun _ => 1) *
              markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s) :=
          mul_le_mul_of_nonneg_left hc (markedRawStateMass_nonneg ν hν s)
        _ ≤ markedRawStateMass ν s *
            (R * markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hrow s) he)
            (markedRawStateMass_nonneg ν hν s)
        _ = _ := by ring
    _ = R * ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2 *
        markedRawEdgeChargedWeightedAbsRow ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ
          (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target)
          v₀ s (fun _ => 1) := by
      rw [markedRawEdgeChoiceReverseEnergy_sum_eq_swapped_row ν V hν hV hZ ψ η d₀ Y Q ρ hv₀ χ f hχ hf]
    _ ≤ R * (R * ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hR
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      calc
        _ ≤ markedRawStateMass ν s * ‖f s‖ ^ 2 * R :=
          mul_le_mul_of_nonneg_left (hcolumn s)
            (mul_nonneg (markedRawStateMass_nonneg ν hν s) (sq_nonneg _))
        _ = _ := by ring
    _ = _ := by ring


end
end ArtinMatthews
