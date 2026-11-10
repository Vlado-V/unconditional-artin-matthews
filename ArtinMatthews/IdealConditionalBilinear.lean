module

public import ArtinMatthews.IdealSelectedFill
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Conditional tuple comparisons average in the shared labels with
exactly the original two full-label energies. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealConditional_norm {Z : Type*} [Fintype Z]
    (ρ F G : Z → ℝ) (hρ : ∀ z,0 ≤ ρ z) (hF : ∀ z,0 ≤ F z) (hG : ∀ z,0 ≤ G z)
    (T : Z → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ z,‖T z‖ ≤ ε*Real.sqrt (F z)*Real.sqrt (G z)) :
    ‖∑ z,(ρ z:ℂ)*T z‖ ≤ ε*Real.sqrt (∑ z,ρ z*F z)*Real.sqrt (∑ z,ρ z*G z) := by
  have hs (z : Z) :
      ρ z*Real.sqrt (F z)*Real.sqrt (G z)=
        Real.sqrt (ρ z*F z)*Real.sqrt (ρ z*G z) := by
    rw [Real.sqrt_mul (hρ z),Real.sqrt_mul (hρ z)]
    have hr := Real.sq_sqrt (hρ z)
    calc
      _ = (Real.sqrt (ρ z))^2*Real.sqrt (F z)*Real.sqrt (G z) := by rw [hr]
      _ = _ := by ring
  calc
    _ ≤ ∑ z,ρ z*‖T z‖ := by
      refine (norm_sum_le _ _).trans_eq ?_
      apply sum_congr rfl
      intro z _
      rw [norm_mul,Complex.norm_of_nonneg (hρ z)]
    _ ≤ ε*∑ z,Real.sqrt (ρ z*F z)*Real.sqrt (ρ z*G z) := by
      rw [mul_sum]
      apply sum_le_sum
      intro z _
      calc
        _ ≤ ρ z*(ε*Real.sqrt (F z)*Real.sqrt (G z)) := mul_le_mul_of_nonneg_left (hT z) (hρ z)
        _ = _ := by rw [← hs]; ring
    _ ≤ _ := by
      have hc := Real.sum_sqrt_mul_sqrt_le (s:=univ)
        (fun z => mul_nonneg (hρ z) (hF z)) (fun z => mul_nonneg (hρ z) (hG z))
      calc
        _ ≤ ε*(Real.sqrt (∑ z,ρ z*F z)*Real.sqrt (∑ z,ρ z*G z)) :=
          mul_le_mul_of_nonneg_left hc hε
        _ = _ := by ring

theorem idealSelectedConditional_norm {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (A B : Finset (G × Fin M)) (f g : MarkedPhysicalMarking P M → ℂ)
    (T : MarkedPhysicalMarking P M → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ z,‖T z‖ ≤
      ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealFullSelectedBands P A))
        (fun x => f (idealSelectedFill A z x)))*
      Real.sqrt (idealFrameEnergy (idealSelectedMass (idealFullSelectedBands P B))
        (fun x => g (idealSelectedFill B z x)))) :
    ‖idealLabelExpectation P M T‖ ≤ ε*Real.sqrt (idealLabelEnergy P M f)*Real.sqrt (idealLabelEnergy P M g) := by
  have hmA := idealSelectedMass_nonneg (idealFullSelectedBands P A) (fun a => hV a.val.1)
  have hmB := idealSelectedMass_nonneg (idealFullSelectedBands P B) (fun a => hV a.val.1)
  have h := idealConditional_norm (idealLabelMass P M) _ _ (idealLabelMass_nonneg P M hV)
    (fun z => idealFrameEnergy_nonneg _ hmA _) (fun z => idealFrameEnergy_nonneg _ hmB _) T hε hT
  rw [idealSelectedFill_energy P hV A f,idealSelectedFill_energy P hV B g] at h
  exact h

end
end ArtinMatthews
