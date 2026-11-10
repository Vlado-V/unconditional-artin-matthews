module

public import ArtinMatthews.IdealSelectedLabels
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

/-! The selected prime products are units for every character in the
literal conductor cutoff. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I]

theorem idealSelectedProduct_coprime {P : I → Finset ℕ} {Q : ℕ}
    (hP : ∀ i p, p ∈ P i → p.Prime) (hlarge : ∀ i p, p ∈ P i → Q < p)
    (χ : IdealPrimitiveCharacters Q) (a : IdealSelectedLabels P) :
    (idealSelectedProduct a).Coprime χ.1.val := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i _
  apply (hP i _ (a i).property).coprime_iff_not_dvd.mpr
  intro hdvd
  have hle := Nat.le_of_dvd (idealPrimitiveCharacter_level_pos χ) hdvd
  have hq : χ.1.val ≤ Q := (mem_Icc.mp χ.1.property).2
  have hp := hlarge i _ (a i).property
  omega

theorem idealSelectedCharacter_norm_one {P : I → Finset ℕ} {Q : ℕ}
    (hP : ∀ i p, p ∈ P i → p.Prime) (hlarge : ∀ i p, p ∈ P i → Q < p)
    (χ : IdealPrimitiveCharacters Q) (a : IdealSelectedLabels P) :
    ‖idealPrimitiveCharacterValue χ (idealSelectedProduct a)‖ = 1 := by
  let : NeZero χ.1.val := ⟨(idealPrimitiveCharacter_level_pos χ).ne'⟩
  have hu := χ.2.val.unit_norm_eq_one
    (ZMod.unitOfCoprime (idealSelectedProduct a) (idealSelectedProduct_coprime hP hlarge χ a))
  simpa only [ZMod.coe_unitOfCoprime, idealPrimitiveCharacterValue] using hu

end
end ArtinMatthews
