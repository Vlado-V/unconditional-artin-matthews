module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeChoices
public import ArtinMatthews.MarkedMinorArcRawEdgeDetector
public import ArtinMatthews.MarkedMinorArcDirtyAnchor
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal nonzero delta coefficient implies the actual dirty determinant,
with original full source product and genuine promoted/fresh target factors. -/
noncomputable section
namespace ArtinMatthews

theorem markedDirtyRawEdge_delta_support {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : ℝ → ℂ) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s)
    (hne : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y) s choice ≠ 0) :
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
    (d₀ ≤ (D:ℝ) ∧ (D:ℝ)<2*d₀) ∧
      ((D:ℤ) ∣ markedMinorIntegerDet s.1.1 choice.target.1) ∧
      ¬MarkedRawFullCrossBan s.2.1 (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh) ∧
      markedMinorIntegerDet s.1.1 choice.target.1/(D:ℤ) =
        (markedRawLastProduct ((markedRawActiveSplit pads) s.2.1).2:ℤ)-
          (markedRawLastProduct (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh):ℤ) := by
  classical
  unfold markedRawEdgeChoiceDetectorCoefficient at hne
  dsimp only at hne ⊢
  split_ifs at hne with hdyad hdiv hban
  · exact False.elim (hne rfl)
  · refine ⟨hdyad,hdiv,hban,?_⟩
    by_contra hδ
    simp [markedRawEdgeDeltaDetector] at hne
    exact hδ hne.1
  · exact False.elim (hne rfl)
  · exact False.elim (hne rfl)

theorem markedDirtyRawEdge_delta_determinant {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : ℝ → ℂ) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (jstar : J) (kstar : Fin (s.2.2.1.1 jstar:ℕ))
    (hk : choice.promotions jstar=some kstar)
    (hne : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y) s choice ≠ 0) :
    markedMinorIntegerDet s.1.1 choice.target.1 = markedMinorDirtyDeterminant
      (markedSourceFullProduct (markedRawNumericActive s.2.1):ℤ)
      (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ)
      ((s.2.2.2 jstar kstar).1.1:ℕ)
      (markedDirtyEdgeOtherPromotedProduct s.2.2 choice.promotions choice.fresh jstar:ℤ)
      (markedDirtyEdgeFreshProduct s.2.2 choice.promotions choice.fresh:ℤ) := by
  have hs := markedDirtyRawEdge_delta_support hZ ψ η d₀ Y ρ χ s choice hne
  have he := (Int.ediv_mul_cancel hs.2.1).symm
  rw [hs.2.2.2] at he
  have hfull : (markedSourceFullProduct (markedRawNumericActive s.2.1):ℤ)=
      (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ)*
        (markedRawLastProduct ((markedRawActiveSplit pads) s.2.1).2:ℤ) := by
    exact_mod_cast markedRawFullProduct_split pads s.2.1
  have htarget : (markedRawLastProduct (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh):ℤ)=
      ((s.2.2.2 jstar kstar).1.1:ℕ)*
        (markedDirtyEdgeOtherPromotedProduct s.2.2 choice.promotions choice.fresh jstar:ℤ)*
        (markedDirtyEdgeFreshProduct s.2.2 choice.promotions choice.fresh:ℤ) := by
    exact_mod_cast markedDirtyEdgeTargetProduct_split s.2.2 choice.promotions choice.fresh jstar kstar hk
  rw [htarget] at he
  unfold markedMinorDirtyDeterminant
  rw [hfull]
  linear_combination he

end ArtinMatthews
