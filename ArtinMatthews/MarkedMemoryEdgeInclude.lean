module

public import ArtinMatthews.MarkedRawEdgeInclude
public import ArtinMatthews.MarkedMemoryHistoryEdgeChoice
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

/-! Both actual slot permutations commute with restriction of the
position space. No permutation or probability factor is discarded. -/

noncomputable section
namespace ArtinMatthews

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hW : ∀ z∈W,IsCoprime z.1 z.2)

def markedMemoryEdgeChoiceInclude (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedMemoryEdgeChoice hZ s) :
    MarkedMemoryEdgeChoice hW (markedRawStateInclude h s) :=
  ⟨c.1,markedRawEdgeChoiceInclude h hZ hW (markedRawSlotEquiv c.1 s) c.2.1,c.2.2⟩

def markedMemoryEdgeChoiceWindowEquiv (s : MarkedRawState P (pads+1) B Z) :
    MarkedMemoryEdgeChoice hZ s ≃
      {c : MarkedMemoryEdgeChoice hW (markedRawStateInclude h s) // c.2.1.target.1∈Z} where
  toFun c := ⟨markedMemoryEdgeChoiceInclude h hZ hW s c,c.2.1.target.2⟩
  invFun c := ⟨c.1.1,
    (markedRawEdgeChoiceWindowEquiv h hZ hW (markedRawSlotEquiv c.1.1 s)).symm ⟨c.1.2.1,c.2⟩,
    c.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedMemoryEdgeChoiceInclude_target (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceTarget hW (markedRawStateInclude h s)
      (markedMemoryEdgeChoiceInclude h hZ hW s c)=
      markedRawStateInclude h (markedMemoryEdgeChoiceTarget hZ s c) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryEdgeChoiceInclude_weight [DecidableEq J]
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B W → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceWeight ν V hW ψ η d₀ Y Q ρ χ (markedRawStateInclude h s)
      (markedMemoryEdgeChoiceInclude h hZ hW s c)=
      markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ
        (fun s => χ (markedRawStateInclude h s)) s c := by
  change ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
      (markedRawEdgeChoicePrimeMass ν V hW
        (markedRawStateInclude h (markedRawSlotEquiv c.1 s))
        (markedRawEdgeChoiceInclude h hZ hW (markedRawSlotEquiv c.1 s) c.2.1):ℂ)*
      markedRawEdgeChoiceCoefficient hW ψ η d₀ Y Q ρ χ
        (markedRawStateInclude h (markedRawSlotEquiv c.1 s))
        (markedRawEdgeChoiceInclude h hZ hW (markedRawSlotEquiv c.1 s) c.2.1)*
      ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)=_
  rw [markedRawEdgeChoiceInclude_mass,markedRawEdgeChoiceInclude_coefficient]
  rfl

end ArtinMatthews
