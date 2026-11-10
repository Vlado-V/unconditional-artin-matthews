module

public import ArtinMatthews.MarkedMinorArcDirtySecondGood
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The combined good event underlying the actual two-sided endpoint
projection, retained explicitly for good/error decompositions. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

def MarkedRawDirtyGood {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) : Prop :=
  MarkedRawFirstGood r d₀ Y w s ∧ MarkedRawDirtySecondGood e x r w s

theorem markedRawDirtyGoodCutoff_eq_ite {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    markedRawDirtyGoodCutoff e x r d₀ Y w χ s=
      if MarkedRawDirtyGood e x r d₀ Y w s then χ s else 0 := by
  unfold markedRawDirtyGoodCutoff markedRawFirstGoodCutoff markedRawDirtySecondGoodCutoff MarkedRawDirtyGood
  split_ifs <;> simp_all

theorem markedRawDirtyGood_pending_permute {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (z : Z) (a : MarkedRawActive (markedRawActualPrimeBand e x) M)
    (m : MarkedRawMemory (markedRawActualPrimeBand e x) B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j:ℕ))) :
    MarkedRawDirtyGood e x r d₀ Y w (z,(a,markedRawMemoryPermute m σ)) ↔
      MarkedRawDirtyGood e x r d₀ Y w (z,(a,m)) := Iff.rfl

end
end ArtinMatthews
