module

public import ArtinMatthews.MarkedMinorArcBanRawEntry
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

/-! Exact raw-state action of the literal ban difference. -/
noncomputable section
namespace ArtinMatthews

open Matrix

theorem markedRawCleanApply_kernel_sub {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (K L : MarkedRawBackground P pads B → Matrix (MarkedRawCleanFiber P Z) (MarkedRawCleanFiber P Z) ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawCleanApply ν (K-L) f s = markedRawCleanApply ν K f s-markedRawCleanApply ν L f s := by
  unfold markedRawCleanApply
  simp only [Pi.sub_apply,Matrix.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem markedRawBanErrorKernel_action_difference {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawCleanApply ν (markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ) f s =
      markedRawCleanApply ν (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ) f s-
      markedRawCleanApply ν (markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ)) f s := by
  have he : markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ =
      markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ-
        markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ) := by
    funext bg
    exact markedRawBanErrorKernel_eq_difference hZ ψ η d₀ Y Q ρ χ bg
  rw [he,markedRawCleanApply_kernel_sub]

end ArtinMatthews
