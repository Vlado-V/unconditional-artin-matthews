module

public import ArtinMatthews.MarkedPhysicalBadRootReplacement
public import ArtinMatthews.MarkedPhysicalRootHaarMain
public import ArtinMatthews.MarkedPhysicalBadHaarMain
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

/-! Identification and estimate of the explicit main term returned by
the actual positive canonical-root replacement. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalBadRootKernelMain_eq_positive
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (S : ℕ) (A B C D : ℝ) (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ) :
    markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D d b a R Q ψ =
      markedPhysicalRootPositiveMain Finset.univ S A B C D
        (markedPhysicalBadArcLower e x source d₀ Y)
        (markedPhysicalBadArcUpper e x source d₀ Y)
        (markedPhysicalBadArcCoefficient e x source d₀ Y) d b a R Y Q ψ := by
  unfold markedPhysicalBadRootKernelMain markedPhysicalRootPositiveMain
  rw [Finset.product_eq_sprod, Finset.sum_product]

theorem markedPhysicalBadRootKernelMain_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e) (T : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d₀ Y : ℝ,
      Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (S : ℕ), Squarefree S →
        ∀ A B C D : ℝ, A ≤ B → C ≤ D →
        ∀ (d b a : ℤ) (R Q W : ℝ) (ψ : ℝ → ℂ),
          1 ≤ Q → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
          (∀ u, ‖ψ u‖ ≤ W) → (∀ u, ψ u ≠ 0 → |u| ≤ R) →
          markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D d b a R Q ψ ≤
          ((B-A)*(D-C)/((riemannZeta 2).re*
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
            ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
  filter_upwards [markedPhysicalBadRootPositiveMain_log_saving e he hinj T] with x hx
  intro d₀ Y hY source S hS A B C D hAB hCD d b a R Q W ψ hQ hYone hR hW hψ hsupp
  rw [markedPhysicalBadRootKernelMain_eq_positive]
  exact hx d₀ Y hY source S hS A B C D hAB hCD d b a R Q W ψ hQ hYone hR hW hψ hsupp

end ArtinMatthews
