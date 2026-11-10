module

public import ArtinMatthews.MarkedPhysicalRootDiscrepancyMass
public import ArtinMatthews.MarkedPhysicalSourcePolynomialGlobal
public import ArtinMatthews.MarkedPhysicalSourceTailNorm
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

/-! The original physical damping is compared with the capped line
main term through its genuine polynomial, root and positive-tail terms. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysical_norm_four_differences (a b c d f : ℂ) :
    ‖a-f‖ ≤ ‖a-b‖+‖b-c‖+‖c-d‖+‖d-f‖ := by
  have tri (x y z : ℂ) : ‖x-z‖ ≤ ‖x-y‖+‖y-z‖ := by
    calc
      _ = ‖(x-y)+(y-z)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have h1 := tri a b f
  have h2 := tri b c f
  have h3 := tri c d f
  linarith

theorem markedPhysicalSourceDampingGlobal_capped_error_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R)
    (S : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) → ℕ) (hS : ∀ a,S a≠0)
    (hdis : Pairwise (fun j k => Disjoint (markedLogPowerBand (e j) x) (markedLogPowerBand (e k) x)))
    (hn : 0 < markedMemoryMomentLength x) (hU : 1 < U) (hVr : 1 < Vr)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) → ℤ × ℤ)
    (hw : ∀ a,markedMinorIntegerDet a.1 (w a)=1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖markedPhysicalSourceDampingGlobal e x ψ η d₀ Y Q q U Vr S hS (R := R) w-
      (U*Vr/(riemannZeta 2).re) •
        markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y Q q U Vr R hR‖ ≤
      markedPhysicalOddRootDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr+
      (U*Vr/(riemannZeta 2).re)*markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U Vr R hR+
      ‖markedPhysicalCoordinateRootGlobal e x ψ η d₀ Y Q hR q U Vr
          (2*markedPhysicalBonferroniDepth x)-
        (U*Vr/(riemannZeta 2).re) •
          markedPhysicalCoordinatePolynomialGlobal e x ψ η d₀ Y Q q U Vr R hR‖+
      (U*Vr/(riemannZeta 2).re)*
        ‖markedPhysicalCoordinatePolynomialGlobal e x ψ η d₀ Y Q q U Vr R hR-
          markedPhysicalCoordinateIndependentGlobal e x ψ η d₀ Y Q q U Vr R hR‖+
      (U*Vr/(riemannZeta 2).re)*
        ‖markedPhysicalCoordinateIndependentGlobal e x ψ η d₀ Y Q q U Vr R hR-
          markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y Q q U Vr R hR‖ := by
  let d := U*Vr/(riemannZeta 2).re
  have hd : 0 ≤ d := div_nonneg (mul_nonneg (by linarith) (by linarith)) markedRoot_zeta_two_pos.le
  have hfirst := markedPhysicalSourceDampingGlobal_root_error e x ψ η d₀ Y Q q U Vr S hS hR
    hdis hn hU hVr w hw hq0 hq1
  have hchain := markedPhysical_norm_four_differences
    (markedPhysicalSourceDampingGlobal e x ψ η d₀ Y Q q U Vr S hS (R := R) w)
    (markedPhysicalCoordinateRootGlobal e x ψ η d₀ Y Q hR q U Vr (2*markedPhysicalBonferroniDepth x))
    (d • markedPhysicalCoordinatePolynomialGlobal e x ψ η d₀ Y Q q U Vr R hR)
    (d • markedPhysicalCoordinateIndependentGlobal e x ψ η d₀ Y Q q U Vr R hR)
    (d • markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y Q q U Vr R hR)
  have hmul (a b : ℂ) : ‖d • a-d • b‖=d*‖a-b‖ := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
  rw [hmul,hmul] at hchain
  linarith

end
end ArtinMatthews
