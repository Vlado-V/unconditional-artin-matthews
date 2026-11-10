module

public import ArtinMatthews.MarkedPhysicalRootHaarLines
public import ArtinMatthews.MarkedPhysicalBadArcFamily
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

/-! The actual positive bad-root main term after the complete finite
residue-class average. The line conditions are retained inside the target
sum, and their density is paid once per union prime. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalBadRootIncidenceMain_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e) (T : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d₀ Y : ℝ,
      Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (S : ℕ) [NeZero S], ∀ (hS : Squarefree S)
        (A B C D : ℝ), A ≤ B → C ≤ D →
        ∀ (d b a : ℤ) (R Q W : ℝ) (ψ : ℝ → ℂ),
          1 ≤ Q → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
          (∀ u, ‖ψ u‖ ≤ W) → (∀ u, ψ u ≠ 0 → |u| ≤ R) →
          ∀ (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → (ℤ × ℤ) → Prop)
            (ℓ : (ℤ × ℤ) → MarkedRootLineTuple S),
            (∀ z ∈ markedPhysicalRootTargetWindow d R Y,
              ∀ g, E g z → markedRootKernelTuple hS g = ℓ z) →
          markedPhysicalRootIncidenceMain Finset.univ S A B C D
            (markedPhysicalBadArcLower e x source d₀ Y)
            (markedPhysicalBadArcUpper e x source d₀ Y)
            (markedPhysicalBadArcCoefficient e x source d₀ Y) d b a R Y Q ψ E ≤
          ((B-A)*(D-C)/(riemannZeta 2).re) * markedPhysicalRootLineMass S *
            ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
  have hμ := eventually_all.mpr (fun I : Finset J =>
    marked_actual_harmonic_fresh_probability_eventually (fun j : ↥(Finset.univ \ I) => e j.1)
      (fun j => by linarith [he j.1]))
  filter_upwards [hμ, markedPhysicalBadRootPositiveMain_log_saving e he hinj T]
    with x hμx hmain
  intro d₀ Y hY source S _hS0 hS A B C D hAB hCD d b a R Q W ψ hQ hYone hR hW hψ hsupp E ℓ hE
  have hc := markedPhysicalRootIncidenceMain_le_count Finset.univ hS A B C D hAB hCD
    (markedPhysicalBadArcLower e x source d₀ Y)
    (markedPhysicalBadArcUpper e x source d₀ Y)
    (markedPhysicalBadArcCoefficient e x source d₀ Y)
    (fun i _ => markedPhysicalBadArcCoefficient_nonneg e x source d₀ Y
      (fun I => (hμx I).1) i) d b a R Y Q ψ E ℓ hE
  have hm := hmain d₀ Y hY source S hS A B C D hAB hCD d b a R Q W ψ
    hQ hYone hR hW hψ hsupp
  have hscale : 0 ≤ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) *
      markedPhysicalRootLineMass S :=
    mul_nonneg (Nat.cast_nonneg _) (markedPhysicalRootLineMass_nonneg S)
  apply hc.trans
  apply (mul_le_mul_of_nonneg_left hm hscale).trans_eq
  have hN : (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) ≠ 0 := by
    exact_mod_cast (show Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) ≠ 0 from Nat.card_pos.ne')
  field_simp [hN, markedPhysicalRoot_zeta_two_pos.ne']

end ArtinMatthews
