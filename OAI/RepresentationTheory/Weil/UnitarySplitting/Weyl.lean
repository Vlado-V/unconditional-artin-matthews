module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.UnitarySplitting.HeisenbergStability
public import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance
public import OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg


set_option backward.privateInPublic true
@[expose] public section

/-! # Weyl -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Weyl.Construction

noncomputable section

/-! Unitarity and adjoint identities for the actual Weyl operators. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)

theorem heisenbergOperator_energy (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.l2Energy F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
  change (∫ x, ‖Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x‖ ^ 2 ∂ Weak.Construction.referencePositionMeasure F d) =
    ∫ x, ‖f.val x‖ ^ 2 ∂ Weak.Construction.referencePositionMeasure F d
  simp_rw [FourierCovariance.Construction.heisenbergFunction_dot, norm_mul, hu, one_mul]
  exact integral_sub_right_eq_self (fun x => ‖f.val x‖ ^ 2) (FourierCovariance.Construction.phasePosition v)

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem heisenbergOperator_composition (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f) =
      ψ (Oscillator.Construction.standardSymplecticPairing d v w / 2) • HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (v + w) f := by
  apply Subtype.ext
  exact Heisenberg.Construction.heisenbergFunction_composition ψ v w f.val

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem heisenbergOperator_neg_cancel (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (-v) (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) = f := by
  apply Subtype.ext
  exact Heisenberg.Construction.heisenbergFunction_neg_left_cancel ψ v f.val

theorem heisenbergOperator_inner (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f g : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f),
      Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v g)⟫_ℂ =
        ⟪Weak.Construction.testToL2 F d f, Weak.Construction.testToL2 F d g⟫_ℂ :=
  Weak.Construction.energy_preserving_inner F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v).toLinearMap
    (heisenbergOperator_energy hF ψ hc hu v) f g

theorem heisenbergOperator_adjoint (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f g : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d g, Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)⟫_ℂ =
      ⟪Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (-v) g), Weak.Construction.testToL2 F d f⟫_ℂ := by
  have hh := heisenbergOperator_inner hF ψ hc hu (-v) g (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)
  rw [heisenbergOperator_neg_cancel] at hh
  exact hh.symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Weyl.Construction
