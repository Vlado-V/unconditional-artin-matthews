module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerKernel
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.RepresentationTheory.Weil.Local.UnitaryInner


set_option backward.privateInPublic true
@[expose] public section

/-! # Real Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.RealCover.CM

noncomputable section

/-! Construct the real Schrödinger cover required by PoissonAutomorphy from LocalWeil's
actual bare metaplectic group. All projection, kernel, intertwining,
and unitary properties are proved for the unchanged test functions. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Weil.Local.UnitaryInner.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerKernel.CM

theorem unitary (n : ℕ) (g : Real.SchrodingerAction.CM.RealMp n) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) :
    (∫ x, (Real.SchrodingerAction.CM.action n g f).val x * star ((Real.SchrodingerAction.CM.action n g h).val x)) =
      ∫ x, f.val x * star (h.val x) := by
  have he := RepresentationTheory.Weil.Local.UnitaryInner.Construction.energy_preserving_inner ℝ n (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g).toLinearMap
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation_unitary ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g) (Real.SchwartzComparison.CM.tests n h) (Real.SchwartzComparison.CM.tests n f)
  rw [RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2_inner, RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2_inner] at he
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) volume,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure] at he
  let c := Measure.addHaarScalarFactor (RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) volume
  have hc : (c : ℝ) ≠ 0 := by
    exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) volume).ne'
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  change (c : ℂ) * (∫ x, (Real.SchrodingerAction.CM.action n g f).val x * star ((Real.SchrodingerAction.CM.action n g h).val x)) =
    (c : ℂ) * (∫ x, f.val x * star (h.val x)) at he
  exact mul_left_cancel₀ hc' he

def realCover (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (Real.SchrodingerAction.CM.RealMp n) where
  project := Real.SchrodingerAction.CM.projection n
  action := Real.SchrodingerAction.CM.action n
  surjective := Real.SchrodingerAction.CM.projection_surjective n
  negOne := Real.SchrodingerKernel.CM.negOne n
  negOne_ne_one := Real.SchrodingerKernel.CM.negOne_ne_one n
  project_negOne := Real.SchrodingerKernel.CM.project_negOne n
  kernel := Real.SchrodingerKernel.CM.kernel n
  genuine := Real.SchrodingerKernel.CM.genuine n
  faithful := Real.SchrodingerKernel.CM.faithful n
  intertwines := Real.SchrodingerAction.CM.action_intertwines n
  unitary := CM.unitary n

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.RealCover.CM
