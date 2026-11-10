module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients
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
public import OAI.RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis
public import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraWeylCoefficients
public import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd


set_option backward.privateInPublic true
@[expose] public section

/-! # Weak Weyl Gaussian -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian.Construction

noncomputable section

/-! An absolutely convergent weak Gaussian transform of Weyl matrix
coefficients. This uses the actual Schrödinger action on test functions. -/

open _root_.MeasureTheory _root_.Topology

def weakWeylGaussian
    {F : Type} [NormedField F] [MeasurableSpace F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d))
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (f h : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) : ℂ :=
  ∫ v, ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h v ∂ν

theorem weakWeylGaussian_integrable_ultra
    {F : Type} [NormedField F] [LocallyCompactSpace F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hn : ∃ a : F, ψ a ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (hq : Continuous q) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Integrable (fun v => ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v) ν := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  have hc' := (hc.comp hq).mul (UltraWeylCoefficients.Construction.weylMatrixCoefficient_locallyConstant_ultra hF ψ hc μ f h).continuous
  exact hc'.integrable_of_hasCompactSupport
    (WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn μ f h).mul_left

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian.Construction
