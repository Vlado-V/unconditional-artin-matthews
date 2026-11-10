module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance
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
public import Mathlib.Topology.MetricSpace.Ultra.Pi
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUltra
public import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest


set_option backward.privateInPublic true
@[expose] public section

/-! # Ultra Weyl Coefficients -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraWeylCoefficients.Construction

noncomputable section

/-! The nonarchimedean Weyl matrix coefficient is locally constant and
is a Fourier transform in the momentum coordinate. -/

open _root_.MeasureTheory _root_.Topology Filter
open scoped BigOperators ComplexConjugate

theorem weylMatrixCoefficient_fourier
    {F : Type} [NormedField F] [MeasurableSpace F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d))
    (f h : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h v =
      ψ (-Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phaseMomentum v) ((2 : F)⁻¹ • FourierCovariance.Construction.phasePosition v)) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun x => f (x - FourierCovariance.Construction.phasePosition v) * conj (h x)) (-FourierCovariance.Construction.phaseMomentum v) := by
  unfold WeylMatrixCoefficients.Construction.weylMatrixCoefficient Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [FourierCovariance.Construction.heisenbergFunction_dot]
    have hp : Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phaseMomentum v) (x - (2 : F)⁻¹ • FourierCovariance.Construction.phasePosition v) =
        -Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phaseMomentum v) ((2 : F)⁻¹ • FourierCovariance.Construction.phasePosition v) + Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phaseMomentum v) x := by
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    have hn : -Local.FunctionsMetaplectic.Construction.dot (-FourierCovariance.Construction.phaseMomentum v) x = Local.FunctionsMetaplectic.Construction.dot (FourierCovariance.Construction.phaseMomentum v) x := by simp [Local.FunctionsMetaplectic.Construction.dot]
    rw [hp, hn, ψ.map_add_eq_mul]
    ring

theorem weylMatrixCoefficient_locallyConstant_ultra
    {F : Type} [NormedField F] [LocallyCompactSpace F] [IsUltrametricDist F]
    [MeasurableSpace F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    IsLocallyConstant (WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val) := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  obtain ⟨hfl, -⟩ := UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
  obtain ⟨hhl, hhs⟩ := UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp h.property
  let k : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.Position F d → ℂ :=
    fun p => Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ p.1 f.val p.2 * conj (h.val p.2)
  have hphase : Continuous (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.Position F d =>
      ∑ i, p.1 (Sum.inr i) * (p.2 i - p.1 (Sum.inl i) / 2)) := by fun_prop
  have hshift : Continuous (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace F d × Local.FunctionsMetaplectic.Construction.Position F d =>
      fun i => p.2 i - p.1 (Sum.inl i)) := by fun_prop
  have hk : IsLocallyConstant k := by
    unfold k Local.FunctionsMetaplectic.Construction.heisenbergFunction
    exact (((LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous hphase).mul
      (hfl.comp_continuous hshift)).mul ((hhl.comp_continuous continuous_snd).comp conj)
  exact FourierUltra.Construction.locallyConstant_integral_of_uniform_compact_support μ k hk (tsupport h.val) hhs
    (fun v x hx => by simp only [k, image_eq_zero_of_notMem_tsupport hx, map_zero, mul_zero])

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraWeylCoefficients.Construction
