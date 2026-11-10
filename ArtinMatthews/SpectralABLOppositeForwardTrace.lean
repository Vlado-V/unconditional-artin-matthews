module

public import ArtinMatthews.SpectralABLOppositeKWeight
public import ArtinMatthews.SpectralABLOppositeModulus
public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralABLOppositeBareSpectrum
public import ArtinMatthews.SpectralABLOppositeHeatTrace
public import ArtinMatthews.SpectralBareTestDominance
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff Topology
noncomputable section

/-- The opposite-sign forward formula for a real compact spatial test,
with the source check transform and the exact native quarter factor. -/
theorem gamma0ABLOpposite_forward_trace_real (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (hchart : r = s ∨ ¬ gamma0EisensteinCuspsEquivalent N r s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m*n < 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hr : ∀ x, star (f x) = f x) :
    let h := spectralABLOppositeEnergyTest f hf hc hp
    Summable (fun c : Ioi (0 : ℕ) => gamma0ABLOppositeGeometricTerm N r s c m n f) ∧
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
    IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) ∧
    gamma0BareSourceSpectralSide N h r s Y hY m n hm hn =
      (1/(4*(Real.pi : ℂ)))*(∑' c : Ioi (0 : ℕ), gamma0ABLOppositeGeometricTerm N r s c m n f) := by
  let h := spectralABLOppositeEnergyTest f hf hc hp
  obtain ⟨hC,hI⟩ := gamma0OppositeBareSpectrum_integrable N r s Y hY m n hm hn f hf hc hp
  obtain ⟨hG,hLim⟩ := gamma0TrueWidthOppositeHeatSeries_tendsto N r s m n hm hn hmn f hf hc hp
  refine ⟨hG,hC,hI,?_⟩
  change gamma0BareSourceSpectralSide N h r s Y hY m n hm hn = _
  calc
    _ = (1/4 : ℂ)*((∑' c : Ioi (0 : ℕ), gamma0ABLOppositeGeometricTerm N r s c m n f)/
        (Real.pi : ℂ)) := by
      apply tendsto_nhds_unique (gamma0HeatSourceSpectralSide_tendsto_of_bare N h r s Y hY m n hm hn hC hI)
      apply (hLim.const_mul (1/4 : ℂ)).congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact (gamma0HeatOpposite_source_trace N r s hchart Y hY m n hm hn hmn f hf hc hp hr R hR).symm
    _ = _ := by field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end
end ArtinMatthews
