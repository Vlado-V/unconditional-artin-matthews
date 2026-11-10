module

public import ArtinMatthews.SpectralCuspConstantTermOperator
public import ArtinMatthews.SpectralCuspConstantTermHeights
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual horizontal-average projection is the actual constant term
pulled back along cusp height. Vanishing only above a high cusp cutoff
suffices to remove its restricted tail. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem cusp_height_measurePreserving (w Y : ℝ) (hY : 0<Y) :
    MeasurePreserving UpperHalfPlane.im (volume.restrict (hyperbolicCuspStrip w Y))
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
  have hs : MeasurePreserving Prod.snd (cuspStripMeasure w Y)
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) :=
    ⟨measurable_snd,Measure.map_snd_prod⟩
  exact hs.comp (cusp_coordinates_measurePreserving w Y hY)

theorem cuspHyperbolicAverageProjection_ae_constantTerm (w Y : ℝ) (hY : 0<Y)
    (U : CuspHyperbolicL2 w Y) :
    cuspHyperbolicAverageProjection w Y hY U
      =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
        fun z => cuspHyperbolicConstantTerm w Y hY U z.im := by
  rw [cuspHyperbolicAverageProjection_factor_constantTerm]
  have hv : cuspVerticalPullback w Y (cuspHyperbolicConstantTerm w Y hY U)
      =ᵐ[cuspStripMeasure w Y] fun p => cuspHyperbolicConstantTerm w Y hY U p.2 :=
    Lp.coeFn_compMeasurePreserving _ ⟨measurable_snd,Measure.map_snd_prod⟩
  exact (cuspHyperbolicPullback_ae w Y hY _).trans
    ((cusp_coordinates_measurePreserving w Y hY).quasiMeasurePreserving.ae_eq_comp hv)

theorem gamma0CuspEnergyProjection_restricted_zero (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (u : gamma0EnergySpace N) {Y : ℝ} (hY : 1≤Y)
    (hc : gamma0CuspConstantTerm N r Y (zero_lt_one.trans_le hY) (gamma0EnergyInclusion N u)=0) :
    spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (cuspHyperbolicAverageProjection (N:ℝ) 1 zero_lt_one (gamma0CuspEnergyRestriction N r u))=0 := by
  have hP := cuspHyperbolicAverageProjection_ae_constantTerm (N:ℝ) 1 zero_lt_one
    (gamma0CuspMassRestriction N r 1 zero_lt_one (gamma0EnergyInclusion N u))
  rw [gamma0CuspMassRestriction_energy,gamma0CuspHeightRestriction_one] at hP
  have hP' := (Measure.absolutelyContinuous_of_le (spectralCuspHyperbolicMeasure_mono hY)).ae_eq hP
  have hC := gamma0CuspConstantTerm_height_ae N r 1 Y zero_lt_one (zero_lt_one.trans_le hY) hY
    (gamma0EnergyInclusion N u)
  rw [hc] at hC
  have hzero := hC.trans (Lp.coeFn_zero ℂ 2 ((cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y))
  have hz := (cusp_height_measurePreserving (N:ℝ) Y (zero_lt_one.trans_le hY)).quasiMeasurePreserving.ae_eq_comp hzero
  apply Lp.ext
  filter_upwards [spectralLpMeasureRestriction_ae (spectralCuspHyperbolicMeasure_mono hY)
    (cuspHyperbolicAverageProjection (N:ℝ) 1 zero_lt_one (gamma0CuspEnergyRestriction N r u)),
    hP',hz,Lp.coeFn_zero ℂ 2 (volume.restrict (hyperbolicCuspStrip (N:ℝ) Y))]
    with z hr hp hc hz0
  rw [hr,hp]
  have he : cuspHyperbolicConstantTerm (N:ℝ) 1 zero_lt_one
      (gamma0CuspEnergyRestriction N r u) z.im=
      gamma0CuspConstantTerm N r 1 zero_lt_one (gamma0EnergyInclusion N u) z.im := by
    change _=cuspHyperbolicConstantTerm (N:ℝ) 1 zero_lt_one
      (gamma0CuspMassRestriction N r 1 zero_lt_one (gamma0EnergyInclusion N u)) z.im
    rw [gamma0CuspMassRestriction_energy,gamma0CuspHeightRestriction_one]
  rw [he]
  exact hc.trans hz0.symm

end ArtinMatthews
