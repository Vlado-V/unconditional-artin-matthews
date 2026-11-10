module

public import ArtinMatthews.SpectralPeterssonCutPeriodization
public import ArtinMatthews.SpectralPeterssonFourierAtHeight
public import ArtinMatthews.SpectralPeterssonGammaTail
public import ArtinMatthews.SpectralHyperbolicBochnerCoordinates
public import ArtinMatthews.SpectralPeterssonCutStripIntegrable
public import ArtinMatthews.SpectralPeterssonReproducing
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

/-! The true sharp-cut pairing reproduces the Fourier coefficient with
its incomplete-Gamma mass. The argument covers weight two directly. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralPeterssonCutStrip_reproduce (k : ℕ) (hk : 2 ≤ k) (n : ℕ+)
    (A : ℝ) (hA : 0 < A) (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ)
    (hbd : ∀ z, ‖F z‖*z.im^((k : ℝ)/2) ≤ M) (b : ℂ)
    (hb : ∀ (y : ℝ) (hy : 0 < y), spectralPeterssonFourierAtHeight F n y hy = b) :
    (∫ z, UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed n A) F z) =
      (spectralPeterssonTruncatedMass k n A : ℂ)*b := by
  let δ := A/(4*Real.pi*(n : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let S := (Ioc (0 : ℝ) 1) ×ˢ Ioi δ
  let G := spectralPeterssonStripCoordinates k n F
  let I (p : ℝ × ℝ) := (p.2^2)⁻¹ • G p
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioi
  have hpos : S ⊆ {p : ℝ × ℝ | 0 < p.2} := fun _ hp => hδ.trans hp.2
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re,z.im) ∈ S} := hS.preimage (by fun_prop)
  rw [spectralPeterssonCutStrip_coordinates]
  change (∫ z, ({z : UpperHalfPlane | (z.re,z.im) ∈ S}.indicator
    (fun z : UpperHalfPlane => G (z.re,z.im))) z) = _
  rw [integral_indicator hpre,upperHalfPlane_setIntegral_coordinates_smul G hS hpos]
  have hInt : IntegrableOn I S (volume.prod volume) :=
    spectralPeterssonCutCoordinates_weighted_integrable k hk n δ hδ F hF M hbd
  change (∫ p in S, I p ∂(volume.prod volume)) = _
  rw [← Measure.prod_restrict]
  have hInt' : Integrable I ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioi δ))) := by
    rw [Measure.prod_restrict]
    exact hInt
  rw [integral_prod_symm I hInt']
  calc
    _ = ∫ y in Ioi δ, ((y^(k-2)*Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℝ) : ℂ)*b := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hy0 : 0 < y := hδ.trans hy
      exact (spectralPeterssonStripCoordinate_slice k hk n F y hy0).trans (by rw [hb y hy0])
    _ = _ := by
      rw [integral_mul_const,integral_complex_ofReal]
      rfl

end ArtinMatthews
