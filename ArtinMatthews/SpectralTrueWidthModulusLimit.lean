module

public import ArtinMatthews.SpectralTrueWidthPhysicalSummability
public import ArtinMatthews.SpectralWeylHeightCutoff
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
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

/-! The literal exhausting height cutoffs pass through the full actual
true-width Kloosterman series. The common summable majorant follows from
the determinant count and the physical profile's positive power. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology MatrixGroups
namespace ArtinMatthews

theorem gamma0TrueWidthPhysicalFibre_cutoff_tendsto (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : Ioi (0 : ℕ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {a B M : ℝ} (ha : 0 < a) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Tendsto (fun K : ℕ => gamma0TrueWidthPhysicalFibre N r s c m n
      (spectralWeylProfileCutoff a K f) g) atTop
        (𝓝 (gamma0TrueWidthPhysicalFibre N r s c m n f g)) := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hq₁ : 0 < |cuspFourierFrequency 1 m| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hq₂ : 0 < |cuspFourierFrequency 1 n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hC := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  have hX : 0 < Real.sqrt (|cuspFourierFrequency 1 m| * |cuspFourierFrequency 1 n|)*
      (2/gamma0TrueWidthModulus N r s (c.val : ℝ)) := by positivity
  have h := spectralWeylPhysicalBilinear_cutoff_tendsto ha hX hB hB₁ hM
    (cuspFourierFrequency 1 m/|cuspFourierFrequency 1 m|)
    (cuspFourierFrequency 1 n/|cuspFourierFrequency 1 n|) f g hfm hg hgc hgp hf
  exact tendsto_const_nhds.mul h

theorem gamma0TrueWidthPhysicalSeries_cutoff_tendsto (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {a B M : ℝ} (ha : 0 < a) (hB : 1/2 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Tendsto (fun K : ℕ => ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
      (spectralWeylProfileCutoff a K f) g) atTop
        (𝓝 (∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n f g)) := by
  obtain ⟨L,_,hL⟩ := gamma0TrueWidthPhysicalFibre_uniform_bound N r s m n hm hn
    (by linarith) hB₁ hM g hg hgc hgp
  have hp : Summable (fun c : ℕ => 1/(c : ℝ)^(2*B)) := Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hs := (hp.mul_left L).subtype (fun c : ℕ => 0 < c)
  apply tendsto_tsum_of_dominated_convergence hs
  · intro c
    exact gamma0TrueWidthPhysicalFibre_cutoff_tendsto N r s c m n hm hn ha
      (by linarith) hB₁ hM f g hfm hg hgc hgp hf
  · filter_upwards with K c
    simpa only [mul_one_div,Function.comp_def] using hL (spectralWeylProfileCutoff a K f)
      (spectralWeylProfileCutoff_measurable a K f hfm)
      (fun z hz => (spectralWeylProfileCutoff_norm_le a K f z).trans (hf z hz)) c

end ArtinMatthews
