module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralPeterssonStripIntegrable
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The positive-height cut makes the Petersson Gamma envelope integrable
at weight two as well as every higher weight. -/
noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralPeterssonCutGammaEnvelope_integrable (k : ℕ) (hk : 2 ≤ k)
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) :
    IntegrableOn (fun y : ℝ => y^((k : ℝ)/2-2)*Real.exp (-(r*y))) (Ioi δ) := by
  by_cases hk3 : 3 ≤ k
  · have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    have hi := spectralPetersson_gammaEnvelope_integrable ((k : ℝ)/2-1) r (by linarith) hr
    have he : (k : ℝ)/2-1-1 = (k : ℝ)/2-2 := by ring
    rw [he] at hi
    exact hi.mono_set (Ioi_subset_Ioi hδ.le)
  · have hk2 : k = 2 := by omega
    subst k
    have hexp : IntegrableOn (fun y : ℝ => Real.exp (-(r*y))) (Ioi δ) := by
      simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -r) (by linarith) δ
    have hbase := hexp.const_mul δ⁻¹
    apply hbase.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hδ.trans hy
    norm_num only [Nat.cast_ofNat,show (2 : ℝ)/2-2 = -1 by norm_num,Real.rpow_neg_one]
    rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hy0.le) (Real.exp_nonneg _))]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ hy.le) (Real.exp_nonneg _)

end ArtinMatthews
