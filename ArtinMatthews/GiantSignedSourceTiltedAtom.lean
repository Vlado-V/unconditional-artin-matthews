module

public import ArtinMatthews.GiantSignedSourceVisitWeights
public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantTwoSidedLabelOffsets
public import ArtinMatthews.GiantSignedTiltBandBounds
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! A prescribed birth draws an atom of the original tilted harmonic
law. Its bound uses the actual lower edge of the prime bands. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem giantSignedTiltedPrimeLaw_atom_le
    (P : Finset ℕ) {n : ℕ} (visitQ : Fin n → ℝ)
    (hq0 : ∀ i, 0 ≤ visitQ i) (hq1 : ∀ i, visitQ i ≤ 1)
    {vmin Pmin : ℝ} (hvmin : 0 < vmin) (hV : vmin ≤ bandReciprocalMass P)
    (hPmin : 0 < Pmin) (hsmall : (n : ℝ)/Pmin ≤ 1/2)
    (p : P) (hp : Pmin ≤ (p.val : ℝ)) :
    giantSignedTiltedPrimeLaw P visitQ p ≤ (2/vmin)/Pmin := by
  have hVpos := hvmin.trans_le hV
  have hden : 0 < 1 - (n : ℝ)/Pmin := by linarith
  have hd := (giantSignedPrimeDensity_band_bounds visitQ hq0 hq1 Pmin hPmin hp
    (show (n : ℝ)/Pmin < 1 by linarith)).2
  have hTwo : (1 - (n : ℝ)/Pmin)⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hden).mpr (by linarith)
  have ha : markedHarmonicAtom P p ≤ (1/Pmin)/vmin := by
    unfold markedHarmonicAtom
    exact (div_le_div_of_nonneg_right (one_div_le_one_div_of_le hPmin hp) hVpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) hvmin hV)
  rw [giantSignedTiltedPrimeLaw_eq]
  calc
    _ ≤ markedHarmonicAtom P p * 2 :=
      mul_le_mul_of_nonneg_left (hd.trans hTwo) (markedHarmonicAtom_nonneg P hVpos)
    _ ≤ ((1/Pmin)/vmin)*2 := mul_le_mul_of_nonneg_right ha (by norm_num)
    _ = _ := by ring

theorem giantSignedSourceTiltedAtom_eventually
    {q c vmin : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c) (hvmin : 0 < vmin) :
    ∀ᶠ x : ℝ in atTop, ∀ (P : Finset ℕ), vmin ≤ bandReciprocalMass P →
      ∀ p : P, Real.exp ((Real.log x)^c) ≤ (p.val : ℝ) →
      giantSignedTiltedPrimeLaw P
        (giantSignedSourceVisitQ q (giantTwoSidedSourceMomentLength x)) p ≤
          (2/vmin)/Real.exp ((Real.log x)^c) := by
  have ht := (rpow_mul_exp_neg_rpow_tendsto (2 : ℝ) hc
    (by norm_num : (0 : ℝ) < 1)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (5 : ℝ))] with x hx hL5
  intro P hV p hp
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let Pmin := Real.exp (L^c)
  have hPmin : 0 < Pmin := Real.exp_pos _
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hn : ((n+1 : ℕ) : ℝ) ≤ L^(2 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL1 (show (13/25 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at hpow
    have hlen := giantTwoSidedSourceMomentLength_le (x := x) hL1
    change (n : ℝ) ≤ 4*L^(13/25 : ℝ) at hlen
    rw [Nat.cast_add, Nat.cast_one, Real.rpow_two]
    have hh : 5 ≤ L := hL5
    nlinarith [mul_le_mul_of_nonneg_right hh hL0]
  have hsmall : L^(2 : ℝ)/Pmin < 1/2 := by
    simpa only [Function.comp_def, Set.mem_Iio, neg_one_mul, Real.exp_neg, div_eq_mul_inv, L, Pmin]
      using hx
  have hsqrt : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
  exact giantSignedTiltedPrimeLaw_atom_le P (giantSignedSourceVisitQ q n)
    (fun i => (giantSignedSourceVisitQ_bounds hq0 hq1 n i).1)
    (fun i => (giantSignedSourceVisitQ_bounds hq0 hq1 n i).2.trans hsqrt)
    hvmin hV hPmin ((div_le_div_of_nonneg_right hn hPmin.le).trans hsmall.le) p hp

end
end ArtinMatthews
