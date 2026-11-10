module

public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import ArtinMatthews.MarkedMajorArcCoefficientBounds
public import ArtinMatthews.MarkedMajorArcRoughMertens
public import ArtinMatthews.MarkedMajorTypeIIBands
public import ArtinMatthews.MarkedRoughCharacterRange
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original scalar Type-II coefficients supply rough support and a
uniform logarithmic α bound. No bound on a physical endpoint vector is assumed. -/
namespace ArtinMatthews
open Filter Finset

 theorem marked_centered_nonzero_rough (W modulation : ℝ) {n : ℕ}
    (hW : 0 ≤ W) (hn : W < (n:ℝ))
    (hα : markedMajorCenteredCoefficient W modulation n ≠ 0) :
    ∀ p ∈ Nat.primesLE ⌊W⌋₊,¬p∣n := by
  classical
  by_cases hprime : n.Prime
  · intro p hp hdiv
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hpW : (p:ℝ) ≤ W :=
      (show (p:ℝ) ≤ ⌊W⌋₊ by exact_mod_cast (Nat.mem_primesLE.mp hp).1).trans (Nat.floor_le hW)
    have heq := (hprime.dvd_iff_eq hpp.ne_one).mp hdiv
    subst n
    exact (not_lt_of_ge hpW) hn
  · by_contra h
    simp [markedMajorCenteredCoefficient,hprime,h] at hα

 theorem markedMajorTypeII_alpha_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (modulation : ℝ), Real.exp (δ*L) ≤ (n:ℝ) →
      ‖markedMajorCenteredCoefficient (Real.exp (L^(6/25:ℝ))) modulation n‖ ≤ L^2 := by
  let E := Real.exp (Real.eulerMascheroniConstant+1)
  have hE : 0 < E := Real.exp_pos _
  filter_upwards [marked_rough_density_inverse_cutoff (6/25) (by norm_num),
    eventually_ge_atTop (max 1 (max (1/δ) (1+E)))] with L hV hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδL : 1 ≤ δ*L := by
    have hh := (le_max_left (1/δ) (1+E)).trans ((le_max_right _ _).trans hL)
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm L δ)
  have hEL : 1+E ≤ L := (le_max_right (1/δ) (1+E)).trans ((le_max_right _ _).trans hL)
  intro n modulation hn
  have hnpos : 0 < (n:ℝ) := (Real.exp_pos _).trans_le hn
  have hlog : 1 ≤ Real.log n := hδL.trans ((Real.le_log_iff_exp_le hnpos).mpr hn)
  have hnorm := marked_centered_coefficient_norm_le (Real.exp (L^(6/25:ℝ))) modulation
    (by exact_mod_cast hnpos) hlog
  have hp : L^(6/25:ℝ) ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (6/25:ℝ)≤1)
  change (markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))))⁻¹ ≤ E*L^(6/25:ℝ) at hV
  have hh := mul_le_mul_of_nonneg_left hp hE.le
  nlinarith

 theorem markedMajorTypeII_bands_below_rough {I : Type*} [Fintype I]
    (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ)) :
    ∀ᶠ L : ℝ in atTop, ∀ i p,p ∈ markedLogPowerBand (e i) (Real.exp L) →
      p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊ := by
  filter_upwards [markedMajorTypeII_band_data e hinj he 0,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/25)).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (0:ℝ)] with L hb hg hL
  intro i p hp
  have hh := hb.2.1 i p hp
  have hscale : 2*L^(1/(5:ℝ)) ≤ L^(6/25:ℝ) := by
    have hid : (6/25:ℝ)=1/5+1/25 := by norm_num
    rw [hid,Real.rpow_add hL]
    nlinarith [Real.rpow_pos_of_pos hL (1/(5:ℝ))]
  apply Nat.mem_primesLE.mpr
  refine ⟨(Nat.le_floor_iff (Real.exp_nonneg _)).mpr ?_,hh.1⟩
  exact (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hh.1.pos)).mp (hh.2.2.trans hscale)

 theorem markedMajorTypeII_alpha_rough (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (modulation : ℝ), Real.exp (δ*L) ≤ (n:ℝ) →
      markedMajorCenteredCoefficient (Real.exp (L^(6/25:ℝ))) modulation n ≠ 0 →
      ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n := by
  filter_upwards [marked_rough_cutoff_scale (6/25) (δ/2) (by norm_num) (half_pos hδ),
    eventually_gt_atTop (0:ℝ)] with L hW hL
  intro n modulation hn hα
  have hstrict : Real.exp ((δ/2)*L) < Real.exp (δ*L) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact marked_centered_nonzero_rough _ modulation (Real.exp_nonneg _)
    (hW.trans_lt (hstrict.trans_le hn)) hα

end ArtinMatthews
