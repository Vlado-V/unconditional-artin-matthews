module

public import ArtinMatthews.SpectralEisensteinOutgoingApproximation
public import ArtinMatthews.SpectralEisensteinCompactProfile
public import ArtinMatthews.SpectralEisensteinCompactForcing
public import ArtinMatthews.SpectralEisensteinCutoffRegularity
public import ArtinMatthews.SpectralEisensteinProfileLocalFinite
public import ArtinMatthews.SpectralModularGradientChart
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

/-! Compact outgoing approximants eventually agree with the literal
Eisenstein cutoff on a neighborhood of every point. This identifies
the gradient limit as the actual spatial gradient. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0CuspOutgoingApprox_eventually_germ (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (z : UpperHalfPlane) :
    ∀ᶠ n : ℕ in atTop,
      gamma0CuspHeightProfile N a (eisensteinOutgoingApprox q (((n+1:ℕ):ℝ)⁻¹)) =ᶠ[𝓝 z]
        gamma0CuspEisensteinCutoff N a q := by
  classical
  obtain ⟨K,hK,hz⟩ := exists_compact_mem_nhds z
  let H := cuspEisensteinNormalizedHeight N 1 a
  have hfin := cuspEisensteinHeight_compact_finite N 1 a zero_lt_one hK
  let T := hfin.toFinset
  have hb (v : Gamma0CuspEisensteinRows N 1 a) : ∃ M : ℝ, ∀ w ∈ K, H v w≤M := by
    obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn
      (cuspEisensteinNormalizedHeight_continuous N 1 a v).continuousOn
    refine ⟨M,fun w hw => ?_⟩
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM w hw)
  choose M hM using hb
  let B : ℝ := ∑ v ∈ T, max (M v) 0
  obtain ⟨k,hk⟩ := exists_nat_ge B
  filter_upwards [eventually_ge_atTop k] with n hn
  filter_upwards [hz] with w hw
  rw [gamma0CuspEisensteinCutoff_eq_profile]
  unfold gamma0CuspHeightProfile
  congr 1
  apply finsum_congr
  intro v
  change eisensteinOutgoingApprox q (((n+1:ℕ):ℝ)⁻¹) (H v w) = eisensteinVerticalCutoffMode q (H v w)
  by_cases hv : H v w≤1
  · rw [eisensteinOutgoingApprox_zero_low q _ hv,eisensteinVerticalCutoffMode_zero q hv]
  · have hvT : v∈T := hfin.mem_toFinset.mpr ⟨w,hw,(lt_of_not_ge hv).le⟩
    have hB : H v w≤B :=
      (hM v w hw).trans ((le_max_left _ _).trans (Finset.single_le_sum (fun i _ => le_max_right (M i) 0) hvT))
    have hN : (0:ℝ)<(n+1:ℕ) := by positivity
    have hkn : (k:ℝ)≤(n+1:ℕ) := by exact_mod_cast hn.trans (Nat.le_succ n)
    have h : (((n+1:ℕ):ℝ)⁻¹)*H v w≤1 := by
      simpa only [div_eq_mul_inv,mul_comm] using (div_le_one hN).mpr (hB.trans (hk.trans hkn))
    simp only [eisensteinOutgoingApprox,eisensteinVerticalCutoffMode,eisensteinHeightCutoff_zero h,
      sub_zero,mul_one]

theorem gamma0CuspOutgoingApprox_eventually_value (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (z : UpperHalfPlane) :
    ∀ᶠ n : ℕ in atTop,
      gamma0CuspHeightProfile N a (eisensteinOutgoingApprox q (((n+1:ℕ):ℝ)⁻¹)) z =
        gamma0CuspEisensteinCutoff N a q z := by
  filter_upwards [gamma0CuspOutgoingApprox_eventually_germ N a q z] with n hn
  exact hn.eq_of_nhds

theorem gamma0CuspOutgoingApprox_eventually_gradient (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (z : UpperHalfPlane) :
    ∀ᶠ n : ℕ in atTop,
      h2SectionGradient (gamma0CuspHeightProfile N a (eisensteinOutgoingApprox q (((n+1:ℕ):ℝ)⁻¹))) z =
        h2SectionGradient (gamma0CuspEisensteinCutoff N a q) z := by
  filter_upwards [gamma0CuspOutgoingApprox_eventually_germ N a q z] with n hn
  exact h2SectionGradient_congr_of_eventuallyEq _ _ z hn

end ArtinMatthews
