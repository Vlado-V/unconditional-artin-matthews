module

public import ArtinMatthews.SpectralCuspEisensteinConstantTerm
public import ArtinMatthews.SpectralCuspEisensteinPositiveIntegral
public import ArtinMatthews.SpectralEisensteinPositiveMeanBound
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

/-! Genuine all-cusp decay of the positive-row part, obtained from its exact
constant term and a direct rowwise comparison. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspEisensteinPositivePart (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  (gamma0CuspTrueWidth N a:ℂ)^(-s)*
    ∑' v : CuspEisensteinPositiveRows N r a,
      cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y hy x)

theorem cuspEisensteinPositive_integral_norm_bound (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (gamma0CuspTrueWidth N a:ℝ)^(-s.re)*
      (∑' v : CuspEisensteinPositiveRows N r a, ∫ t in Ioc (0:ℝ) 1,
        ‖cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y hy t)‖) ≤
      y^(1-s.re)*‖gamma0CuspScattering N r a (s.re:ℂ)‖ := by
  have hsR : 1 < (s.re:ℂ).re := hs
  have hsum := cuspEisensteinPositiveIntegral_summable N r a (s.re:ℂ) hsR y hy
  have he := cuspEisensteinPositiveIntegral_dirichlet N r a (s.re:ℂ) hsR y hy
  have hcomplex : (gamma0CuspTrueWidth N a:ℂ)^(-(s.re:ℂ))*
      (∑' v : CuspEisensteinPositiveRows N r a,
        cuspEisensteinRowIntegral N r a (s.re:ℂ) y hy v.val)=
      (y:ℂ)^(1-(s.re:ℂ))*gamma0CuspScattering N r a (s.re:ℂ) := by
    rw [he]
    unfold gamma0CuspScattering
    ring
  have hw : (gamma0CuspTrueWidth N a:ℂ)^(-(s.re:ℂ))=
      (((gamma0CuspTrueWidth N a:ℝ)^(-s.re):ℝ):ℂ) := by
    simpa only [Complex.ofReal_natCast,Complex.ofReal_neg] using
      (Complex.ofReal_cpow (show (0:ℝ) ≤ gamma0CuspTrueWidth N a by positivity) (-s.re)).symm
  have hreal := congrArg Complex.re hcomplex
  rw [hw,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hreal
  have hsumR : (∑' v : CuspEisensteinPositiveRows N r a, ∫ t in Ioc (0:ℝ) 1,
      ‖cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y hy t)‖)=
      (∑' v : CuspEisensteinPositiveRows N r a,
        cuspEisensteinRowIntegral N r a (s.re:ℂ) y hy v.val).re := by
    simp_rw [cuspEisensteinRowIntegral_norm_eq_re]
    exact (Complex.re_tsum hsum).symm
  rw [hsumR,hreal]
  calc
    _ ≤ ‖(y:ℂ)^(1-(s.re:ℂ))*gamma0CuspScattering N r a (s.re:ℂ)‖ := Complex.re_le_norm _
    _=_ := by
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simp only [Complex.sub_re,Complex.one_re,Complex.ofReal_re]

theorem gamma0CuspEisensteinPositivePart_decay (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (x y : ℝ) (hy : 1 ≤ y) (hx : |x| ≤ 1) :
    ‖gamma0CuspEisensteinPositivePart N r a s y (lt_of_lt_of_le zero_lt_one hy) x‖ ≤
      9^s.re*y^(1-s.re)*‖gamma0CuspScattering N r a (s.re:ℂ)‖ := by
  let py := lt_of_lt_of_le zero_lt_one hy
  have hnorm := (cuspEisensteinRowTerm_summable_norm N r a s hs
    (cuspEisensteinTargetPoint N r y py x)).comp_injective
      (i := fun v : CuspEisensteinPositiveRows N r a => v.val) Subtype.coe_injective
  have hint := (cuspEisensteinRowIntegral_norm_summable N r a s hs y py).comp_injective
    (i := fun v : CuspEisensteinPositiveRows N r a => v.val) Subtype.coe_injective
  have hmean := hnorm.tsum_le_tsum
    (fun v => cuspEisensteinPositiveRow_mean_bound N r a s hs v x y hy hx) (hint.mul_left (9^s.re))
  rw [tsum_mul_left] at hmean
  unfold gamma0CuspEisensteinPositivePart
  rw [norm_mul,Complex.norm_natCast_cpow_of_pos (gamma0CuspTrueWidth_pos N a)]
  change (gamma0CuspTrueWidth N a:ℝ)^(-s.re)*‖∑' v : CuspEisensteinPositiveRows N r a,
    cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y py x)‖ ≤ _
  calc
    _ ≤ (gamma0CuspTrueWidth N a:ℝ)^(-s.re)*(∑' v : CuspEisensteinPositiveRows N r a,
        ‖cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y py x)‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) (by positivity)
    _ ≤ (gamma0CuspTrueWidth N a:ℝ)^(-s.re)*(9^s.re*
        (∑' v : CuspEisensteinPositiveRows N r a, ∫ t in Ioc (0:ℝ) 1,
          ‖cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y py t)‖)) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _=9^s.re*((gamma0CuspTrueWidth N a:ℝ)^(-s.re)*
        (∑' v : CuspEisensteinPositiveRows N r a, ∫ t in Ioc (0:ℝ) 1,
          ‖cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y py t)‖)) := by ring
    _ ≤ 9^s.re*(y^(1-s.re)*‖gamma0CuspScattering N r a (s.re:ℂ)‖) :=
      mul_le_mul_of_nonneg_left (cuspEisensteinPositive_integral_norm_bound N r a s hs y py) (by positivity)
    _=_ := by ring

end ArtinMatthews
