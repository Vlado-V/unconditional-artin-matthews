module

public import ArtinMatthews.SpectralPlaneSobolevPointwise
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

/-! The compact-support two-dimensional Sobolev estimate in the actual L2 norm. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace ArtinMatthews

theorem spectral_L2_integral_norm_le_indicator_norm
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : Lp ℝ 2 μ)
    {K : Set X} (hK : MeasurableSet K) (hKf : μ K ≠ ⊤)
    (hs : ∀ᵐ x ∂μ, x ∉ K → u x = 0) :
    (∫ x, ‖u x‖ ∂μ) ≤ ‖indicatorConstLp 2 hK hKf (1:ℝ)‖*‖u‖ := by
  let v := (Lp.memLp u).norm.toLp (fun x => ‖u x‖)
  have hv : v =ᵐ[μ] fun x => ‖u x‖ := (Lp.memLp u).norm.coeFn_toLp
  have hvn : ‖v‖ = ‖u‖ := by
    rw [Lp.norm_toLp,Lp.norm_def,eLpNorm_norm _ (Lp.aestronglyMeasurable u)]
  have he : inner ℝ (indicatorConstLp 2 hK hKf (1:ℝ)) v = ∫ x, ‖u x‖ ∂μ := by
    rw [L2.inner_indicatorConstLp_one]
    calc
      (∫ x in K, v x ∂μ) = ∫ x in K, ‖u x‖ ∂μ := integral_congr_ae (ae_restrict_of_ae hv)
      _ = ∫ x, ‖u x‖ ∂μ := setIntegral_eq_integral_of_ae_compl_eq_zero
        (hs.mono fun x hx hxK => by rw [hx hxK,norm_zero])
  rw [← he]
  exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans_eq (by rw [hvn]))

def spectralPlaneMixedLp (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  ((spectralPlaneDy_smooth (spectralPlaneDx_smooth hF)).continuous.memLp_of_hasCompactSupport
    (spectralPlaneDy_compact (spectralPlaneDx_compact hcF))).toLp
      (spectralPlaneDy (spectralPlaneDx F))

theorem spectralPlane_compact_sobolev_bound {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
      (hcF : HasCompactSupport F), tsupport F ⊆ K → ∀ p,
      ‖F p‖ ≤ C*‖spectralPlaneMixedLp F hF hcF‖ := by
  let I : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
    indicatorConstLp 2 hK.measurableSet (hK.measure_lt_top (μ := volume)).ne (1:ℝ)
  refine ⟨‖I‖+1,by positivity,?_⟩
  intro F hF hcF hs p
  let H := spectralPlaneDy (spectralPlaneDx F)
  let u := spectralPlaneMixedLp F hF hcF
  have hu : u =ᵐ[volume] H := MemLp.coeFn_toLp _
  have hHs : tsupport H ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (0,1)).trans
      ((tsupport_fderiv_apply_subset ℝ (1,0)).trans hs)
  have hb := spectral_L2_integral_norm_le_indicator_norm volume u hK.measurableSet
    (hK.measure_lt_top (μ := volume)).ne (hu.mono fun x hx hxK => by
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport (fun hxH => hxK (hHs hxH)))
  have hi : (∫ x, ‖H x‖) = ∫ x, ‖u x‖ :=
    integral_congr_ae (hu.mono fun _ hx => congrArg norm hx.symm)
  calc
    ‖F p‖ ≤ ∫ x, ‖H x‖ := spectralPlane_pointwise_le_mixed_integral hF hcF p
    _ ≤ ‖I‖*‖u‖ := hi ▸ hb
    _ ≤ (‖I‖+1)*‖u‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end ArtinMatthews
