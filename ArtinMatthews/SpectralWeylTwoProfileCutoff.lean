module

public import ArtinMatthews.SpectralWeylHeightCutoff
public import ArtinMatthews.SpectralWeylWeightedMoment
public import ArtinMatthews.SpectralWeylPowerNorm
public import ArtinMatthews.SpectralWeylTwoProfileBound
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The second exhausting cutoff also converges in the actual orbital
integral under the proved weighted moment condition. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

theorem spectralWeylPhysicalMoment_mono (B : ℝ) (f g : ℝ → ℂ)
    (hf : Measurable f)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure)
    (hfg : ∀ x, 0 < x → ‖f x‖ ≤ ‖g x‖) :
    Integrable (fun x : ℝ => x^(-B)*‖f x‖) spectralKLPhysicalMeasure ∧
      spectralWeylPhysicalMoment B f ≤ spectralWeylPhysicalMoment B g := by
  have hmf : Measurable (fun x : ℝ => x^(-B)*‖f x‖) := by fun_prop
  have hle : ∀ᵐ x ∂spectralKLPhysicalMeasure, x^(-B)*‖f x‖ ≤ x^(-B)*‖g x‖ := by
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    exact mul_le_mul_of_nonneg_left (hfg x hx) (Real.rpow_nonneg hx.le _)
  have hi : Integrable (fun x : ℝ => x^(-B)*‖f x‖) spectralKLPhysicalMeasure := by
    apply hMoment.mono' hmf.aestronglyMeasurable
    filter_upwards [hle,spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx hpos
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hpos.le _) (norm_nonneg _))]
    exact hx
  exact ⟨hi,integral_mono_ae hi hMoment hle⟩

theorem spectralWeylPhysicalMoment_cutoff (B a : ℝ) (K : ℕ) (g : ℝ → ℂ)
    (hg : Measurable g)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure) :
    Integrable (fun x : ℝ => x^(-B)*‖spectralWeylProfileCutoff a K g x‖) spectralKLPhysicalMeasure ∧
      spectralWeylPhysicalMoment B (spectralWeylProfileCutoff a K g) ≤ spectralWeylPhysicalMoment B g :=
  spectralWeylPhysicalMoment_mono B _ g (spectralWeylProfileCutoff_measurable a K g hg)
    hMoment (fun x _ => spectralWeylProfileCutoff_norm_le a K g x)

theorem spectralWeylPhysicalBilinear_uniform_dominated_moment {B M : ℝ}
    (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M) (G : ℝ → ℂ)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖G x‖) spectralKLPhysicalMeasure) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X, 0 < X → ∀ s t : ℝ, ∀ f g : ℝ → ℂ,
      Measurable f → Measurable g → (∀ z, 0 < z → ‖f z‖ ≤ M*z^B) →
      (∀ x, 0 < x → ‖g x‖ ≤ ‖G x‖) →
      ‖spectralWeylPhysicalBilinear s t f g X‖ ≤ D*X^(2*B-1) := by
  let U := ∫ u in Ioo (0 : ℝ) 1, (1-u)^(B-1)
  let J := spectralWeylPhysicalMoment B G*U
  have hU : 0 ≤ U :=
    setIntegral_nonneg measurableSet_Ioo (fun u hu => Real.rpow_nonneg (by linarith [hu.2]) _)
  have hJ : 0 ≤ J := mul_nonneg (spectralWeylPhysicalMoment_nonneg B G) hU
  refine ⟨4*M/4^B*J,by positivity,?_⟩
  intro X hX s t f g hfm hgm hf hg
  obtain ⟨hmg,hJg⟩ := spectralWeylPhysicalMoment_mono B g G hgm hMoment hg
  calc
    _ ≤ ((4/X)*M*(X^2/4)^B)*(spectralWeylPhysicalMoment B g*U) :=
      (spectralWeylPhysicalBilinear_moment_bound hX hB hB₁ hM s t f g hfm hgm hmg hf).2.2
    _ ≤ ((4/X)*M*(X^2/4)^B)*J :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJg hU) (by positivity)
    _ = _ := by simpa only [mul_one] using spectralWeyl_power_prefactor hX zero_lt_one B M J

theorem spectralWeylFoldDensity_cutoff_right_norm (a : ℝ) (K : ℕ) (s t X : ℝ)
    (f g : ℝ → ℂ) (q : ℝ × ℝ) :
    ‖spectralWeylFoldDensity s t f (spectralWeylProfileCutoff a K g) X q‖ ≤
      ‖spectralWeylFoldDensity s t f g X q‖ := by
  simp only [spectralWeylFoldDensity,norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_left (spectralWeylProfileCutoff_norm_le a K g q.1) (by positivity)

theorem spectralWeylFoldDensity_cutoff_right_tendsto {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (s t X u : ℝ) (f g : ℝ → ℂ) :
    Tendsto (fun K : ℕ => spectralWeylFoldDensity s t f (spectralWeylProfileCutoff a K g) X (x,u))
      atTop (𝓝 (spectralWeylFoldDensity s t f g X (x,u))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [spectralHeightAnnularPartial_eventually_one (mul_pos ha hx)] with K hK
  simp only [spectralWeylFoldDensity,spectralWeylProfileCutoff,hK,Complex.ofReal_one,one_mul]

theorem spectralWeylPhysicalBilinear_cutoff_right_tendsto {a X B M : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Tendsto (fun K : ℕ => spectralWeylPhysicalBilinear s t f (spectralWeylProfileCutoff a K g) X)
      atTop (𝓝 (spectralWeylPhysicalBilinear s t f g X)) := by
  have hI := (spectralWeylPhysicalBilinear_moment_bound hX hB hB₁ hM s t f g hfm hgm hMoment hf).1
  have hconv : Tendsto (fun K : ℕ => spectralWeylFoldBilinear s t f (spectralWeylProfileCutoff a K g) X)
      atTop (𝓝 (spectralWeylFoldBilinear s t f g X)) := by
    apply tendsto_integral_of_dominated_convergence (fun q => ‖spectralWeylFoldDensity s t f g X q‖)
    · intro K
      exact (spectralWeylFoldDensity_measurable s t X f _ hfm
        (spectralWeylProfileCutoff_measurable a K g hgm)).aestronglyMeasurable
    · exact hI.norm
    · intro K
      exact Eventually.of_forall (spectralWeylFoldDensity_cutoff_right_norm a K s t X f g)
    · have hp : ∀ᵐ q ∂spectralWeylFoldMeasure, 0 < q.1 := by
        unfold spectralWeylFoldMeasure
        apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
        filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
        exact Eventually.of_forall (fun _ => hx)
      filter_upwards [hp] with q hq
      exact spectralWeylFoldDensity_cutoff_right_tendsto ha hq s t X q.2 f g
  have he : ∀ K : ℕ, spectralWeylPhysicalBilinear s t f (spectralWeylProfileCutoff a K g) X =
      spectralWeylFoldBilinear s t f (spectralWeylProfileCutoff a K g) X := by
    intro K
    exact spectralWeylPhysicalBilinear_fold hX s t f _ hfm
      (spectralWeylProfileCutoff_measurable a K g hgm)
      (spectralWeylPhysicalBilinear_moment_bound hX hB hB₁ hM s t f _ hfm
        (spectralWeylProfileCutoff_measurable a K g hgm)
        (spectralWeylPhysicalMoment_cutoff B a K g hgm hMoment).1 hf).1
  rw [funext he,spectralWeylPhysicalBilinear_fold hX s t f g hfm hgm hI]
  exact hconv

end ArtinMatthews
