module

public import ArtinMatthews.SpectralTrueWidthPhysicalSummability
public import ArtinMatthews.SpectralWeylHeightCutoff
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralTrueWidthLinearCount
public import ArtinMatthews.SpectralWeylTwoProfileCutoff
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

/-! The full true-width modulus sum admits a second noncompact profile
through its actual weighted physical moment. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology MatrixGroups
namespace ArtinMatthews

theorem gamma0TrueWidthPhysicalFibre_uniform_moment (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {B M : ℝ} (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (G : ℝ → ℂ)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖G x‖) spectralKLPhysicalMeasure) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ f g : ℝ → ℂ, Measurable f → Measurable g →
      (∀ z, 0 < z → ‖f z‖ ≤ M*z^B) → (∀ x, 0 < x → ‖g x‖ ≤ ‖G x‖) →
      ∀ c : Ioi (0 : ℕ), ‖gamma0TrueWidthPhysicalFibre N r s c m n f g‖ ≤ L/(c.val : ℝ)^(2*B) := by
  obtain ⟨D,hD,hbound⟩ := spectralWeylPhysicalBilinear_uniform_dominated_moment hB hB₁ hM G hMoment
  let a := |cuspFourierFrequency 1 m|
  let b := |cuspFourierFrequency 1 n|
  let K := Real.sqrt (a*b)
  let W := Real.sqrt (gamma0CuspTrueWidth N r : ℝ)*Real.sqrt (gamma0CuspTrueWidth N s : ℝ)
  have ha : 0 < a := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hb : 0 < b := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hK : 0 < K := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hr : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hs : 0 < (gamma0CuspTrueWidth N s : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N s)
  have hW : 0 < W := mul_pos (Real.sqrt_pos.mpr hr) (Real.sqrt_pos.mpr hs)
  have hWsq : W^2 = (gamma0CuspTrueWidth N r : ℝ)*gamma0CuspTrueWidth N s := by
    dsimp only [W]
    rw [mul_pow,Real.sq_sqrt hr.le,Real.sq_sqrt hs.le]
  refine ⟨K*D*(2*K/W)^(2*B-1),by positivity,?_⟩
  intro f g hfm hgm hf hg c
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hc : 0 < (c.val : ℝ) := Nat.cast_pos.mpr c.property
  have hC : 0 < (c.val : ℝ)*W := mul_pos hc hW
  have hS : ‖gamma0TrueWidthKloostermanSum N r s c.val m n‖ ≤ W^2*(c.val : ℝ) := by
    rw [hWsq]
    exact gamma0TrueWidthKloostermanSum_linear_bound N r s c.val m n
  have hF := hbound (K*(2/((c.val : ℝ)*W))) (mul_pos hK (div_pos two_pos hC))
    (cuspFourierFrequency 1 m/a) (cuspFourierFrequency 1 n/b) f g hfm hgm hf hg
  have hmod : gamma0TrueWidthModulus N r s (c.val : ℝ) = (c.val : ℝ)*W := by
    dsimp only [gamma0TrueWidthModulus,W]
    ring
  change ‖gamma0TrueWidthKloostermanSum N r s c.val m n * ((K/(gamma0TrueWidthModulus N r s (c.val : ℝ))^2 : ℝ) : ℂ) *
    spectralWeylPhysicalBilinear (cuspFourierFrequency 1 m/a) (cuspFourierFrequency 1 n/b)
      f g (K*(2/gamma0TrueWidthModulus N r s (c.val : ℝ)))‖ ≤ _
  rw [hmod,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (W^2*(c.val : ℝ))*(K/((c.val : ℝ)*W)^2)*
        (D*(K*(2/((c.val : ℝ)*W)))^(2*B-1)) := by gcongr
    _ = _ := spectralWeyl_modulus_power_factor hc hK hW B D

theorem gamma0TrueWidthPhysicalFibre_moment_summable (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {B M : ℝ} (hB : 1/2 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Summable (fun c : Ioi (0 : ℕ) => gamma0TrueWidthPhysicalFibre N r s c m n f g) := by
  obtain ⟨L,_,hL⟩ := gamma0TrueWidthPhysicalFibre_uniform_moment N r s m n hm hn
    (by linarith) hB₁ hM g hMoment
  have hp : Summable (fun c : ℕ => 1/(c : ℝ)^(2*B)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hs := (hp.mul_left L).subtype (fun c : ℕ => 0 < c)
  apply hs.of_norm_bounded
  intro c
  simpa only [mul_one_div,Function.comp_def] using hL f g hfm hgm hf (fun _ _ => le_rfl) c

theorem gamma0TrueWidthPhysicalFibre_cutoff_right_tendsto (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : Ioi (0 : ℕ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {a B M : ℝ} (ha : 0 < a) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Tendsto (fun K : ℕ => gamma0TrueWidthPhysicalFibre N r s c m n f
      (spectralWeylProfileCutoff a K g)) atTop
        (𝓝 (gamma0TrueWidthPhysicalFibre N r s c m n f g)) := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hq₁ : 0 < |cuspFourierFrequency 1 m| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hq₂ : 0 < |cuspFourierFrequency 1 n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hC := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  have hX : 0 < Real.sqrt (|cuspFourierFrequency 1 m| * |cuspFourierFrequency 1 n|)*
      (2/gamma0TrueWidthModulus N r s (c.val : ℝ)) := by positivity
  have h := spectralWeylPhysicalBilinear_cutoff_right_tendsto ha hX hB hB₁ hM
    (cuspFourierFrequency 1 m/|cuspFourierFrequency 1 m|)
    (cuspFourierFrequency 1 n/|cuspFourierFrequency 1 n|) f g hfm hgm hMoment hf
  exact tendsto_const_nhds.mul h

theorem gamma0TrueWidthPhysicalSeries_cutoff_right_tendsto (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {a B M : ℝ} (ha : 0 < a) (hB : 1/2 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Tendsto (fun K : ℕ => ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n f
      (spectralWeylProfileCutoff a K g)) atTop
        (𝓝 (∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n f g)) := by
  obtain ⟨L,_,hL⟩ := gamma0TrueWidthPhysicalFibre_uniform_moment N r s m n hm hn
    (by linarith) hB₁ hM g hMoment
  have hp : Summable (fun c : ℕ => 1/(c : ℝ)^(2*B)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hs := (hp.mul_left L).subtype (fun c : ℕ => 0 < c)
  apply tendsto_tsum_of_dominated_convergence hs
  · intro c
    exact gamma0TrueWidthPhysicalFibre_cutoff_right_tendsto N r s c m n hm hn ha
      (by linarith) hB₁ hM f g hfm hgm hMoment hf
  · filter_upwards with K c
    simpa only [mul_one_div,Function.comp_def] using hL f (spectralWeylProfileCutoff a K g) hfm
      (spectralWeylProfileCutoff_measurable a K g hgm) hf
      (fun x _ => spectralWeylProfileCutoff_norm_le a K g x) c

end ArtinMatthews
