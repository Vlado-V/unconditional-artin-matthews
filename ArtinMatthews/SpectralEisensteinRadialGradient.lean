module

public import ArtinMatthews.SpectralEisensteinEnvelopeL2
public import ArtinMatthews.SpectralEisensteinProfileGradient
public import ArtinMatthews.SpectralEisensteinProfileGradientSum
public import ArtinMatthews.SpectralEisensteinRadialDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
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

/-! The actual compact radial approximants converge in their pointwise
hyperbolic gradients, with one genuine ambient-L² envelope. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

def cuspEisensteinHeightFrame (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![
    z.im*(eisensteinNormalizedRowHeightX (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1) (z.re,z.im):ℂ),
    z.im*(eisensteinNormalizedRowHeightY (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1) (z.re,z.im):ℂ)]

theorem cuspEisensteinNormalizedHeight_eq_frameHeight (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    eisensteinNormalizedRowHeight (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1) (z.re,z.im)=
      cuspEisensteinNormalizedHeight N r a v z := by
  have hh := eisensteinNormalizedRowHeight_eq (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1)
    (cuspEisensteinRow_coefficients_ne_zero N r a v) (z.re,z.im) z.im_pos
  have hh' := cuspEisensteinNormalizedHeightPlane_eq N r a v (z.re,z.im) z.im_pos
  convert hh.trans hh' using 1
  congr 1

theorem cuspEisensteinProfileTerm_gradient_frame (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    h2SectionGradient (cuspEisensteinProfileTerm N r a f v) z=
      deriv f (cuspEisensteinNormalizedHeight N r a v z) • cuspEisensteinHeightFrame N r a v z := by
  rw [cuspEisensteinProfileTerm_gradient N r a f hf v z]
  ext i
  fin_cases i <;>
    simp [eisensteinHeightProfileGradient,eisensteinHeightProfileX,eisensteinHeightProfileY,
      cuspEisensteinHeightFrame,cuspEisensteinNormalizedHeight_eq_frameHeight,mul_left_comm]

theorem cuspEisensteinHeightFrame_norm (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    ‖cuspEisensteinHeightFrame N r a v z‖=cuspEisensteinNormalizedHeight N r a v z := by
  let f : ℝ → ℂ := fun t => (t:ℂ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff
  have hd : deriv f (cuspEisensteinNormalizedHeight N r a v z)=1 := by
    exact (by simpa only [f,id_eq,Complex.ofReal_one] using
      ((hasDerivAt_id (cuspEisensteinNormalizedHeight N r a v z)).ofReal_comp).deriv)
  have h := cuspEisensteinProfileTerm_gradient_norm N r a f hf v z
  rw [cuspEisensteinProfileTerm_gradient_frame N r a f hf v z,hd,one_smul,norm_one,mul_one] at h
  exact h

def gamma0CuspRemainderGradientSeries (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (z : UpperHalfPlane) : EuclideanSpace ℂ (Fin 2) :=
  (1/2:ℂ) • ∑' v : Gamma0CuspEisensteinRows N 1 a,
    deriv (eisensteinRemainderProfile s) (cuspEisensteinNormalizedHeight N 1 a v z) •
      cuspEisensteinHeightFrame N 1 a v z

theorem cuspEisensteinRadialGradient_bound (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) {A M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |t*deriv eisensteinHeightCutoff t| ≤ M)
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    ‖h2SectionGradient (cuspEisensteinProfileTerm N r a (eisensteinRadialApprox s A) v) z‖ ≤
      (2*M+‖s‖)*eisensteinRadialEnvelope s.re (cuspEisensteinNormalizedHeight N r a v z) := by
  rw [cuspEisensteinProfileTerm_gradient_norm N r a _ (eisensteinRadialApprox_smooth s hA) v z]
  have hh := cuspEisensteinNormalizedHeight_pos N r a v z
  have hn : cuspEisensteinNormalizedHeight N r a v z*
      ‖deriv (eisensteinRadialApprox s A) (cuspEisensteinNormalizedHeight N r a v z)‖=
      ‖(cuspEisensteinNormalizedHeight N r a v z:ℂ)*
        deriv (eisensteinRadialApprox s A) (cuspEisensteinNormalizedHeight N r a v z)‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
  rw [hn]
  exact eisensteinRadialApprox_deriv_envelope s A M hM hbound hh

theorem gamma0CuspRadialGradient_tendsto (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Tendsto (fun n : ℕ => h2SectionGradient
      (gamma0CuspHeightProfile N a (eisensteinRadialApprox s (n+1:ℕ))) z) atTop
        (𝓝 (gamma0CuspRemainderGradientSeries N a s z)) := by
  obtain ⟨M,hM,hbound⟩ := eisensteinHeightCutoff_weighted_deriv_bounded
  have hsum := (cuspEisensteinNormalizedHeight_rpow_summable N 1 a s.re hs z).mul_left (2*M+‖s‖)
  have ht := tendsto_tsum_of_dominated_convergence hsum
    (fun v => (eisensteinRadialApprox_deriv_tendsto s
      (cuspEisensteinNormalizedHeight_pos N 1 a v z)).smul_const (cuspEisensteinHeightFrame N 1 a v z))
    (Filter.Eventually.of_forall (fun n v => by
      rw [← cuspEisensteinProfileTerm_gradient_frame N 1 a _
        (eisensteinRadialApprox_smooth s (by positivity : (0:ℝ)<(n+1:ℕ))) v z]
      apply (cuspEisensteinRadialGradient_bound N 1 a s (by positivity) hM hbound v z).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold eisensteinRadialEnvelope
      apply mul_le_of_le_one_left (Real.rpow_nonneg (cuspEisensteinNormalizedHeight_pos N 1 a v z).le _)
      linarith [(eisensteinHeightCutoff_range (cuspEisensteinNormalizedHeight N 1 a v z/2)).1]))
  have hc : Tendsto (fun _ : ℕ => (1/2:ℂ)) atTop (𝓝 (1/2:ℂ)) := tendsto_const_nhds
  convert hc.smul ht using 1
  · funext n
    rw [gamma0CuspHeightProfile_gradient_tsum N a _
      (eisensteinRadialApprox_smooth s (by positivity : (0:ℝ)<(n+1:ℕ)))
      (one_div_pos.mpr (by positivity : (0:ℝ)<(n+1:ℕ)))
      (fun t ht => eisensteinRadialApprox_small_zero s (by positivity) ht)]
    congr 1
    apply tsum_congr
    intro v
    exact cuspEisensteinProfileTerm_gradient_frame N 1 a _
      (eisensteinRadialApprox_smooth s (by positivity : (0:ℝ)<(n+1:ℕ))) v z
  · rfl

theorem gamma0CuspRadialGradient_norm_le (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) {A M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |t*deriv eisensteinHeightCutoff t| ≤ M) (z : UpperHalfPlane) :
    ‖h2SectionGradient (gamma0CuspHeightProfile N a (eisensteinRadialApprox s A)) z‖ ≤
      (2*M+‖s‖)*gamma0CuspRadialEnvelope N a s.re z := by
  have hsum := (cuspEisensteinRadialEnvelope_summable N 1 a s.re hs z).mul_left (2*M+‖s‖)
  have hn : Summable (fun v : Gamma0CuspEisensteinRows N 1 a =>
      ‖h2SectionGradient (cuspEisensteinProfileTerm N 1 a (eisensteinRadialApprox s A) v) z‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => cuspEisensteinRadialGradient_bound N 1 a s hA hM hbound v z)
  rw [gamma0CuspHeightProfile_gradient_tsum N a _ (eisensteinRadialApprox_smooth s hA)
    (one_div_pos.mpr hA) (fun t ht => eisensteinRadialApprox_small_zero s hA ht),norm_smul]
  have hh : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hh]
  calc
    _ ≤ (1/2:ℝ)*(∑' v : Gamma0CuspEisensteinRows N 1 a,
        (2*M+‖s‖)*eisensteinRadialEnvelope s.re (cuspEisensteinNormalizedHeight N 1 a v z)) :=
      mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hn).trans
        (hn.tsum_le_tsum (fun v => cuspEisensteinRadialGradient_bound N 1 a s hA hM hbound v z) hsum)) (by norm_num)
    _=_ := by rw [tsum_mul_left];unfold gamma0CuspRadialEnvelope;ring

theorem gamma0CuspRemainderGradientSeries_norm_le (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |t*deriv eisensteinHeightCutoff t| ≤ M) (z : UpperHalfPlane) :
    ‖gamma0CuspRemainderGradientSeries N a s z‖ ≤ (2*M+‖s‖)*gamma0CuspRadialEnvelope N a s.re z :=
  le_of_tendsto (gamma0CuspRadialGradient_tendsto N a s hs z).norm
    (Filter.Eventually.of_forall (fun n => gamma0CuspRadialGradient_norm_le N a s hs
      (by positivity : (0:ℝ)<(n+1:ℕ)) hM hbound z))

end ArtinMatthews
