module

public import ArtinMatthews.SourceContourHeightWeight
public import ArtinMatthews.SpectralABLExceptionalWideWindow
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralABLExceptionalWideDecay
public import ArtinMatthews.SpectralBesselJAllX
public import ArtinMatthews.SpectralBesselJOrderAnalytic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ArtinMatthews
open MeasureTheory Filter Complex
noncomputable section

/-- The actual exceptional J order integrand in the upper-half-plane convention. -/
def spectralABLExceptionalJOrderIntegrand (a : ℝ) (A : ℕ) (X : ℝ) (z : ℂ) : ℂ :=
  z*spectralABLExceptionalWideCorrected a A z*Complex.besselJ (-2*I*z) (X : ℂ)

theorem spectralWeylOrder_horizontal (t y : ℝ) :
    -2*I*((t : ℂ)+(y : ℂ)*I) = ((2*y : ℝ) : ℂ)+2*((-t : ℝ) : ℂ)*I := by
  push_cast
  ring_nf
  simp only [I_sq]
  ring

theorem spectralWeylOrder_horizontal_norm_le (t y : ℝ) (hy : 0 ≤ y) :
    ‖(t : ℂ)+(y : ℂ)*I‖ ≤ |t|+y := by
  calc
    _ ≤ ‖(t : ℂ)‖+‖(y : ℂ)*I‖ := norm_add_le _ _
    _ = _ := by simp [abs_of_nonneg hy]

theorem spectralABLExceptionalJOrder_differentiableAt (a : ℝ) {A : ℕ} (hA : 1 ≤ A)
    {X : ℝ} (hX : 0 < X) {z : ℂ} (hz0 : 0 ≤ z.im) (hzA : z.im ≤ (A : ℝ)) :
    DifferentiableAt ℂ (spectralABLExceptionalJOrderIntegrand a A X) z := by
  have hH := spectralABLExceptionalWideCorrected_differentiableAt a hA z
    (by simpa only [abs_of_nonneg hz0] using hzA)
  have hν : -(1/2 : ℝ) < (-2*I*z).re := by
    norm_num [Complex.mul_re,Complex.mul_im]
    linarith
  have hJ := (spectral_besselJ_order_differentiableAt hX hν).comp z
    (differentiableAt_id.const_mul (-2*I))
  exact (differentiableAt_id.mul hH).mul hJ

theorem spectralABLExceptionalJOrder_line_bound (A y : ℕ) (hA : 3 ≤ A) (hy : y ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ a X t : ℝ, 0 < X →
      ‖spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+(y : ℂ)*I)‖ ≤
        C*Real.exp (4*(y : ℝ)*|Real.log a|)*X^(2*(y : ℝ))*SourcePhysical.sourceContourHeightWeight t := by
  obtain ⟨H,hH,hHbound⟩ := spectralABLExceptionalWideCorrected_exp_bound_at A (by omega)
  obtain ⟨J,hJ,hJbound⟩ := spectral_besselJ_vertical_allX (2*(y : ℝ)) (by positivity)
  refine ⟨((y : ℝ)+1)*H*J,by positivity,?_⟩
  intro a X t hX
  let z : ℂ := (t : ℂ)+(y : ℂ)*I
  let u : ℝ := 1+t^2
  let E := Real.exp (4*(y : ℝ)*|Real.log a|)
  let P := X^(2*(y : ℝ))
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : 1 ≤ u := by dsimp [u]; nlinarith [sq_nonneg t]
  have htu : |t| ≤ u := by dsimp [u]; nlinarith [sq_abs t,sq_nonneg (|t|-1/2)]
  have hz : ‖z‖ ≤ ((y : ℝ)+1)*u := by
    calc
      _ ≤ |t|+(y : ℝ) := by
        simpa only [z,Complex.ofReal_natCast] using
          spectralWeylOrder_horizontal_norm_le t (y : ℝ) (by positivity)
      _ ≤ _ := by dsimp [u] at *; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) y) (sq_nonneg t)]
  have hj : ‖Complex.besselJ (-2*I*z) (X : ℂ)‖ ≤ J*Real.exp (Real.pi*|t|)*P := by
    have h := hJbound (-t) X hX
    have he := spectralWeylOrder_horizontal t (y : ℝ)
    simp only [Complex.ofReal_natCast] at he
    change -2*I*z = ((2*(y : ℝ) : ℝ) : ℂ)+2*((-t : ℝ) : ℂ)*I at he
    simpa only [he,abs_neg,P] using h
  have hh : Real.exp (Real.pi*|t|)*‖spectralABLExceptionalWideCorrected a A z‖ ≤ H*E/u^(A-1) :=
    hHbound a t y hy
  have hfrac : u/u^(A-1) ≤ 1/u := by
    calc
      _ ≤ u/u^2 := div_le_div_of_nonneg_left hu.le (pow_pos hu _)
        (pow_le_pow_right₀ hu1 (by omega : 2 ≤ A-1))
      _ = _ := by field_simp [hu.ne']
  change ‖z*spectralABLExceptionalWideCorrected a A z*Complex.besselJ (-2*I*z) (X : ℂ)‖ ≤ _
  rw [norm_mul,norm_mul]
  calc
    _ ≤ ‖z‖*‖spectralABLExceptionalWideCorrected a A z‖*(J*Real.exp (Real.pi*|t|)*P) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ = ‖z‖*(Real.exp (Real.pi*|t|)*‖spectralABLExceptionalWideCorrected a A z‖)*(J*P) := by ring
    _ ≤ (((y : ℝ)+1)*u)*(H*E/u^(A-1))*(J*P) := by gcongr
    _ = (((y : ℝ)+1)*H*J*E*P)*(u/u^(A-1)) := by ring
    _ ≤ (((y : ℝ)+1)*H*J*E*P)*(1/u) := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = _ := by rw [SourcePhysical.sourceContourHeightWeight,one_div]

theorem spectralABLExceptionalJOrder_line (A y : ℕ) (hA : 3 ≤ A) (hy : y ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ a X : ℝ, 0 < X →
      Integrable (fun t : ℝ => spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+(y : ℂ)*I)) ∧
      ‖∫ t : ℝ, spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+(y : ℂ)*I)‖ ≤
        C*Real.exp (4*(y : ℝ)*|Real.log a|)*X^(2*(y : ℝ)) := by
  obtain ⟨D,hD,hpoint⟩ := spectralABLExceptionalJOrder_line_bound A y hA hy
  let W := ∫ t : ℝ, SourcePhysical.sourceContourHeightWeight t
  have hW : 0 ≤ W := integral_nonneg SourcePhysical.sourceContourHeightWeight_nonneg
  refine ⟨D*(W+1),by positivity,?_⟩
  intro a X hX
  let E := Real.exp (4*(y : ℝ)*|Real.log a|)
  let P := X^(2*(y : ℝ))
  let F : ℝ → ℂ := fun t => spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+(y : ℂ)*I)
  have hcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hy' : (y : ℝ) ≤ A := by exact_mod_cast hy
    let line : ℝ → ℂ := fun u => (u : ℂ)+(y : ℂ)*I
    have hline : Continuous line := by dsimp [line]; fun_prop
    have hcontAt : ContinuousAt (spectralABLExceptionalJOrderIntegrand a A X) (line t) :=
      (spectralABLExceptionalJOrder_differentiableAt a (by omega : 1 ≤ A) hX
        (z := (t : ℂ)+(y : ℂ)*I) (by simp) (by simpa using hy')).continuousAt
    exact hcontAt.comp hline.continuousAt
  have hi := SourcePhysical.sourceContourHeightWeight_integrable.const_mul (D*E*P)
  have hb : ∀ᵐ t ∂(volume : Measure ℝ), ‖F t‖ ≤ (D*E*P)*SourcePhysical.sourceContourHeightWeight t :=
    ae_of_all _ fun t => hpoint a X t hX
  refine ⟨hi.mono' hcont.aestronglyMeasurable hb,?_⟩
  calc
    _ ≤ ∫ t : ℝ, (D*E*P)*SourcePhysical.sourceContourHeightWeight t := norm_integral_le_of_norm_le hi hb
    _ = (D*W)*(E*P) := by rw [integral_const_mul]; change (D*E*P)*W = _; ring
    _ ≤ D*(W+1)*(E*P) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hD.le) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews
