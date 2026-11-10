module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselJOrderAnalytic
public import ArtinMatthews.SpectralBesselJPoissonJoint
public import ArtinMatthews.SpectralBesselJSpatialODE
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


set_option backward.privateInPublic true
@[expose] public section

/-! Joint continuity in order and positive argument, and entire order dependence,
for the actual J function. The contiguous identity extends the Poisson half-plane. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace ArtinMatthews

private theorem spectral_besselJ_order_joint_at (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun p : ℂ × ℝ => Complex.besselJ p.1 (p.2 : ℂ)) (ν,x) ∧
      DifferentiableAt ℂ (fun ζ => Complex.besselJ ζ (x : ℂ)) ν := by
  suffices h : ∀ (n : ℕ) (ζ : ℂ), -(n : ℝ)-1/2 < ζ.re →
      ContinuousAt (fun p : ℂ × ℝ => Complex.besselJ p.1 (p.2 : ℂ)) (ζ,x) ∧
        DifferentiableAt ℂ (fun w => Complex.besselJ w (x : ℂ)) ζ by
    obtain ⟨n, hn⟩ := exists_nat_gt (-ν.re-1/2)
    exact h n ν (by linarith)
  intro n
  induction n with
  | zero =>
    intro ζ hζ
    have hζ' : -(1/2 : ℝ) < ζ.re := by simpa only [Nat.cast_zero, neg_zero, zero_sub] using hζ
    exact ⟨spectral_besselJ_joint_continuousAt_halfPlane hζ' hx,
      spectral_besselJ_order_differentiableAt hx hζ'⟩
  | succ n ih =>
    intro ζ hζ
    have hs : -(n : ℝ)-1/2 < (ζ+1).re := by
      push_cast at hζ
      rw [Complex.add_re, Complex.one_re]
      linarith
    have ht : -(n : ℝ)-1/2 < (ζ+2).re := by
      push_cast at hζ
      rw [Complex.add_re]
      norm_num
      linarith
    have h1 := ih (ζ+1) hs
    have h2 := ih (ζ+2) ht
    constructor
    · have hShift (d : ℂ) : Continuous (fun p : ℂ × ℝ => (p.1+d,p.2)) :=
        (continuous_fst.add continuous_const).prodMk continuous_snd
      have hShiftAt (d : ℂ) : ContinuousAt (fun p : ℂ × ℝ => (p.1+d,p.2)) (ζ,x) :=
        (hShift d).continuousAt
      have hJ₁ : ContinuousAt (fun p : ℂ × ℝ => Complex.besselJ (p.1+1) (p.2 : ℂ)) (ζ,x) :=
        h1.1.comp_of_eq (hShiftAt 1) rfl
      have hJ₂ : ContinuousAt (fun p : ℂ × ℝ => Complex.besselJ (p.1+2) (p.2 : ℂ)) (ζ,x) :=
        h2.1.comp_of_eq (hShiftAt 2) rfl
      have hC : ContinuousAt (fun p : ℂ × ℝ => 2*(p.1+1)/(p.2 : ℂ)) (ζ,x) :=
        (by fun_prop : Continuous (fun p : ℂ × ℝ => 2*(p.1+1))).continuousAt.div
          (Complex.continuous_ofReal.comp continuous_snd).continuousAt
          (Complex.ofReal_ne_zero.mpr hx.ne')
      apply ((hC.mul hJ₁).sub hJ₂).congr
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hx] with p hp
      exact (spectral_besselJ_order_recurrence p.1 hp).symm
    · have hD₁ : DifferentiableAt ℂ (fun w => Complex.besselJ (w+1) (x : ℂ)) ζ :=
        h1.2.comp ζ (differentiableAt_id.add_const 1)
      have hD₂ : DifferentiableAt ℂ (fun w => Complex.besselJ (w+2) (x : ℂ)) ζ :=
        h2.2.comp ζ (differentiableAt_id.add_const 2)
      have hC : DifferentiableAt ℂ (fun w : ℂ => 2*(w+1)/(x : ℂ)) ζ := by fun_prop
      apply ((hC.mul hD₁).sub hD₂).congr_of_eventuallyEq
      exact Eventually.of_forall (fun w => spectral_besselJ_order_recurrence w hx)

theorem spectral_besselJ_order_argument_continuousAt (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun p : ℂ × ℝ => Complex.besselJ p.1 (p.2 : ℂ)) (ν,x) :=
  (spectral_besselJ_order_joint_at ν hx).1

theorem spectral_besselJ_order_differentiable {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (fun ν => Complex.besselJ ν (x : ℂ)) :=
  fun ν => (spectral_besselJ_order_joint_at ν hx).2

end ArtinMatthews
