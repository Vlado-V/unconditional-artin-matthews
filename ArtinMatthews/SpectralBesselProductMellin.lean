module

public import ArtinMatthews.SpectralBesselMellinInversion
public import ArtinMatthews.SpectralBesselMellinConvergence
public import ArtinMatthews.SpectralBesselMellinEvaluation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! An actual K-product Mellin convolution.  Absolute convergence and Fubini
are proved from the single-K Mellin and inverse-Mellin identities. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKProductMellinKernel (ν μ s : ℂ) (σ x t : ℝ) : ℂ :=
  ((x : ℂ)^((s-(σ : ℂ))-1)*schlafliBesselK ν x) *
    Complex.exp (-(t : ℂ)*Complex.I*(Real.log x : ℂ)) *
      spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I)

theorem spectralKProductMellinKernel_norm (ν μ s : ℂ) (σ x t : ℝ) :
    ‖spectralKProductMellinKernel ν μ s σ x t‖ =
      ‖(x : ℂ)^((s-(σ : ℂ))-1)*schlafliBesselK ν x‖ *
        ‖spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I)‖ := by
  unfold spectralKProductMellinKernel
  rw [norm_mul,norm_mul,Complex.norm_exp]
  simp

theorem spectralKProductMellinKernel_integrable (ν μ s : ℂ) (σ : ℝ)
    (hμ : |μ.re| < σ) (hν : |ν.re| < s.re-σ) :
    Integrable (fun p : ℝ × ℝ => spectralKProductMellinKernel ν μ s σ p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hx : IntegrableOn (fun x : ℝ => (x : ℂ)^((s-(σ : ℂ))-1)*schlafliBesselK ν x) (Ioi 0) :=
    schlafliBesselK_mellin_integrable ν (s-(σ : ℂ)) (by simpa using hν)
  have ht := spectralKMellinMultiplier_vertical_integrable μ σ hμ
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => spectralKProductMellinKernel ν μ s σ p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
    exact (hx.aestronglyMeasurable.comp_fst.mul
      (show Measurable (fun p : ℝ × ℝ =>
        Complex.exp (-(p.2 : ℂ)*Complex.I*(Real.log p.1 : ℂ))) by fun_prop).aestronglyMeasurable).mul
          ht.aestronglyMeasurable.comp_snd
  apply (hx.norm.mul_prod ht.norm).mono' hm
  filter_upwards [] with p
  exact (spectralKProductMellinKernel_norm ν μ s σ p.1 p.2).le

theorem spectralKProductMellinKernel_power (ν μ s : ℂ) (σ t : ℝ) {x : ℝ} (hx : 0 < x) :
    spectralKProductMellinKernel ν μ s σ x t =
      ((x : ℂ)^((s-((σ : ℂ)+(t : ℂ)*Complex.I))-1)*schlafliBesselK ν x) *
        spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have he : Complex.exp (-(t : ℂ)*Complex.I*(Real.log x : ℂ)) =
      (x : ℂ)^(-(t : ℂ)*Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hxC,← Complex.ofReal_log hx.le]
    congr 1
    ring
  unfold spectralKProductMellinKernel
  rw [he]
  calc
    _ = ((x : ℂ)^((s-(σ : ℂ))-1)*(x : ℂ)^(-(t : ℂ)*Complex.I)) *
        schlafliBesselK ν x * spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hxC]
      congr 3
      ring

theorem spectralKProductMellinKernel_inverse (ν μ s : ℂ) (σ : ℝ)
    (hμ : |μ.re| < σ) {x : ℝ} (hx : 0 < x) :
    (1/(2*Real.pi) : ℝ) • (∫ t : ℝ, spectralKProductMellinKernel ν μ s σ x t) =
      (x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x := by
  have hpoint (t : ℝ) : spectralKProductMellinKernel ν μ s σ x t =
      ((x : ℂ)^(s-1)*schlafliBesselK ν x) *
        ((x : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))*
          spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I)) := by
    rw [spectralKProductMellinKernel_power ν μ s σ t hx]
    have hp : (x : ℂ)^(s-1)*(x : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I)) =
        (x : ℂ)^((s-((σ : ℂ)+(t : ℂ)*Complex.I))-1) := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
      congr 1
      ring
    rw [← hp]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hInv := schlafliBesselK_mellin_inversion μ σ hμ hx
  unfold mellinInv at hInv
  simp only [smul_eq_mul,Complex.real_smul] at hInv
  rw [Complex.real_smul]
  calc
    _ = ((x : ℂ)^(s-1)*schlafliBesselK ν x) *
        (((1/(2*Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, (x : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))*
            spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I)) := by ring
    _ = _ := by rw [hInv]

theorem spectralKProductMellinKernel_integral_x (ν μ s : ℂ) (σ t : ℝ)
    (hν : |ν.re| < s.re-σ) :
    (∫ x in Ioi (0 : ℝ), spectralKProductMellinKernel ν μ s σ x t) =
      spectralKMellinMultiplier ν (s-((σ : ℂ)+(t : ℂ)*Complex.I)) *
        spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I) := by
  calc
    _ = ∫ x in Ioi (0 : ℝ),
        ((x : ℂ)^((s-((σ : ℂ)+(t : ℂ)*Complex.I))-1)*schlafliBesselK ν x) *
          spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact spectralKProductMellinKernel_power ν μ s σ t hx
    _ = _ := by
      rw [integral_mul_const,schlafliBesselK_mellin ν
        (s-((σ : ℂ)+(t : ℂ)*Complex.I)) (by simpa using hν)]
      rfl

theorem schlafliBesselK_product_mellin_integrable (ν μ s : ℂ) (σ : ℝ)
    (hμ : |μ.re| < σ) (hν : |ν.re| < s.re-σ) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x)
      (Ioi 0) := by
  have hI := (spectralKProductMellinKernel_integrable ν μ s σ hμ hν).integral_prod_left
  apply (hI.smul (1/(2*Real.pi) : ℝ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact spectralKProductMellinKernel_inverse ν μ s σ hμ hx

theorem schlafliBesselK_product_mellin_convolution (ν μ s : ℂ) (σ : ℝ)
    (hμ : |μ.re| < σ) (hν : |ν.re| < s.re-σ) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x) =
      (1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        spectralKMellinMultiplier ν (s-((σ : ℂ)+(t : ℂ)*Complex.I)) *
          spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I) := by
  have hI := spectralKProductMellinKernel_integrable ν μ s σ hμ hν
  calc
    _ = (1/(2*Real.pi) : ℝ) • ∫ x in Ioi (0 : ℝ),
        ∫ t : ℝ, spectralKProductMellinKernel ν μ s σ x t := by
      rw [← integral_smul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (spectralKProductMellinKernel_inverse ν μ s σ hμ hx).symm
    _ = (1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        ∫ x in Ioi (0 : ℝ), spectralKProductMellinKernel ν μ s σ x t := by
      rw [integral_integral_swap hI]
    _ = _ := by simp_rw [spectralKProductMellinKernel_integral_x ν μ s σ _ hν]

def spectralKProductMellinLine (ν μ s : ℂ) : ℝ :=
  (s.re+|μ.re|-|ν.re|)/2

theorem spectralKProductMellinLine_bounds (ν μ s : ℂ) (hs : |ν.re|+|μ.re| < s.re) :
    |μ.re| < spectralKProductMellinLine ν μ s ∧
      |ν.re| < s.re-spectralKProductMellinLine ν μ s := by
  unfold spectralKProductMellinLine
  constructor <;> linarith

theorem schlafliBesselK_product_mellin_integrable_of_re_gt (ν μ s : ℂ)
    (hs : |ν.re|+|μ.re| < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x)
      (Ioi 0) :=
  schlafliBesselK_product_mellin_integrable ν μ s (spectralKProductMellinLine ν μ s)
    (spectralKProductMellinLine_bounds ν μ s hs).1
    (spectralKProductMellinLine_bounds ν μ s hs).2

theorem schlafliBesselK_product_mellin_convolution_of_re_gt (ν μ s : ℂ)
    (hs : |ν.re|+|μ.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x) =
      (1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        spectralKMellinMultiplier ν
          (s-((spectralKProductMellinLine ν μ s : ℂ)+(t : ℂ)*Complex.I)) *
        spectralKMellinMultiplier μ
          ((spectralKProductMellinLine ν μ s : ℂ)+(t : ℂ)*Complex.I) :=
  schlafliBesselK_product_mellin_convolution ν μ s (spectralKProductMellinLine ν μ s)
    (spectralKProductMellinLine_bounds ν μ s hs).1
    (spectralKProductMellinLine_bounds ν μ s hs).2

end ArtinMatthews
