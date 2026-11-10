module

public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.SpectralCuspTrueWidth
public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralKLHeightPhysicalTest
public import ArtinMatthews.SpectralCuspWidthNormalization
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralKLCuspHeightTransform
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact true-width scaling of the actual Bessel transform. The literal
factor is 1/sqrt(width), and the common-period frequencies are admissible
multiples of N/width. -/

noncomputable section
open Set MeasureTheory
open scoped Topology MatrixGroups

namespace ArtinMatthews

theorem cuspBesselTransform_positive_dilation (ν : ℂ) (q Y w : ℝ)
    (hw : 0 < w) (hY : 0 < Y) (ρ : ℝ → ℝ) :
    cuspBesselTransform ν q Y ρ = (Real.sqrt w : ℂ)⁻¹*
      cuspBesselTransform ν (q*w) (Y/w) (fun u => ρ (w*u)) := by
  have hh := integral_comp_mul_left_Ioi' (cuspBesselTransformIntegrand ν q ρ) (Y/w) hw
  rw [mul_div_cancel₀ Y hw.ne'] at hh
  unfold cuspBesselTransform
  rw [← hh,← integral_smul,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := (div_pos hY hw).trans hu
  have hsq : (Real.sqrt w : ℂ)^2 = (w : ℂ) := by exact_mod_cast Real.sq_sqrt hw.le
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
  have hsC : (Real.sqrt w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hw).ne'
  dsimp only [cuspBesselTransformIntegrand,cuspBesselKernel]
  rw [Real.sqrt_mul hw.le,Complex.real_smul]
  push_cast
  rw [mul_assoc q w u]
  field_simp
  rw [hsq]
  ring_nf

theorem cuspBesselTransform_trueWidth (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (ν : ℂ) (j : ℤ) (Y : ℝ) (hY : 0 < Y) (ρ : ℝ → ℝ) :
    cuspBesselTransform ν |cuspFourierFrequency (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*j)| Y ρ =
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)⁻¹*
        cuspBesselTransform ν |cuspFourierFrequency 1 j| (Y/(gamma0CuspTrueWidth N r : ℝ))
          (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)) := by
  rw [cuspBesselTransform_positive_dilation ν _ Y (gamma0CuspTrueWidth N r : ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r) hY ρ,cuspFourierFrequency_abs_trueWidth]

theorem spectral_cusp_width_test_properties (w Y : ℝ) (hw : 0 < w)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hs : tsupport ρ ⊆ Ioi Y) :
    Continuous (fun u => ρ (w*u)) ∧ HasCompactSupport (fun u => ρ (w*u)) ∧
      tsupport (fun u => ρ (w*u)) ⊆ Ioi (Y/w) := by
  have hc : Continuous (fun u : ℝ => ρ (w*u)) := hρ.comp (by fun_prop)
  have hcc : HasCompactSupport (fun u : ℝ => ρ (w*u)) := by
    simpa only [Function.comp_def,Homeomorph.coe_mulLeft₀] using
      hcρ.comp_homeomorph (Homeomorph.mulLeft₀ w hw.ne')
  have hsp : tsupport (fun u : ℝ => ρ (w*u)) ⊆ Ioi (Y/w) := by
    intro u hu
    have hu' : w*u ∈ tsupport ρ :=
      tsupport_comp_subset_preimage (f := fun x : ℝ => w*x) ρ (by fun_prop) hu
    apply (div_lt_iff₀ hw).mpr
    have hYu : Y < w*u := hs hu'
    simpa only [mul_comm] using hYu
  exact ⟨hc,hcc,hsp⟩

theorem cuspBesselTransform_trueWidth_imaginary_KL (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (j : ℤ) (hj : j ≠ 0) (Y : ℝ) (hY : 0 < Y) (ρ : ℝ → ℝ)
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hs : tsupport ρ ⊆ Ioi Y) (t : ℝ) :
    cuspBesselTransform ((t : ℂ)*Complex.I)
      |cuspFourierFrequency (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*j)| Y ρ =
        (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)⁻¹*
          spectralKLPhysicalAnalysisIntegral
            (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 j|
              (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u))) t := by
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N r
  obtain ⟨hR,hRc,hRs⟩ := spectral_cusp_width_test_properties _ Y hw ρ hρ hcρ hs
  have hq : 0 < |cuspFourierFrequency 1 j| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos j hj)
  rw [cuspBesselTransform_trueWidth N r _ j Y hY ρ,
    cuspBesselTransform_imaginary_eq_KL hq (div_pos hY hw) _ hR hRc hRs]

end ArtinMatthews
