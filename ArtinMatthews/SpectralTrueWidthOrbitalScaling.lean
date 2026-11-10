module

public import ArtinMatthews.SpectralTrueWidthNormalizedMatrices
public import ArtinMatthews.SpectralOrbitalWeylKernel
public import ArtinMatthews.SpectralCuspWidthNormalization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact width dilation of the actual Weyl integral.  The unit-period kernel
has modulus c*sqrt(w_r)*sqrt(w_s) and the literal rescaled vertical tests. -/

noncomputable section
open Matrix MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace ContDiff

namespace ArtinMatthews

theorem gamma0TrueWidthModulus_ne_zero (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) {c : ℝ} (hc : c ≠ 0) : gamma0TrueWidthModulus N r s c ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero hc (Real.sqrt_pos.mpr
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r)).ne')
      (Real.sqrt_pos.mpr (by exact_mod_cast gamma0CuspTrueWidth_pos N s)).ne'

set_option backward.isDefEq.respectTransparency false in
theorem realWeylMatrix_trueWidth (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : ℝ) (hc : c ≠ 0) :
    realWeylMatrix c hc * cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ)
      (by exact_mod_cast gamma0CuspTrueWidth_pos N r) =
    cuspWidthDilation (gamma0CuspTrueWidth N s : ℝ)
      (by exact_mod_cast gamma0CuspTrueWidth_pos N s) *
      realWeylMatrix (gamma0TrueWidthModulus N r s c)
        (gamma0TrueWidthModulus_ne_zero N r s hc) := by
  have hr := (Real.sqrt_pos.mpr (show (0 : ℝ) < gamma0CuspTrueWidth N r by
    exact_mod_cast gamma0CuspTrueWidth_pos N r)).ne'
  have hs := (Real.sqrt_pos.mpr (show (0 : ℝ) < gamma0CuspTrueWidth N s by
    exact_mod_cast gamma0CuspTrueWidth_pos N s)).ne'
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [realWeylMatrix,cuspWidthDilation,gamma0TrueWidthModulus,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hc,hr,hs]

theorem cuspFourierWave_dilation_trueWidth (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m : ℤ) (ρ : ℝ → ℝ) (z : UpperHalfPlane) :
    cuspFourierWave N ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ
      (cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ)
        (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • z) =
      cuspFourierWave 1 m (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) z := by
  unfold cuspFourierWave
  rw [cuspWidthDilation_im_smul,cuspWidthDilation_re_smul,cuspFourierPhase_trueWidth]
  simp only [Nat.cast_one]

theorem cuspWidthDilation_measurePreserving (w : ℝ) (hw : 0 < w) :
    MeasurePreserving (fun z : UpperHalfPlane => cuspWidthDilation w hw • z) volume volume := by
  change MeasurePreserving (fun z : UpperHalfPlane =>
    Matrix.SpecialLinearGroup.mapGL ℝ (cuspWidthDilation w hw) • z) _ _
  exact measurePreserving_smul _ _

theorem cuspWeylOrbitalIntegrand_trueWidth (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (ρ η : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (z : UpperHalfPlane) :
    cuspWeylOrbitalIntegrand N ((gamma0CuspFrequencyStep N r : ℤ)*m)
      ((gamma0CuspFrequencyStep N s : ℤ)*n) ρ η c hc
      (cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ)
        (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • z) =
      cuspWeylOrbitalIntegrand 1 m n
        (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))
        (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y))
        (gamma0TrueWidthModulus N r s c) (gamma0TrueWidthModulus_ne_zero N r s hc) z := by
  have hact : realWeylMatrix c hc •
      (cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ)
        (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • z) =
      cuspWidthDilation (gamma0CuspTrueWidth N s : ℝ)
        (by exact_mod_cast gamma0CuspTrueWidth_pos N s) •
      (realWeylMatrix (gamma0TrueWidthModulus N r s c)
        (gamma0TrueWidthModulus_ne_zero N r s hc) • z) := by
    rw [← mul_smul,realWeylMatrix_trueWidth,mul_smul]
  unfold cuspWeylOrbitalIntegrand
  rw [hact,cuspFourierWave_dilation_trueWidth,cuspFourierWave_dilation_trueWidth]

theorem cuspWeylOrbitalKernel_trueWidth (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (ρ η : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) :
    cuspWeylOrbitalKernel N ((gamma0CuspFrequencyStep N r : ℤ)*m)
      ((gamma0CuspFrequencyStep N s : ℤ)*n) ρ η c hc =
      cuspWeylOrbitalKernel 1 m n
        (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))
        (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y))
        (gamma0TrueWidthModulus N r s c) (gamma0TrueWidthModulus_ne_zero N r s hc) := by
  let D := cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r)
  have he := (cuspWidthDilation_measurePreserving (gamma0CuspTrueWidth N r : ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r)).integral_comp
    (show MeasurableEmbedding (fun z : UpperHalfPlane => D • z) from
      measurableEmbedding_const_smul D)
    (cuspWeylOrbitalIntegrand N ((gamma0CuspFrequencyStep N r : ℤ)*m)
      ((gamma0CuspFrequencyStep N s : ℤ)*n) ρ η c hc)
  unfold cuspWeylOrbitalKernel
  rw [← he]
  apply integral_congr_ae
  exact Eventually.of_forall (cuspWeylOrbitalIntegrand_trueWidth N r s m n ρ η c hc)

theorem cuspWeylOrbitalIntegrand_trueWidth_integrable (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (ρ η : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Set.Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Set.Ioi (0 : ℝ))
    (c : ℤ) (hc : c ≠ 0) :
    Integrable (cuspWeylOrbitalIntegrand 1 m n
      (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))
      (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y))
      (gamma0TrueWidthModulus N r s c)
      (gamma0TrueWidthModulus_ne_zero N r s (by exact_mod_cast hc))) := by
  let D := cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r)
  have hI := cuspWeylOrbitalIntegrand_integrable N
    ((gamma0CuspFrequencyStep N r : ℤ)*m) ((gamma0CuspFrequencyStep N s : ℤ)*n)
    ρ η hρ hη hcρ hcη hpρ hpη c hc
  have hmp := cuspWidthDilation_measurePreserving (gamma0CuspTrueWidth N r : ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r)
  have hcomp : Integrable (fun z : UpperHalfPlane =>
      cuspWeylOrbitalIntegrand N ((gamma0CuspFrequencyStep N r : ℤ)*m)
        ((gamma0CuspFrequencyStep N s : ℤ)*n) ρ η (c : ℝ) (by exact_mod_cast hc) (D • z)) :=
    (hmp.integrable_comp_emb (measurableEmbedding_const_smul D)
      (g := cuspWeylOrbitalIntegrand N ((gamma0CuspFrequencyStep N r : ℤ)*m)
        ((gamma0CuspFrequencyStep N s : ℤ)*n) ρ η (c : ℝ) (by exact_mod_cast hc))).mpr hI
  apply hcomp.congr
  exact Eventually.of_forall (cuspWeylOrbitalIntegrand_trueWidth N r s m n ρ η (c : ℝ)
    (by exact_mod_cast hc))

end ArtinMatthews
