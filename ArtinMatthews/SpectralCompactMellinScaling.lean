module

public import ArtinMatthews.SpectralEisensteinHighProfile
public import ArtinMatthews.SpectralProbeMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact change of height variables for compact cusp Mellin pairings.
Primitive cusp widths cancel, while a profile dilation contributes c^(s-1). -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem spectralCuspVertical_integral_density {Y : ℝ} (hY : 0<Y) (F : ℝ → ℂ) :
    (∫ y,F y ∂cuspVerticalMeasure Y)=∫ y in Ioi Y,(y^(-2:ℤ)) • F y := by
  simpa only [cuspHorizontalMeasure_univ,ENNReal.ofReal_one,one_smul] using
    (cuspVerticalL2_integral_complex_density (w:=1) zero_lt_one hY F)

theorem spectralScaledCompactMellin {w : ℝ} (hw : 0<w) (ρ : ℝ → ℂ) (s : ℂ) :
    w • (∫ y in Ioi (0:ℝ),(y^(-2:ℤ)) • inner ℂ (ρ (y/w)) (((y/w:ℝ):ℂ)^s))=
      spectralCompactCuspMellin ρ s := by
  let f (y : ℝ) := (y^(-2:ℤ)) • inner ℂ (ρ (y/w)) (((y/w:ℝ):ℂ)^s)
  have hvar := integral_comp_mul_left_Ioi f 0 hw
  rw [mul_zero] at hvar
  have he (u : ℝ) : f (w*u)=(w^(-2:ℤ)) • ((u^(-2:ℤ)) • inner ℂ (ρ u) ((u:ℂ)^s)) := by
    dsimp only [f]
    rw [mul_div_cancel_left₀ u hw.ne',mul_zpow,mul_smul]
  simp_rw [he] at hvar
  rw [integral_smul] at hvar
  have h := congrArg (fun z : ℂ => w^2 • z) hvar
  simp only [smul_smul] at h
  have h1 : w^2*w^(-2:ℤ)=1 := by simp [zpow_neg,zpow_ofNat,hw.ne']
  have h2 : w^2*w⁻¹=w := by field_simp
  rw [h1,h2,one_smul] at h
  exact h.symm

theorem gamma0EisensteinHighProfilePower_eq_mellin (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (ρ : ℝ → ℂ)
    (hlow : ∀ y≤gamma0EisensteinMatchingHeight N,
      ρ (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ))=0) (s : ℂ) :
    gamma0EisensteinHighProfilePower N i ρ s=spectralCompactCuspMellin ρ s := by
  let w : ℝ := gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i)
  let H := gamma0EisensteinMatchingHeight N
  have hw : 0<w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N _)
  have hH : 0<H := gamma0EisensteinMatchingHeight_pos N
  let f (y : ℝ) := (y^(-2:ℤ)) • inner ℂ (ρ (y/w)) (((y/w:ℝ):ℂ)^s)
  have hzero (y : ℝ) (hy : y≤H) : f y=0 := by
    dsimp only [f]
    rw [hlow y hy,inner_zero_left,smul_zero]
  have hfull : (∫ y in Ioi H,f y)=∫ y in Ioi (0:ℝ),f y := by
    calc
      _ = ∫ y,f y := setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi H)
        (fun y hy => hzero y (le_of_not_gt hy))
      _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (0:ℝ))
        (fun y hy => hzero y ((le_of_not_gt hy).trans hH.le))).symm
  rw [gamma0EisensteinHighProfilePower,spectralCuspVertical_integral_density hH]
  change (w:ℂ)*(∫ y in Ioi H,f y)=_
  rw [hfull,← Complex.real_smul]
  exact spectralScaledCompactMellin hw ρ s

theorem spectralCompactCuspMellin_dilate {c : ℝ} (hc : 0<c) (ρ : ℝ → ℂ) (s : ℂ) :
    spectralCompactCuspMellin (fun y => ρ (y/c)) s=(c:ℂ)^(s-1)*spectralCompactCuspMellin ρ s := by
  let f (y : ℝ) := (y^(-2:ℤ)) • inner ℂ (ρ (y/c)) ((y:ℂ)^s)
  let K : ℂ := (c^(-2:ℤ):ℝ) • (c:ℂ)^s
  have he (u : ℝ) (hu : 0<u) : f (c*u)=K*((u^(-2:ℤ)) • inner ℂ (ρ u) ((u:ℂ)^s)) := by
    dsimp only [f]
    rw [mul_div_cancel_left₀ u hc.ne',Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hc.le hu.le s,mul_zpow]
    simp only [RCLike.inner_apply,Complex.real_smul,K,Complex.ofReal_mul]
    ring
  have hvar := integral_comp_mul_left_Ioi' f 0 hc
  rw [mul_zero] at hvar
  have hleft : (∫ u in Ioi (0:ℝ),f (c*u))=K*spectralCompactCuspMellin ρ s := by
    rw [spectralCompactCuspMellin,← integral_const_mul]
    apply integral_congr_ae
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun u hu => he u hu)
  rw [hleft,Complex.real_smul] at hvar
  change (c:ℂ)*(K*spectralCompactCuspMellin ρ s)=
    spectralCompactCuspMellin (fun y => ρ (y/c)) s at hvar
  have hcoef : (c:ℂ)*K=(c:ℂ)^(s-1) := by
    dsimp only [K]
    rw [Complex.real_smul,Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hc.ne'),Complex.cpow_one]
    have hpow : c^(-2:ℤ)=(c^2)⁻¹ := by simp
    rw [hpow,Complex.ofReal_inv,Complex.ofReal_pow]
    field_simp
  rw [← mul_assoc,hcoef] at hvar
  exact hvar.symm

theorem gamma0EisensteinHighProfile_actual_mellin (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ⊆Ioi (0:ℝ))
    (hlow : ∀ y≤gamma0EisensteinMatchingHeight N,
      ρ (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ))=0) (s : ℂ) :
    gamma0CuspEisensteinMeromorphicTest N a (gamma0EisensteinHighProfileSeed N i ρ hρ hcρ hpos) s=
      gamma0CuspEisensteinIndicator N (gamma0EisensteinCuspClassRepresentative N i) a*spectralCompactCuspMellin ρ s+
        gamma0EisensteinMatchedCoefficient N a s i*spectralCompactCuspMellin ρ (1-s) := by
  rw [gamma0EisensteinHighProfile_actual_test N i a ρ hρ hcρ hpos hlow,
    gamma0EisensteinHighProfilePower_eq_mellin N i ρ hlow,
    gamma0EisensteinHighProfilePower_eq_mellin N i ρ hlow]

end ArtinMatthews
