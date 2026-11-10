module

public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralKLPhysicalDilation
public import ArtinMatthews.SpectralWeylPhysicalHeightDilation
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A single physical K test produces compatible compact height profiles
at different Fourier frequencies, with identical invariant height mass. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology ContDiff

namespace ArtinMatthews

def spectralFrequencyTestProfile (q : ℝ) (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.sqrt y*F (q*y)

theorem spectralFrequencyTestProfile_tsupport (q : ℝ) (F : ℝ → ℝ) :
    tsupport (spectralFrequencyTestProfile q F) ⊆ (fun y => q*y) ⁻¹' tsupport F :=
  tsupport_mul_subset_right.trans
    (tsupport_comp_subset_preimage (f := fun y : ℝ => q*y) F (by fun_prop))

theorem spectralFrequencyTestProfile_contDiff (q : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hpF : tsupport F ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (spectralFrequencyTestProfile q F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have hzero : (0 : ℝ) ∉ tsupport (spectralFrequencyTestProfile q F) := by
      intro h
      have h₀ : q*(0 : ℝ) ∈ tsupport F := spectralFrequencyTestProfile_tsupport q F h
      have hbad : 0 < q*(0 : ℝ) := hpF h₀
      simp only [mul_zero,lt_self_iff_false] at hbad
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hzero)
  · have hcomp : ContDiff ℝ ∞ (fun y : ℝ => F (q*y)) := hF.comp (by fun_prop)
    exact (Real.contDiffAt_sqrt hy).mul hcomp.contDiffAt

theorem spectralFrequencyTestProfile_compact (q : ℝ) (hq : 0 < q) (F : ℝ → ℝ)
    (hcF : HasCompactSupport F) : HasCompactSupport (spectralFrequencyTestProfile q F) := by
  have hC : HasCompactSupport (fun y : ℝ => F (q*y)) := by
    simpa only [Function.comp_def,Homeomorph.coe_mulLeft₀] using
      hcF.comp_homeomorph (Homeomorph.mulLeft₀ q hq.ne')
  exact hC.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right

theorem spectralFrequencyTestProfile_support_lower (q : ℝ) (hq : 0 < q) (F : ℝ → ℝ)
    {A : ℝ} (hF : tsupport F ⊆ Ici A) {y : ℝ}
    (hy : y ∈ tsupport (spectralFrequencyTestProfile q F)) : A/q ≤ y := by
  have h : q*y ∈ tsupport F := spectralFrequencyTestProfile_tsupport q F hy
  have hA : A ≤ q*y := hF h
  apply (div_le_iff₀ hq).mpr
  simpa only [mul_comm] using hA

theorem spectralFrequencyTestProfile_support_above (q : ℝ) (hq : 0 < q) (F : ℝ → ℝ)
    {Y : ℝ} (hF : tsupport F ⊆ Ioi (q*Y)) :
    tsupport (spectralFrequencyTestProfile q F) ⊆ Ioi Y := by
  intro y hy
  have h : q*y ∈ tsupport F := spectralFrequencyTestProfile_tsupport q F hy
  exact (mul_lt_mul_iff_of_pos_left hq).mp (hF h)

theorem spectralFrequencyTestProfile_height_mass (q : ℝ) (hq : 0 < q) (F : ℝ → ℝ) :
    cuspFourierHeightPairing (spectralFrequencyTestProfile q F) (spectralFrequencyTestProfile q F) =
      ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure := by
  unfold cuspFourierHeightPairing
  calc
    _ = ∫ y in Ioi (0 : ℝ), (F (q*y))^2/y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hy0 : 0 < y := hy
      change ((Real.sqrt y*F (q*y))*(Real.sqrt y*F (q*y)))/y^2 = _
      rw [← pow_two,mul_pow,Real.sq_sqrt hy0.le]
      field_simp [hy0.ne']
    _ = ∫ x in Ioi (0 : ℝ), (F x)^2/x := by
      simpa only [div_inv_eq_mul,mul_comm] using
        spectralKLPhysical_dilation_real_integral (fun x : ℝ => (F x)^2) (inv_pos.mpr hq)
    _ = _ := by
      rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_integral _ _ (by fun_prop)
        (fun x hx => inv_nonneg.mpr hx.le)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact div_eq_inv_mul _ _

theorem spectralFrequencyTestProfile_transform (q : ℝ) (hq : 0 < q) (F : ℝ → ℝ)
    (ν : ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hs : tsupport (spectralFrequencyTestProfile q F) ⊆ Ioi Y) :
    cuspBesselTransform ν q Y (spectralFrequencyTestProfile q F) =
      ∫ x : ℝ, (F x : ℂ)*schlafliBesselK ν x ∂spectralKLPhysicalMeasure := by
  let ρ := spectralFrequencyTestProfile q F
  let H (x : ℝ) := (F x : ℂ)*schlafliBesselK ν x
  change cuspBesselTransform ν q Y ρ = ∫ x : ℝ, H x ∂spectralKLPhysicalMeasure
  unfold cuspBesselTransform
  calc
    _ = ∫ y in Ioi (0 : ℝ), cuspBesselTransformIntegrand ν q ρ y := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hY)
      intro y hy
      have hz : ρ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy.2 (hs h))
      simp [cuspBesselTransformIntegrand,hz]
    _ = ∫ y in Ioi (0 : ℝ), H (q*y)/(y : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hy0 : 0 < y := hy
      change ((Real.sqrt y*F (q*y)/y^2 : ℝ) : ℂ)*
        ((Real.sqrt y : ℂ)*schlafliBesselK ν (q*y)) = _
      have hsqrt : (Real.sqrt y : ℂ)^2 = (y : ℂ) := by exact_mod_cast Real.sq_sqrt hy0.le
      push_cast
      calc
        _ = ((Real.sqrt y : ℂ)^2/(y : ℂ)^2)*H (q*y) := by dsimp only [H]; ring
        _ = _ := by
          rw [hsqrt]
          field_simp [Complex.ofReal_ne_zero.mpr hy0.ne']
    _ = ∫ x in Ioi (0 : ℝ), H x/(x : ℂ) := by
      simpa only [div_inv_eq_mul,mul_comm] using spectralKLPhysical_dilation_integral H (inv_pos.mpr hq)
    _ = _ := (spectralKLPhysical_integral_div H).symm

end ArtinMatthews
