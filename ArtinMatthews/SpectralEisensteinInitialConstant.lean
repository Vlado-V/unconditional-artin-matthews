module

public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralEisensteinRemainderL2
public import ArtinMatthews.SpectralCuspContinuousMean
public import ArtinMatthews.SpectralCuspNormalizedHorocycle
public import ArtinMatthews.SpectralEisensteinCutoffAtCusps
public import ArtinMatthews.SpectralEisensteinCutoffAutomorphy
public import ArtinMatthews.SpectralEisensteinCutoffRegularity
public import ArtinMatthews.SpectralEisensteinRestrictionIdentification
public import ArtinMatthews.SpectralHorizontalPeriodMeasurableFibers
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

/-! Identification of the continued coefficient with the literal original
all-cusp Eisenstein scattering coefficient on its convergent half-plane. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspEisensteinRemainder_normalized_mean (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) (y : ℝ) (hy : 2≤y) :
    (∫ x in (0:ℝ)..1, gamma0CuspEisensteinRemainder N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy) x))=
      (y:ℂ)^(1-s)*gamma0CuspScattering N r a s := by
  let py := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hy
  have hE : Continuous (fun x => gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y py x)) :=
    (gamma0CuspEisenstein_continuous N a s hs).comp
      ((continuous_const_smul _).comp (gamma0EisensteinHorizontalPoint_continuous y py))
  have hC : Continuous (fun x => gamma0CuspEisensteinCutoff N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y py x)) :=
    (gamma0CuspEisensteinCutoff_continuous N a s hs).comp
      ((continuous_const_smul _).comp (gamma0EisensteinHorizontalPoint_continuous y py))
  simp_rw [gamma0CuspEisensteinRemainder]
  rw [intervalIntegral.integral_sub (hE.intervalIntegrable 0 1) (hC.intervalIntegrable 0 1),
    gamma0CuspEisenstein_all_cusp_constant_term N r a s hs y py]
  simp_rw [gamma0CuspEisensteinCutoff_high_cusp N r a s hs _ y hy]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul]
  ring

theorem gamma0CuspEisensteinRemainder_common_mean (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) (t : ℝ)
    (ht : 2*(gamma0CuspTrueWidth N r:ℝ)≤t) :
    (N:ℂ)⁻¹*(∫ x in (0:ℝ)..(N:ℝ), gamma0CuspEisensteinRemainder N a s
      (r⁻¹ • gamma0EisensteinHorizontalPoint t
        (lt_of_lt_of_le (mul_pos (by norm_num : (0:ℝ)<2)
          (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))) ht) x))=
      ((gamma0CuspTrueWidth N r:ℂ)^(s-1)*gamma0CuspScattering N r a s)*(t:ℂ)^(1-s) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := by dsimp [w];exact_mod_cast gamma0CuspTrueWidth_pos N r
  have ht0 : 0<t := lt_of_lt_of_le (mul_pos (by norm_num : (0:ℝ)<2) hw) ht
  rw [gamma0Invariant_common_mean_trueWidth N r _ (gamma0CuspEisensteinRemainder_continuous N a s hs)
    (gamma0CuspEisensteinRemainder_automorphy N a s) t ht0]
  rw [gamma0CuspEisensteinRemainder_normalized_mean N r a s hs (t/w) ((le_div_iff₀ hw).mpr ht)]
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg ht0.le hw.le]
  have hn : (w:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hp : (w:ℂ)^(s-1)=((w:ℂ)^(1-s))⁻¹ := by
    rw [show s-1= -(1-s) by ring,Complex.cpow_neg]
  change (t:ℂ)^(1-s)/(w:ℂ)^(1-s)*gamma0CuspScattering N r a s=
    ((w:ℂ)^(s-1)*gamma0CuspScattering N r a s)*(t:ℂ)^(1-s)
  rw [hp]
  ring

theorem gamma0CuspEisensteinRemainder_global_constant_initial (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) :
    gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinRemainderMass N a s hs)
      =ᵐ[volume.restrict (Ioi (2*(gamma0CuspTrueWidth N r:ℝ)))]
        fun y => ((gamma0CuspTrueWidth N r:ℂ)^(s-1)*gamma0CuspScattering N r a s)*(y:ℂ)^(1-s) := by
  let Y : ℝ := 2*(gamma0CuspTrueWidth N r:ℝ)
  have hY : 0<Y := mul_pos (by norm_num) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
  let F : UpperHalfPlane → ℂ := fun z => gamma0CuspEisensteinRemainder N a s (r⁻¹ • z)
  have hF : Continuous F := (gamma0CuspEisensteinRemainder_continuous N a s hs).comp
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))
  have hc := cuspHyperbolicConstantTerm_continuous_representative (N:ℝ) Y
    (Nat.cast_pos.mpr (NeZero.pos N)) hY
    (gamma0CuspMassRestriction N r Y hY (gamma0CuspEisensteinRemainderMass N a s hs)) F hF
    (gamma0CuspEisensteinRemainderMass_restriction_ae N r a s hs Y hY)
  have hcv := (spectralHorizontal_cuspVertical_ae_iff hY).mp hc
  have hg := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
    (gamma0GlobalCuspConstantTerm_ae N r (gamma0CuspEisensteinRemainderMass N a s hs) Y hY)
  filter_upwards [hcv,hg,ae_restrict_mem measurableSet_Ioi] with y hy hyg hyY
  change Y<y at hyY
  change (gamma0CuspConstantTerm N r Y hY (gamma0CuspEisensteinRemainderMass N a s hs)) y=
    cuspHorizontalMean (N:ℝ) (cuspContinuousPlaneExtension Y hY F) y at hy
  rw [hyg,hy]
  rw [cuspContinuousPlaneExtension_mean (N:ℝ) Y (Nat.cast_nonneg N) hY F y hyY]
  exact gamma0CuspEisensteinRemainder_common_mean N r a s hs y hyY.le

end ArtinMatthews
