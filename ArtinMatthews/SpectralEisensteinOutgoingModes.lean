module

public import ArtinMatthews.SpectralCuspConstantTermOperator
public import ArtinMatthews.SpectralCuspEisensteinEquivalentWidths
public import ArtinMatthews.SpectralEisensteinOutgoingCharts
public import ArtinMatthews.SpectralCuspConstantTermHeights
public import ArtinMatthews.SpectralCuspContinuousMean
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralCuspWeightedGluingRepresentative
public import ArtinMatthews.SpectralEisensteinCompactForcing
public import ArtinMatthews.SpectralEisensteinHighProfiles
public import ArtinMatthews.SpectralEisensteinOutgoingEnergy
public import ArtinMatthews.SpectralEisensteinOutgoingGerms
public import ArtinMatthews.SpectralEisensteinRestrictionIdentification
public import ArtinMatthews.SpectralL2PointwiseIdentification
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

/-! The genuine completed constant terms of the actual outgoing cutoff
are its literal width-scaled power. This identifies each outgoing channel
in the same native Hilbert spaces used for truncated compactness. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspOutgoingApproxEnergy_mass_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    Tendsto (fun n => gamma0EnergyInclusion N (gamma0CuspOutgoingApproxEnergy N a q n))
      atTop (𝓝 (gamma0CuspOutgoingCutoffMass N a q hq)) := by
  have h := tendsto_pi_nhds.mpr (gamma0CuspOutgoingApproxEnergy_mass_chart_tendsto N a q hq)
  simpa only [Function.comp_def,WithLp.toLp_ofLp] using
    (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp h

theorem gamma0CuspOutgoingCutoffMass_restriction_ae (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (Y : ℝ) (hY : 0<Y) :
    gamma0CuspMassRestriction N r Y hY (gamma0CuspOutgoingCutoffMass N a q hq)
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N:ℝ) Y)]
        fun z => gamma0CuspEisensteinCutoff N a q (r⁻¹ • z) := by
  apply spectralL2_ae_eq_of_tendsto_pointwise
    (volume.restrict (hyperbolicCuspStrip (N:ℝ) Y))
    (fun n => gamma0CuspMassRestriction N r Y hY
      (gamma0EnergyInclusion N (gamma0CuspOutgoingApproxEnergy N a q n))) _
    (fun n z => gamma0CuspHeightProfile N a (eisensteinOutgoingProfile q n) (r⁻¹ • z)) _
    ((gamma0CuspMassRestriction N r Y hY).continuous.tendsto _ |>.comp
      (gamma0CuspOutgoingApproxEnergy_mass_tendsto N a q hq))
  · intro n
    exact gamma0CuspHeightProfileEnergy_restriction_ae N r a _ (eisensteinOutgoingProfile_smooth q n)
      (eisensteinOutgoingProfile_compact q n) (eisensteinOutgoingProfile_positive_support q n) Y hY
  · apply Filter.Eventually.of_forall
    intro z
    apply tendsto_const_nhds.congr'
    filter_upwards [gamma0CuspOutgoingApprox_eventually_value N a q (r⁻¹ • z)] with n hn
    exact hn.symm

theorem gamma0CuspEisensteinCutoff_raw_high (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (q : ℂ) (z : UpperHalfPlane) (hz : 2*(gamma0CuspTrueWidth N r:ℝ)≤z.im) :
    gamma0CuspEisensteinCutoff N a q (r⁻¹ • z)=
      gamma0CuspEisensteinIndicator N r a*((z.im/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^q := by
  have hw : (0:ℝ)<gamma0CuspTrueWidth N r := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  rw [gamma0CuspEisensteinCutoff_eq_profile,
    gamma0CuspHeightProfile_raw_high N r a _ (fun _ ht => eisensteinVerticalCutoffMode_zero q ht)
      z (by linarith),
    eisensteinVerticalCutoffMode_one q ((le_div_iff₀ hw).mpr hz)]

theorem gamma0CuspOutgoingCutoffMass_constant_mode (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (Y : ℝ) (hY : 0<Y)
    (hhigh : 2*(gamma0CuspTrueWidth N r:ℝ)≤Y) :
    gamma0CuspConstantTerm N r Y hY (gamma0CuspOutgoingCutoffMass N a q hq)
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y]
      fun y => gamma0CuspEisensteinIndicator N r a*((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^q := by
  let F : UpperHalfPlane → ℂ := fun z => gamma0CuspEisensteinCutoff N a q (r⁻¹ • z)
  have hF : Continuous F := (gamma0CuspOutgoingCutoff_continuous N a q).comp
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))
  have hw : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have hc := cuspHyperbolicConstantTerm_continuous_representative (N:ℝ) Y hw hY
    (gamma0CuspMassRestriction N r Y hY (gamma0CuspOutgoingCutoffMass N a q hq))
    F hF (gamma0CuspOutgoingCutoffMass_restriction_ae N r a q hq Y hY)
  filter_upwards [Measure.ae_smul_measure hc (cuspHorizontalMeasure (N:ℝ) univ),
    cuspWeightedVerticalMeasure_ae_gt (N:ℝ) Y hY] with y hy hyY
  change (gamma0CuspConstantTerm N r Y hY (gamma0CuspOutgoingCutoffMass N a q hq)) y=
    cuspHorizontalMean (N:ℝ) (cuspContinuousPlaneExtension Y hY F) y at hy
  rw [hy,cuspContinuousPlaneExtension_mean (N:ℝ) Y hw.le hY F y hyY]
  have he (x : ℝ) : F (gamma0EisensteinHorizontalPoint y (hY.trans hyY) x)=
      gamma0CuspEisensteinIndicator N r a*((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^q :=
    gamma0CuspEisensteinCutoff_raw_high N r a q _ (hhigh.trans hyY.le)
  simp_rw [he]
  rw [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_natCast,←mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne N)),one_mul]

def gamma0EisensteinMatchingHeight (N : ℕ) : ℝ := 2*(N:ℝ)

theorem gamma0EisensteinMatchingHeight_pos (N : ℕ) [NeZero N] :
    0<gamma0EisensteinMatchingHeight N :=
  mul_pos (by norm_num) (Nat.cast_pos.mpr (NeZero.pos N))

theorem gamma0EisensteinMatchingHeight_high (N : ℕ) [NeZero N] (r : SL(2,ℤ)) :
    2*(gamma0CuspTrueWidth N r:ℝ)≤gamma0EisensteinMatchingHeight N := by
  have h := Nat.le_of_dvd (NeZero.pos N) (gamma0CuspTrueWidth_dvd_level N r)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by norm_num)

def gamma0CuspOutgoingTail (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    CuspVerticalL2 (N:ℝ) (gamma0EisensteinMatchingHeight N) :=
  gamma0CuspConstantTerm N r (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
    (gamma0CuspOutgoingCutoffMass N r q hq)

theorem gamma0CuspOutgoingTail_ae (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    gamma0CuspOutgoingTail N r q hq
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure (gamma0EisensteinMatchingHeight N)]
        fun y => ((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^q := by
  have hc := gamma0CuspOutgoingCutoffMass_constant_mode N r r q hq
    (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
    (gamma0EisensteinMatchingHeight_high N r)
  simpa only [gamma0CuspOutgoingTail,gamma0CuspEisensteinIndicator,
    gamma0EisensteinCuspsEquivalent_refl N r,ite_true,one_mul] using hc

theorem gamma0CuspOutgoingTail_ne_zero (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (q : ℂ) (hq : q.re<1/2) : gamma0CuspOutgoingTail N r q hq≠0 := by
  intro h
  let A := gamma0EisensteinMatchingHeight N
  have hA : 0<A := gamma0EisensteinMatchingHeight_pos N
  have hc := gamma0CuspOutgoingTail_ae N r q hq
  rw [h] at hc
  have hz : (fun y => ((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^q)
      =ᵐ[volume.restrict (Ioi A)] (fun _ => 0) :=
    (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hA).mp (hc.symm.trans (Lp.coeFn_zero ℂ 2 _))
  have hμ : volume.restrict (Ioi A)≠0 := by
    intro hν
    have he := congrArg (fun μ : Measure ℝ => μ univ) hν
    simp [Real.volume_Ioi] at he
  let _ : NeBot (ae (volume.restrict (Ioi A))) := ae_neBot.mpr hμ
  obtain ⟨y,hy,hyA⟩ := (hz.and (ae_restrict_mem measurableSet_Ioi)).exists
  have hp : 0<y/(gamma0CuspTrueWidth N r:ℝ) :=
    div_pos (hA.trans hyA) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
  exact (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hp.ne'))) hy

theorem gamma0CuspOutgoingCutoffMass_matching_mode (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    gamma0CuspConstantTerm N r (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
      (gamma0CuspOutgoingCutoffMass N a q hq)=
      gamma0CuspEisensteinIndicator N r a • gamma0CuspOutgoingTail N r q hq := by
  apply Lp.ext
  filter_upwards [gamma0CuspOutgoingCutoffMass_constant_mode N r a q hq
      (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
      (gamma0EisensteinMatchingHeight_high N r),
    gamma0CuspOutgoingTail_ae N r q hq,
    Lp.coeFn_smul (gamma0CuspEisensteinIndicator N r a) (gamma0CuspOutgoingTail N r q hq)] with y hy ht hs
  rw [hy,hs,Pi.smul_apply,ht,smul_eq_mul]

end ArtinMatthews
