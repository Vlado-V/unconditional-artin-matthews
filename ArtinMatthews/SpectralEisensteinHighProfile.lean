module

public import ArtinMatthews.SpectralCuspContinuousRepresentative
public import ArtinMatthews.SpectralEisensteinMeromorphicTests
public import ArtinMatthews.SpectralCuspContinuousMean
public import ArtinMatthews.SpectralCuspSmoothUnfolding
public import ArtinMatthews.SpectralEisensteinCutoffAutomorphy
public import ArtinMatthews.SpectralEisensteinMatchingModes
public import ArtinMatthews.SpectralEisensteinPrimitiveProfileIntegral
public import ArtinMatthews.SpectralEisensteinPrimitiveProfilePairing
public import ArtinMatthews.SpectralHorizontalPeriodMeasurableFibers
public import ArtinMatthews.SpectralStoneEisensteinPair
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

/-! Genuine compact cusp-height tests isolate the incoming and outgoing
constant powers of the actual meromorphic Eisenstein family. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

def gamma0EisensteinHighProfileSeed (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N)
    (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ⊆Ioi (0:ℝ)) :
    h2SmoothCompactSeeds :=
  (1/2:ℂ) • cuspHeightProfileSeed N (gamma0EisensteinCuspClassRepresentative N i) ρ hρ hcρ hpos

def gamma0EisensteinHighProfilePower (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N)
    (ρ : ℝ → ℂ) (s : ℂ) : ℂ :=
  (gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℂ)*
    ∫ y,inner ℂ (ρ (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)))
      ((((y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)):ℝ):ℂ)^s)
        ∂cuspVerticalMeasure (gamma0EisensteinMatchingHeight N)

theorem gamma0EisensteinHighProfileSeed_mass (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N)
    (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ⊆Ioi (0:ℝ)) :
    gamma0SmoothSeedMass N (gamma0EisensteinHighProfileSeed N i ρ hρ hcρ hpos)=
      gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N
        (gamma0EisensteinCuspClassRepresentative N i) ρ hρ hcρ hpos) := by
  rw [gamma0CuspHeightProfileEnergy,gamma0EnergyInclusion_test]
  rfl

theorem gamma0EisensteinHighProfile_truncated_pair_zero (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ⊆Ioi (0:ℝ))
    (hlow : ∀ y≤gamma0EisensteinMatchingHeight N,
      ρ (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ))=0) (s : ℂ) :
    inner ℂ (gamma0SmoothSeedMass N (gamma0EisensteinHighProfileSeed N i ρ hρ hcρ hpos))
      (gamma0EnergyInclusion N (gamma0CuspEisensteinMatchedTruncatedEnergy N a s))=0 := by
  have hm := (gamma0EisensteinMatchingForm_mem_iff N _).mp
    (gamma0CuspEisensteinMatchedTruncatedEnergy_mem N a s) i
  rw [gamma0EisensteinHighProfileSeed_mass,
    gamma0CuspHeightProfileMass_inner_primitive N _ _ (gamma0EisensteinMatchingHeight_pos N)
      ρ hρ hcρ hpos hlow,hm,inner_zero_right,mul_zero]

theorem gamma0EisensteinHighProfile_cutoff_mean (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (a : SL(2,ℤ)) (s : ℂ) (y : ℝ)
    (hy : gamma0EisensteinMatchingHeight N<y) :
    cuspHorizontalMean (N:ℝ) (cuspContinuousPlaneExtension (gamma0EisensteinMatchingHeight N)
      (gamma0EisensteinMatchingHeight_pos N)
      (fun z => gamma0CuspEisensteinCutoff N a s ((gamma0EisensteinCuspClassRepresentative N i)⁻¹ • z))) y=
      gamma0CuspEisensteinIndicator N (gamma0EisensteinCuspClassRepresentative N i) a*
        (((y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)):ℝ):ℂ)^s := by
  let r := gamma0EisensteinCuspClassRepresentative N i
  have hY := gamma0EisensteinMatchingHeight_pos N
  rw [cuspContinuousPlaneExtension_mean (N:ℝ) _ (Nat.cast_nonneg N) hY _ y hy]
  have he (x : ℝ) : gamma0CuspEisensteinCutoff N a s
      (r⁻¹ • gamma0EisensteinHorizontalPoint y (hY.trans hy) x)=
        gamma0CuspEisensteinIndicator N r a*(((y/(gamma0CuspTrueWidth N r:ℝ)):ℝ):ℂ)^s :=
    gamma0CuspEisensteinCutoff_raw_high N r a s _ ((gamma0EisensteinMatchingHeight_high N r).trans hy.le)
  change (N:ℂ)⁻¹*(∫ x in (0:ℝ)..(N:ℝ),gamma0CuspEisensteinCutoff N a s
    (r⁻¹ • gamma0EisensteinHorizontalPoint y (hY.trans hy) x))=_
  simp_rw [he]
  rw [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_natCast,← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast NeZero.ne N),one_mul]

theorem gamma0EisensteinHighProfile_cutoff_test (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ⊆Ioi (0:ℝ))
    (hlow : ∀ y≤gamma0EisensteinMatchingHeight N,
      ρ (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ))=0) (s : ℂ) :
    (2:ℂ)*gamma0EisensteinCutoffCompactTest N a (gamma0EisensteinHighProfileSeed N i ρ hρ hcρ hpos) s=
      gamma0CuspEisensteinIndicator N (gamma0EisensteinCuspClassRepresentative N i) a*
        gamma0EisensteinHighProfilePower N i ρ s := by
  let r := gamma0EisensteinCuspClassRepresentative N i
  let H := gamma0EisensteinMatchingHeight N
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hhalf : (starRingEnd ℂ) (1/2:ℂ)=1/2 := by
    rw [map_div₀,map_one,Complex.conj_ofNat]
  rw [gamma0EisensteinHighProfileSeed,gamma0EisensteinCutoffCompactTest_smul_seed,hhalf]
  rw [← mul_assoc,show (2:ℂ)*(1/2)=1 by norm_num,one_mul,gamma0EisensteinCutoffCompactTest,
    cuspHeightProfileSeed,h2_compactSeed_inner_modularTranslate]
  rw [gamma0Invariant_primitive_profile_integral N r (gamma0CuspEisensteinCutoff N a s)
    (gamma0CuspOutgoingCutoff_continuous N a s) (gamma0CuspEisensteinCutoff_automorphy N a s)
    H (gamma0EisensteinMatchingHeight_pos N) ρ hρ hcρ hpos hlow]
  have he : (∫ y,inner ℂ (ρ (y/w))
      (cuspHorizontalMean (N:ℝ) (cuspContinuousPlaneExtension H (gamma0EisensteinMatchingHeight_pos N)
        (fun z => gamma0CuspEisensteinCutoff N a s (r⁻¹ • z))) y) ∂cuspVerticalMeasure H)=
      gamma0CuspEisensteinIndicator N r a*(∫ y,inner ℂ (ρ (y/w)) (((y/w:ℝ):ℂ)^s)
        ∂cuspVerticalMeasure H) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(spectralHorizontal_cuspVertical_ae_iff (gamma0EisensteinMatchingHeight_pos N)).mpr
      (ae_restrict_mem measurableSet_Ioi)] with y hy
    rw [gamma0EisensteinHighProfile_cutoff_mean N i a s y hy]
    simp only [RCLike.inner_apply]
    ring
  change (w:ℂ)*_=gamma0CuspEisensteinIndicator N r a*gamma0EisensteinHighProfilePower N i ρ s
  rw [he,gamma0EisensteinHighProfilePower]
  dsimp only [w,r,H]
  simp only [Complex.ofReal_natCast]
  ac_rfl

theorem gamma0EisensteinHighProfile_actual_test (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ⊆Ioi (0:ℝ))
    (hlow : ∀ y≤gamma0EisensteinMatchingHeight N,
      ρ (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ))=0) (s : ℂ) :
    gamma0CuspEisensteinMeromorphicTest N a (gamma0EisensteinHighProfileSeed N i ρ hρ hcρ hpos) s=
      gamma0CuspEisensteinIndicator N (gamma0EisensteinCuspClassRepresentative N i) a*
        gamma0EisensteinHighProfilePower N i ρ s+
      gamma0EisensteinMatchedCoefficient N a s i*gamma0EisensteinHighProfilePower N i ρ (1-s) := by
  rw [gamma0CuspEisensteinMeromorphicTest,gamma0EisensteinHighProfile_truncated_pair_zero N i a ρ hρ hcρ hpos hlow,
    add_zero,gamma0EisensteinHighProfile_cutoff_test N i a ρ hρ hcρ hpos hlow]
  simp_rw [gamma0EisensteinHighProfile_cutoff_test N i _ ρ hρ hcρ hpos hlow]
  congr 1
  have hI (j : Gamma0EisensteinCuspClasses N) :
      gamma0CuspEisensteinIndicator N (gamma0EisensteinCuspClassRepresentative N i)
        (gamma0EisensteinCuspClassRepresentative N j)=if i=j then 1 else 0 := by
    rw [gamma0CuspEisensteinIndicator_eq_cuspClass,gamma0EisensteinCuspClassRepresentative_class,
      gamma0EisensteinCuspClassRepresentative_class]
  simp_rw [hI]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl,one_mul]
  · intro j _ hj
    rw [ite_eq_right hj.symm,zero_mul,mul_zero]
  · simp

end ArtinMatthews
