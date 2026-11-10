module

public import ArtinMatthews.SpectralEisensteinCriticalTopPairMass
public import ArtinMatthews.SpectralEisensteinPrimitiveProfilePairing
public import ArtinMatthews.SpectralEisensteinPrimitiveVerticalScale
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

/-! Literal completed ambient pairing on a true-width upper cutoff band.
The compact vertical profile support yields the exact normalized interval
and its hyperbolic density. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups InnerProductSpace ENNReal ContDiff
namespace ArtinMatthews

theorem gamma0CuspHeightProfileMass_inner_upper_band (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y)
    (A : ℝ) (hA : 0<A) (hcut : Y/(gamma0CuspTrueWidth N r:ℝ)<1/A)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgp : tsupport g⊆Ioi (0:ℝ))
    (hBand : tsupport g⊆Icc (1/A) (2/A)) (m : Gamma0RegionL2 N) (f : ℝ → ℂ)
    (hmean : gamma0CuspConstantTerm N r Y hY m
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y]
        fun y => f (y/(gamma0CuspTrueWidth N r:ℝ))) :
    inner ℂ (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r g hg hgc hgp)) m=
      ∫ t in (1/A)..(2/A),((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hLow (y : ℝ) (hy : y≤Y) : g (y/w)=0 :=
    image_eq_zero_of_notMem_tsupport fun hy' =>
      (not_le_of_gt ((div_le_div_of_nonneg_right hy hw.le).trans_lt hcut)) (hBand hy').1
  have hRaw := gamma0CuspHeightProfileMass_inner_primitive_integral N r Y hY g hg hgc hgp hLow m
  have hwC : (w:ℂ)=(gamma0CuspTrueWidth N r:ℂ) := Complex.ofReal_natCast _
  rw [← hwC] at hRaw
  have hN : cuspHorizontalMeasure (N:ℝ) univ≠0 := by
    rw [cuspHorizontalMeasure_univ]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N)))
  have hm := (Measure.ae_ennreal_smul_measure_iff hN).mp hmean
  have hI : (∫ y,inner ℂ (g (y/w)) ((gamma0CuspConstantTerm N r Y hY m) y) ∂cuspVerticalMeasure Y)=
      ∫ y,inner ℂ (g (y/w)) (f (y/w)) ∂cuspVerticalMeasure Y :=
    integral_congr_ae (hm.mono (fun y hy => congrArg (fun z : ℂ => inner ℂ (g (y/w)) z) hy))
  rw [hRaw,hI,← Complex.real_smul,
    spectralCuspVerticalMeasure_primitive_normalization hw hY (fun t => inner ℂ (g t) (f t))]
  let I (t : ℝ) := ((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)
  have hZero (t : ℝ) (ht : t∉Icc (1/A) (2/A)) : I t=0 := by
    have h : g t=0 := image_eq_zero_of_notMem_tsupport (fun hh => ht (hBand hh))
    change ((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)=0
    rw [h,inner_zero_left,smul_zero]
  have hLU : 1/A≤2/A := div_le_div_of_nonneg_right (by norm_num) hA.le
  calc
    (∫ t in Ioi (Y/w),I t) = ∫ t,I t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (Y/w))
        (fun t ht => hZero t (fun hh => ht (hcut.trans_le hh.1)))
    _ = ∫ t in Icc (1/A) (2/A),I t :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hZero).symm
    _ = ∫ t in (1/A)..(2/A),I t := by
      rw [intervalIntegral.integral_of_le hLU,integral_Icc_eq_integral_Ioc]

theorem spectralRadialInner_interval_conj (g f : ℝ → ℂ) (L U : ℝ) :
    (starRingEnd ℂ) (∫ t in L..U,((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t))=
      ∫ t in L..U,((t^2:ℝ)⁻¹) • inner ℂ (f t) (g t) := by
  have hc : (∫ t in L..U,(starRingEnd ℂ) (((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)))=
      (starRingEnd ℂ) (∫ t in L..U,((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)) :=
    Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm
      (fun t => ((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t))
  rw [← hc]
  apply intervalIntegral.integral_congr
  intro t _
  change (starRingEnd ℂ) (((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t))=
    ((t^2:ℝ)⁻¹) • inner ℂ (f t) (g t)
  rw [Complex.real_smul,Complex.real_smul,map_mul,Complex.conj_ofReal,inner_conj_symm]

def gamma0CuspUpperErrorPairMass (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (s : ℂ)
    (A : ℝ) (hA : 0<A) (a b : ℂ) : Gamma0RegionL2 N :=
  gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r (eisensteinCriticalUpperErrorPair s A a b)
    (eisensteinCriticalUpperErrorPair_smooth s A a b) (eisensteinCriticalUpperErrorPair_compact s hA a b)
    (eisensteinCriticalUpperErrorPair_positive s hA a b))

theorem gamma0CuspUpperErrorPairMass_eq (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (s : ℂ)
    (A : ℝ) (hA : 0<A) (a b : ℂ) :
    gamma0CuspUpperErrorPairMass N r s A hA a b=
      a • gamma0CuspUpperCutoffForcingMass N r s A hA+b • gamma0CuspUpperCutoffForcingMass N r (1-s) A hA :=
  gamma0CuspHeightProfileMass_linearCombination N r _ _
    (eisensteinUpperCutoffError_smooth s A) (eisensteinUpperCutoffError_smooth (1-s) A)
    (eisensteinUpperCutoffError_compact s hA) (eisensteinUpperCutoffError_compact (1-s) hA)
    (eisensteinUpperCutoffError_positive_support s hA) (eisensteinUpperCutoffError_positive_support (1-s) hA) a b
    (eisensteinCriticalUpperErrorPair_smooth s A a b) (eisensteinCriticalUpperErrorPair_compact s hA a b)
    (eisensteinCriticalUpperErrorPair_positive s hA a b)

theorem gamma0CuspUpperErrorPairMass_inner_upper_band (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y)
    (A : ℝ) (hA : 0<A) (hcut : Y/(gamma0CuspTrueWidth N r:ℝ)<1/A)
    (s a b : ℂ) (m : Gamma0RegionL2 N) (f : ℝ → ℂ)
    (hmean : gamma0CuspConstantTerm N r Y hY m
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y]
        fun y => f (y/(gamma0CuspTrueWidth N r:ℝ))) :
    inner ℂ (gamma0CuspUpperErrorPairMass N r s A hA a b) m=
      ∫ t in (1/A)..(2/A),((t^2:ℝ)⁻¹) • inner ℂ (eisensteinCriticalUpperErrorPair s A a b t) (f t) :=
  gamma0CuspHeightProfileMass_inner_upper_band N r Y hY A hA hcut _
    (eisensteinCriticalUpperErrorPair_smooth s A a b) (eisensteinCriticalUpperErrorPair_compact s hA a b)
    (eisensteinCriticalUpperErrorPair_positive s hA a b) (eisensteinCriticalUpperErrorPair_support s hA a b)
    m f hmean

end ArtinMatthews
