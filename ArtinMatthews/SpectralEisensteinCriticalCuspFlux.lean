module

public import ArtinMatthews.SpectralEisensteinCriticalMeans
public import ArtinMatthews.SpectralEisensteinCriticalTopPairMass
public import ArtinMatthews.SpectralEisensteinPrimitiveVerticalScale


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ambient top-force pairing is the scalar upper-band flux
in each true cusp. The native constant term and primitive density give
the literal one-dimensional integral without any extra width factor. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped MatrixGroups InnerProductSpace ENNReal
namespace ArtinMatthews

theorem gamma0EisensteinCriticalTopPairMass_inner_flux (N : ℕ) [NeZero N] (s : ℂ)
    (hs : s.re=1/2) (c : Gamma0EisensteinCuspClasses N → ℂ) (i : Gamma0EisensteinCuspClasses N) :
    (inner ℂ (gamma0EisensteinCriticalTopPairMass N (gamma0EisensteinCuspClassRepresentative N i) s
        (c i) ((gamma0CuspScatteringMatrix N s).mulVec c i))
      (gamma0EnergyInclusion N (gamma0EisensteinCriticalTruncatedEnergy N s c))).im=
      s.im*(‖c i‖^2-‖(gamma0CuspScatteringMatrix N s).mulVec c i‖^2) := by
  let r := gamma0EisensteinCuspClassRepresentative N i
  let A := gamma0EisensteinFluxScale N
  let hA := gamma0EisensteinFluxScale_pos N
  let Y := gamma0EisensteinMatchingHeight N
  let hY := gamma0EisensteinMatchingHeight_pos N
  let w : ℝ := gamma0CuspTrueWidth N r
  let a := c i
  let b := (gamma0CuspScatteringMatrix N s).mulVec c i
  let f := eisensteinCriticalTruncatedPair s A a b
  let g := eisensteinCriticalUpperErrorPair s A a b
  let M := gamma0EnergyInclusion N (gamma0EisensteinCriticalTruncatedEnergy N s c)
  have hw : 0<w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hLow (y : ℝ) (hy : y≤Y) : g (y/w)=0 := by
    have h := (lt_div_iff₀ hA).mp (gamma0EisensteinFluxScale_raw_low N r hy)
    exact eisensteinCriticalUpperErrorPair_zero s a b (Or.inl (by simpa only [mul_comm A] using h))
  have hRaw : inner ℂ (gamma0EisensteinCriticalTopPairMass N r s a b) M=
      (w:ℂ)*∫ y, inner ℂ (g (y/w)) ((gamma0EisensteinCriticalMean N i M) y) ∂cuspVerticalMeasure Y := by
    have h := gamma0CuspHeightProfileMass_inner_primitive_integral N r Y hY g
      (eisensteinCriticalUpperErrorPair_smooth s A a b) (eisensteinCriticalUpperErrorPair_compact s hA a b)
      (eisensteinCriticalUpperErrorPair_positive s hA a b) hLow M
    have hwC : (w:ℂ)=(gamma0CuspTrueWidth N r:ℂ) := Complex.ofReal_natCast _
    rw [hwC]
    exact h
  have hN : cuspHorizontalMeasure (N:ℝ) univ≠0 := by
    rw [cuspHorizontalMeasure_univ]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N)))
  have hMean : gamma0EisensteinCriticalMean N i M=ᵐ[cuspVerticalMeasure Y] fun y => f (y/w) :=
    (Measure.ae_ennreal_smul_measure_iff hN).mp (gamma0EisensteinCriticalTruncatedEnergy_mean_ae N s c i)
  have hIntegral : (∫ y,inner ℂ (g (y/w)) ((gamma0EisensteinCriticalMean N i M) y) ∂cuspVerticalMeasure Y)=
      ∫ y,inner ℂ (g (y/w)) (f (y/w)) ∂cuspVerticalMeasure Y :=
    integral_congr_ae (hMean.mono (fun y hy => congrArg (fun z : ℂ => inner ℂ (g (y/w)) z) hy))
  let I (t : ℝ) := ((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)
  have hBandZero (t : ℝ) (ht : t∉Icc (1/A) (2/A)) : I t=0 := by
    have hg : g t=0 := image_eq_zero_of_notMem_tsupport (fun h =>
      ht (eisensteinCriticalUpperErrorPair_support s hA a b h))
    change ((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)=0
    rw [hg,inner_zero_left,smul_zero]
  have hYU : Y/w<1/A := gamma0EisensteinFluxScale_raw_low N r le_rfl
  have hLU : 1/A≤2/A := div_le_div_of_nonneg_right (by norm_num) hA.le
  have hBand : (∫ t in Ioi (Y/w), I t)=∫ t in (1/A)..(2/A),I t := by
    calc
      (∫ t in Ioi (Y/w), I t) = ∫ t,I t :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (Y/w))
          (fun t ht => hBandZero t (fun ht' => ht (hYU.trans_le ht'.1)))
      _ = ∫ t in Icc (1/A) (2/A), I t :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hBandZero).symm
      _ = ∫ t in (1/A)..(2/A),I t := by
        rw [intervalIntegral.integral_of_le hLU,integral_Icc_eq_integral_Ioc]
  change (inner ℂ (gamma0EisensteinCriticalTopPairMass N r s a b) M).im=s.im*(‖a‖^2-‖b‖^2)
  rw [hRaw,hIntegral,← Complex.real_smul,
    spectralCuspVerticalMeasure_primitive_normalization hw hY (fun t => inner ℂ (g t) (f t)),hBand]
  exact eisensteinCriticalTruncatedPair_upper_band_flux hs hA (gamma0EisensteinFluxScale_lt_half N) a b

end ArtinMatthews
