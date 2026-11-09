module

public import ArtinMatthews.SpectralEisensteinPrimitiveProfileIntegral
public import ArtinMatthews.SpectralEisensteinCompactProfile
public import ArtinMatthews.SpectralCuspVerticalTesting


set_option backward.privateInPublic true
@[expose] public section

/-! The true-width compact height test extracts the completed constant
term of any ambient mass vector. The native vertical Hilbert measure
uses the common period N, so the pairing carries the exact ratio w/N. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace ENNReal
namespace ArtinMatthews

theorem gamma0CuspHeightProfileVertical_memLp (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y) (ρ : ℝ → ℂ) (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    MemLp (fun y : ℝ => ρ (y/(gamma0CuspTrueWidth N r:ℝ))) 2
      ((cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y) :=
  cuspVerticalL2_memLp_compact (Nat.cast_pos.mpr (NeZero.pos N)) hY
    (hρ.comp (continuous_id.div_const _))
    (cuspHeightProfile_scaled_compact _ (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) ρ hρc)

def gamma0CuspHeightProfileVerticalLp (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y) (ρ : ℝ → ℂ) (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    CuspVerticalL2 (N:ℝ) Y :=
  (gamma0CuspHeightProfileVertical_memLp N r Y hY ρ hρ hρc).toLp _

theorem gamma0CuspHeightProfileVerticalLp_inner (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y) (ρ : ℝ → ℂ) (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (f : CuspVerticalL2 (N:ℝ) Y) :
    inner ℂ (gamma0CuspHeightProfileVerticalLp N r Y hY ρ hρ hρc) f=
      (N:ℂ)*∫ y, inner ℂ (ρ (y/(gamma0CuspTrueWidth N r:ℝ))) (f y) ∂cuspVerticalMeasure Y := by
  rw [L2.inner_def,integral_smul_measure]
  have hs : ((cuspHorizontalMeasure (N:ℝ)) univ).toReal=(N:ℝ) := by
    rw [cuspHorizontalMeasure_univ,ENNReal.toReal_ofReal (Nat.cast_nonneg N)]
  rw [hs,Complex.real_smul,Complex.ofReal_natCast]
  congr 1
  apply integral_congr_ae
  have hN : cuspHorizontalMeasure (N:ℝ) univ≠0 := by
    rw [cuspHorizontalMeasure_univ]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N)))
  have hp := (Measure.ae_ennreal_smul_measure_iff hN).mp
    (gamma0CuspHeightProfileVertical_memLp N r Y hY ρ hρ hρc).coeFn_toLp
  filter_upwards [hp] with y hy
  exact congrArg (fun z : ℂ => inner ℂ z (f y)) hy

theorem gamma0CuspHeightProfileMass_inner_primitive_seed (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y) (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hpos : tsupport ρ⊆Ioi (0:ℝ)) (hlow : ∀ y≤Y,ρ (y/(gamma0CuspTrueWidth N r:ℝ))=0)
    (φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r ρ hρ hρc hpos))
      (gamma0SmoothSeedMass N φ)=
      ((gamma0CuspTrueWidth N r:ℂ)/(N:ℂ))*
        inner ℂ (gamma0CuspHeightProfileVerticalLp N r Y hY ρ hρ.continuous hρc)
          (gamma0CuspConstantTerm N r Y hY (gamma0SmoothSeedMass N φ)) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  let ψ := cuspHeightProfileBaseSeed w (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) ρ hρ hρc hpos
  let F := gamma0PoincareSeed N φ.val
  let G (z : UpperHalfPlane) := F (r⁻¹ • z)
  let E := cuspContinuousPlaneExtension Y hY G
  have hMean : gamma0CuspConstantTerm N r Y hY (gamma0SmoothSeedMass N φ)
      =ᵐ[cuspVerticalMeasure Y] cuspHorizontalMean (N:ℝ) E := by
    have hgt : ∀ᵐ y ∂cuspVerticalMeasure Y, Y<y :=
      (spectralHorizontal_cuspVertical_ae_iff hY).mpr (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [gamma0CuspConstantTerm_seed_ae N φ r Y hY,hgt] with y hy hyY
    rw [hy,gamma0CuspSeedPlaneExtension_literal_mean N φ r Y hY y hyY]
    rw [cuspContinuousPlaneExtension_mean (N:ℝ) Y (Nat.cast_nonneg N) hY G y hyY,
      Complex.ofReal_natCast]
  rw [gamma0CuspHeightProfileEnergy,gamma0EnergyInclusion_test,map_smul,
    inner_smul_left (𝕜 := ℂ) (E := Gamma0RegionL2 N)]
  change (starRingEnd ℂ) (1/2)*inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ))
    (gamma0SmoothSeedMass N φ)=_
  rw [gamma0SmoothSeedMass_inner_unfold_translated]
  change (starRingEnd ℂ) (1/2)*(2*∫ z : UpperHalfPlane,inner ℂ (ψ.val z) (G z))=_
  have hRaw : (∫ z : UpperHalfPlane,inner ℂ (ψ.val z) (G z))=
      (w:ℂ)*∫ y,inner ℂ (ρ (y/w)) (cuspHorizontalMean (N:ℝ) E y) ∂cuspVerticalMeasure Y :=
    gamma0Invariant_primitive_profile_integral N r F (gamma0PoincareSeed N φ.val).continuous
      (gamma0PoincareSeed_invariant N φ.val) Y hY ρ hρ hρc hpos hlow
  rw [hRaw,gamma0CuspHeightProfileVerticalLp_inner N r Y hY ρ hρ.continuous hρc]
  have he : (∫ y, inner ℂ (ρ (y/w)) ((gamma0CuspConstantTerm N r Y hY
        (gamma0SmoothSeedMass N φ)) y) ∂cuspVerticalMeasure Y) =
      ∫ y, inner ℂ (ρ (y/w)) (cuspHorizontalMean (N:ℝ) E y) ∂cuspVerticalMeasure Y := by
    apply integral_congr_ae
    filter_upwards [hMean] with y hy
    rw [hy]
  rw [he,show (starRingEnd ℂ) (1/2)=(1/2:ℂ) by
    rw [map_div₀,map_one,Complex.conj_ofNat],
    Complex.ofReal_natCast]
  field_simp [show (N:ℂ)≠0 by exact_mod_cast NeZero.ne N]

theorem gamma0CuspHeightProfileMass_inner_primitive (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y) (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hpos : tsupport ρ⊆Ioi (0:ℝ)) (hlow : ∀ y≤Y,ρ (y/(gamma0CuspTrueWidth N r:ℝ))=0)
    (f : Gamma0RegionL2 N) :
    inner ℂ (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r ρ hρ hρc hpos)) f=
      ((gamma0CuspTrueWidth N r:ℂ)/(N:ℂ))*
        inner ℂ (gamma0CuspHeightProfileVerticalLp N r Y hY ρ hρ.continuous hρc)
          (gamma0CuspConstantTerm N r Y hY f) := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_eq (by fun_prop) (by fun_prop))
  intro φ
  exact gamma0CuspHeightProfileMass_inner_primitive_seed N r Y hY ρ hρ hρc hpos hlow φ

theorem gamma0CuspHeightProfileMass_inner_primitive_integral (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y) (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hpos : tsupport ρ⊆Ioi (0:ℝ)) (hlow : ∀ y≤Y,ρ (y/(gamma0CuspTrueWidth N r:ℝ))=0)
    (f : Gamma0RegionL2 N) :
    inner ℂ (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r ρ hρ hρc hpos)) f=
      (gamma0CuspTrueWidth N r:ℂ)*∫ y, inner ℂ (ρ (y/(gamma0CuspTrueWidth N r:ℝ)))
        ((gamma0CuspConstantTerm N r Y hY f) y) ∂cuspVerticalMeasure Y := by
  rw [gamma0CuspHeightProfileMass_inner_primitive N r Y hY ρ hρ hρc hpos hlow,
    gamma0CuspHeightProfileVerticalLp_inner N r Y hY ρ hρ.continuous hρc,← mul_assoc,
    div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne N)]

end ArtinMatthews
