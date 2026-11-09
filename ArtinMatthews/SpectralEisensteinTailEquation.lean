module

public import ArtinMatthews.SpectralAmbientResolventWeakPDE
public import ArtinMatthews.SpectralEisensteinForcingCusps
public import ArtinMatthews.SpectralCuspGreenSeparableTest
public import ArtinMatthews.SpectralCuspSeparablePairing
public import ArtinMatthews.SpectralCuspConstantTermGlobalTesting


set_option backward.privateInPublic true
@[expose] public section

/-! The actual continued remainder has the homogeneous constant-mode Euler
equation in every high cusp. Its forcing vanishing is derived from the
literal normalized-height support, rather than assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0CuspEisensteinCompactForcing_raw_high (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (z : UpperHalfPlane)
    (hz : 2*(gamma0CuspTrueWidth N r:ℝ) ≤ z.im) :
    gamma0CuspEisensteinCompactForcing N a s (r⁻¹ • z)=0 := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := by dsimp [w]; exact_mod_cast gamma0CuspTrueWidth_pos N r
  let p : UpperHalfPlane := (cuspWidthDilation w hw)⁻¹ • z
  have him : p.im=z.im/w := cuspWidthDilation_im_inv_smul w hw z
  have hp2 : 2≤p.im := by rw [him]; exact (le_div_iff₀ hw).mpr hz
  have he : gamma0TrueCuspScaling N r • p=r⁻¹ • z := by
    dsimp [p,w]
    rw [gamma0TrueCuspScaling,mul_smul,smul_inv_smul,← map_inv]
    exact atkinRealMap_smul r⁻¹ z
  have hp : gamma0EisensteinHorizontalPoint p.im p.im_pos p.re=p := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> rfl
  have hf := gamma0CuspEisensteinCompactForcing_high_cusp N r a s p.re p.im hp2
  rwa [hp,he] at hf

theorem gamma0CuspEisensteinCompactForcingMass_tail_test_zero
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ) (ψ : h2SmoothCompactSeeds)
    (hψ : ∀ z ∈ Function.support (fun z : UpperHalfPlane => ψ.val z),
      2*(gamma0CuspTrueWidth N r:ℝ) ≤ z.im) :
    inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ))
      (gamma0CuspEisensteinCompactForcingMass N a s)=0 := by
  let φ := (1/2:ℂ) • cuspHeightProfileSeed N a (eisensteinVerticalCutoffError s)
    (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
    (eisensteinVerticalCutoffError_positive_support s)
  change inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ))
    (gamma0SmoothSeedMass N φ)=0
  rw [gamma0SmoothSeedMass_inner_unfold_translated]
  have hφ (z : UpperHalfPlane) : gamma0CuspSection N φ r z=
      gamma0CuspEisensteinCompactForcing N a s (r⁻¹ • z) := by
    rw [gamma0CuspEisensteinCompactForcing_eq_poincare]
    change arithmeticPoincareSeed (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
      ((1/2:ℂ) • (cuspHeightProfileSeed N a (eisensteinVerticalCutoffError s)
        (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
        (eisensteinVerticalCutoffError_positive_support s)).val) (r⁻¹ • z)=_
    rw [arithmeticPoincareSeed_smul]
    rfl
  have hi : (∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (gamma0CuspSection N φ r z))=0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun z => by
      change inner ℂ (ψ.val z) (gamma0CuspSection N φ r z)=0
      by_cases hz : ψ.val z=0
      · rw [hz,inner_zero_left]
      · rw [hφ,gamma0CuspEisensteinCompactForcing_raw_high N r a s z (hψ z hz),inner_zero_right]
  rw [hi,mul_zero]

theorem gamma0CuspEisensteinContinuedRemainder_constant_second_weak
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain)
    (Y : ℝ) (hY : 0<Y) (hhigh : 2*(gamma0CuspTrueWidth N r:ℝ) ≤ Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) :
    (∫ y in Ioi Y, deriv (deriv ρ) y • gamma0CuspConstantTerm N r Y hY
      (gamma0CuspEisensteinContinuedRemainder N a s) y)=
      -(s*(1-s))*(∫ y in Ioi Y, (ρ y/y^2) • gamma0CuspConstantTerm N r Y hY
        (gamma0CuspEisensteinContinuedRemainder N a s) y) := by
  let hpos : tsupport ρ ⊆ Ioi (0:ℝ) := fun _ hy => hY.trans (hρs hy)
  let ψ := cuspConstantTermTestSeed (N:ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ρ hρ hρc hpos
  have hψ := cuspConstantTermTestSeed_support (N:ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ρ hρ hρc hpos Y hρs
  have hΔψ := cuspConstantTermTestSeed_laplacian_support (N:ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ρ hρ hρc hpos Y hρs
  have he := gamma0CuspEisensteinContinuedRemainder_global_weak_laplacian N a s hs
    (modularTranslateSmoothSeed r ψ)
  rw [gamma0CuspEisensteinCompactForcingMass_tail_test_zero N r a s ψ
      (fun z hz => hhigh.trans (hψ hz).2.le),neg_zero,
    h2SectionLaplacianSeed_modular_pullback,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY (h2SectionLaplacianSeed ψ) hΔψ,
    gamma0CuspTwoCellMassRestriction_test_pairing,
    gamma0CuspTwoCellMassRestriction_laplacian_pairing] at he
  simp only [Complex.real_smul] at he
  have hN : (N:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) hN))
  linear_combination -he

end ArtinMatthews
