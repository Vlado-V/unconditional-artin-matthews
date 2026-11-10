module

public import ArtinMatthews.SpectralCuspSeparableSupport
public import ArtinMatthews.SpectralCuspCompletedUnfolding
public import ArtinMatthews.SpectralSectionLaplacianPullback
public import ArtinMatthews.SpectralGamma0GlobalWeakLaplacian
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.PiTensorProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ambient Green equation tested by the genuine period-window
seed in any cusp, unfolded against the bounded completed two-cell field. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0Green_twoCell_separable_weak_laplacian (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y)
    (f : Gamma0RegionL2 N) :
    let ψ := cuspConstantTermTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ρ hρ hρc hρpos
    (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ (ψ.val z) (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) +
    (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ ((h2SectionLaplacianSeed ψ).val z)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) =
    ∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ (ψ.val z) (gamma0CuspTwoCellMassRestriction N r Y hY f z) := by
  let ψ := cuspConstantTermTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ρ hρ hρc hρpos
  have hψ := cuspConstantTermTestSeed_support (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ρ hρ hρc hρpos Y hs
  have hΔψ := cuspConstantTermTestSeed_laplacian_support (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ρ hρ hρc hρpos Y hs
  have he := gamma0Green_global_weak_laplacian N (modularTranslateSmoothSeed r ψ) f
  rw [h2SectionLaplacianSeed_modular_pullback, inner_add_left,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ (gamma0Green N f),
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY (h2SectionLaplacianSeed ψ) hΔψ (gamma0Green N f),
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ f] at he
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  simpa only [mul_add] using he

end ArtinMatthews
