module

public import ArtinMatthews.SpectralGamma0Core
public import Mathlib.Topology.ContinuousMap.Bounded.Normed


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform norm control of actual compact-seed periodizations after a
bounded continuous multiplier. This is an analytic input, not a spectral premise. -/
noncomputable section
open Set MeasureTheory Filter
open scoped CompactlySupported MatrixGroups BoundedContinuousFunction
namespace ArtinMatthews

def spectralBoundedSeedProduct (ψ : C_c(UpperHalfPlane,ℂ)) (b : UpperHalfPlane →ᵇ ℂ) :
    C_c(UpperHalfPlane,ℂ) where
  toFun z := b z*ψ z
  continuous_toFun := b.continuous.mul ψ.continuous
  hasCompactSupport' := ψ.hasCompactSupport.mul_left

def spectralAbsoluteSeed (ψ : C_c(UpperHalfPlane,ℂ)) : C_c(UpperHalfPlane,ℂ) where
  toFun z := (‖ψ z‖:ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp ψ.continuous.norm
  hasCompactSupport' := HasCompactSupport.comp_left (f := fun z : UpperHalfPlane => ψ z)
    (g := fun w : ℂ => (‖w‖:ℂ)) ψ.hasCompactSupport (by simp)

def spectralBoundedSeedProductLinear (ψ : C_c(UpperHalfPlane,ℂ)) :
    (UpperHalfPlane →ᵇ ℂ) →ₗ[ℂ] C_c(UpperHalfPlane,ℂ) where
  toFun := spectralBoundedSeedProduct ψ
  map_add' b c := by
    ext z
    change (b z+c z)*ψ z=b z*ψ z+c z*ψ z
    ring
  map_smul' c b := by
    ext z
    change (c*b z)*ψ z=c*(b z*ψ z)
    ring

theorem arithmeticPoincare_absolute_seed_norm (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic]
    (ψ : C_c(UpperHalfPlane,ℂ)) (z : UpperHalfPlane) :
    ‖arithmeticPoincareSeed G (spectralAbsoluteSeed ψ) z‖=
      ∑ᶠ g : G, ‖ψ (g • z)‖ := by
  classical
  have hf := (arithmetic_poincare_support_locallyFinite G ψ).point_finite z
  have hn : Function.HasFiniteSupport (fun g : G => ‖ψ (g • z)‖) := by
    apply hf.subset
    intro g hg hz
    exact hg (by simp [hz])
  change ‖∑ᶠ g : G, (‖ψ (g • z)‖:ℂ)‖=∑ᶠ g : G, ‖ψ (g • z)‖
  have he : (∑ᶠ g : G, (‖ψ (g • z)‖:ℂ))=((∑ᶠ g : G, ‖ψ (g • z)‖):ℝ) := by
    exact ((Complex.ofRealLI.toContinuousLinearMap.toAddMonoidHom).map_finsum hn).symm
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  exact finsum_nonneg (fun g => norm_nonneg _)

theorem arithmeticPoincare_bounded_seed_norm (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic]
    (ψ : C_c(UpperHalfPlane,ℂ)) (b : UpperHalfPlane →ᵇ ℂ) (z : UpperHalfPlane) :
    ‖arithmeticPoincareSeed G (spectralBoundedSeedProduct ψ b) z‖ ≤
      ‖b‖*‖arithmeticPoincareSeed G (spectralAbsoluteSeed ψ) z‖ := by
  classical
  have hf := (arithmetic_poincare_support_locallyFinite G ψ).point_finite z
  let T := hf.toFinset
  have hz (g : G) (hg : g ∉ T) : ψ (g • z)=0 := by
    by_contra hn
    exact hg (hf.mem_toFinset.mpr hn)
  have hsum : arithmeticPoincareSeed G (spectralBoundedSeedProduct ψ b) z=
      ∑ g ∈ T, b (g • z)*ψ (g • z) := by
    change (∑ᶠ g : G, b (g • z)*ψ (g • z))=_
    apply finsum_eq_sum_of_support_subset
    intro g hg
    by_contra hn
    exact hg (by
      change b (g • z)*ψ (g • z)=0
      rw [hz g hn,mul_zero])
  have habs : (∑ᶠ g : G, ‖ψ (g • z)‖)=∑ g ∈ T, ‖ψ (g • z)‖ := by
    apply finsum_eq_sum_of_support_subset
    intro g hg
    by_contra hn
    exact hg (by
      change ‖ψ (g • z)‖=0
      rw [hz g hn,norm_zero])
  rw [hsum,arithmeticPoincare_absolute_seed_norm,habs]
  calc
    _ ≤ ∑ g ∈ T, ‖b (g • z)*ψ (g • z)‖ := norm_sum_le _ _
    _ ≤ ∑ g ∈ T, ‖b‖*‖ψ (g • z)‖ := by
      apply Finset.sum_le_sum
      intro g _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (b.norm_coe_le_norm _) (norm_nonneg _)
    _=_ := (Finset.mul_sum _ _ _).symm

end ArtinMatthews
