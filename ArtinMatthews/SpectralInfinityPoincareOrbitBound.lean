module

public import ArtinMatthews.SpectralCuspOrbitSupportCount
public import ArtinMatthews.SpectralModularDensityPeriodization


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise Cauchy-Schwarz for the actual compact-seed periodization,
using the signed primitive row count at the infinity cusp. -/

noncomputable section
open Matrix Set MeasureTheory
open scoped MatrixGroups CompactlySupported BigOperators

namespace ArtinMatthews

def spectralCompactSeedNormSq (ψ : C_c(UpperHalfPlane, ℂ)) : C_c(UpperHalfPlane, ℂ) := by
  refine ⟨⟨fun z => ((‖ψ z‖^2 : ℝ) : ℂ),Complex.continuous_ofReal.comp (ψ.continuous.norm.pow 2)⟩,?_⟩
  apply ψ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  apply subset_tsupport
  intro hp
  change ((‖ψ z‖^2 : ℝ) : ℂ) ≠ 0 at hz
  exact hz (by simp [hp])

theorem spectralCompactSeedNormSq_apply (ψ : C_c(UpperHalfPlane, ℂ)) (z : UpperHalfPlane) :
    spectralCompactSeedNormSq ψ z = ((‖ψ z‖^2 : ℝ) : ℂ) := rfl

theorem gamma0PoincareSeed_integral_point_finite (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) (z : UpperHalfPlane) :
    Function.HasFiniteSupport (fun γ : CongruenceSubgroup.Gamma0 N => ψ (γ.val • z)) := by
  let e := (CongruenceSubgroup.Gamma0 N).equivMapOfInjective
    (SpecialLinearGroup.mapGL ℝ) (SpecialLinearGroup.mapGL_injective (S := ℝ))
  have h : Function.HasFiniteSupport (fun g : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) =>
      ψ (g • z)) :=
    (arithmetic_poincare_support_locallyFinite
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ).point_finite z
  exact Function.HasFiniteSupport.fun_comp_of_injective
    (f := fun g : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) => ψ (g • z))
    (g := e) e.injective h

theorem gamma0Infinity_poincare_orbit_normsq_le (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) {A : ℝ} (hA : 0 < A)
    (hSupp : ∀ z : UpperHalfPlane, ψ z ≠ 0 → z.re ∈ Icc 0 (2*(N : ℝ)) ∧ A ≤ z.im)
    (z : UpperHalfPlane) :
    ‖gamma0PoincareSeed N ψ z‖^2 ≤
      ((2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*A))))*
        (gamma0PoincareSeed N (spectralCompactSeedNormSq ψ) z).re := by
  classical
  let f (γ : CongruenceSubgroup.Gamma0 N) := ψ (γ.val • z)
  let g (γ : CongruenceSubgroup.Gamma0 N) := spectralCompactSeedNormSq ψ (γ.val • z)
  have hf : Function.HasFiniteSupport f := gamma0PoincareSeed_integral_point_finite N ψ z
  let t := hf.toFinset
  have hg : Function.support g ⊆ t := by
    intro γ hγ
    apply hf.mem_toFinset.mpr
    intro hz
    exact hγ (by
      change spectralCompactSeedNormSq ψ (γ.val • z) = 0
      change ψ (γ.val • z) = 0 at hz
      rw [spectralCompactSeedNormSq_apply,hz,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
        Complex.ofReal_zero])
  have hEq : gamma0PoincareSeed N ψ z = ∑ γ ∈ t, f γ := by
    rw [gamma0PoincareSeed_eq_finsum]
    exact finsum_eq_sum_of_support_subset f (fun _ h => hf.mem_toFinset.mpr h)
  have hEq₂ : (gamma0PoincareSeed N (spectralCompactSeedNormSq ψ) z).re =
      ∑ γ ∈ t, ‖f γ‖^2 := by
    rw [gamma0PoincareSeed_eq_finsum]
    change (∑ᶠ γ, g γ).re = _
    rw [finsum_eq_sum_of_support_subset g hg]
    simp only [g,spectralCompactSeedNormSq_apply,← Complex.ofReal_sum,Complex.ofReal_re,f]
  have hc := gamma0Infinity_orbit_support_card_le N z hA t
    (fun γ hγ => hSupp _ (hf.mem_toFinset.mp hγ))
  rw [hEq,hEq₂]
  calc
    _ ≤ (∑ γ ∈ t, ‖f γ‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (t.card : ℝ)*(∑ γ ∈ t, ‖f γ‖^2) := by
      simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) (fun γ => ‖f γ‖)
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end ArtinMatthews
