module

public import ArtinMatthews.SpectralInfinityPoincareOrbitBound


set_option backward.privateInPublic true
@[expose] public section

/-! Every integral cusp chart has an explicit orbit-overlap bound.
The estimate counts both central signs and uses the actual periodization. -/

noncomputable section
open Matrix Set MeasureTheory
open scoped MatrixGroups CompactlySupported BigOperators
namespace ArtinMatthews

def gamma0CuspOrbitOverlap (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (A : ℝ) : ℝ :=
  (2*(gamma0CuspFrequencyStep N a : ℝ)+1)*(4*(1+2/A))

theorem gamma0Cusp_orbit_support_card_le (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (z : UpperHalfPlane) {A : ℝ} (hA : 0 < A)
    (t : Finset (CongruenceSubgroup.Gamma0 N))
    (ht : ∀ γ ∈ t, ((a*γ.val) • z).re ∈ Icc 0 (2*(N : ℝ)) ∧
      A ≤ ((a*γ.val) • z).im) :
    (t.card : ℝ) ≤ gamma0CuspOrbitOverlap N a A := by
  have hrows := cuspEisensteinHeightRows_card_le N 1 a Nat.one_pos
    (fun M _ => Int.one_dvd (M 1 0)) z hA
  simp only [Nat.cast_one,one_mul] at hrows
  exact (gamma0_cusp_orbit_support_card_le N a z hA t ht).trans
    (mul_le_mul_of_nonneg_left hrows (by positivity))

theorem gamma0Cusp_poincare_orbit_normsq_le (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (ψ : C_c(UpperHalfPlane, ℂ)) {A : ℝ} (hA : 0 < A)
    (hSupp : ∀ z : UpperHalfPlane, ψ z ≠ 0 →
      (a • z).re ∈ Icc 0 (2*(N : ℝ)) ∧ A ≤ (a • z).im)
    (z : UpperHalfPlane) :
    ‖gamma0PoincareSeed N ψ z‖^2 ≤ gamma0CuspOrbitOverlap N a A*
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
  have hc := gamma0Cusp_orbit_support_card_le N a z hA t (fun γ hγ => by
    simpa only [mul_smul] using hSupp _ (hf.mem_toFinset.mp hγ))
  rw [hEq,hEq₂]
  calc
    _ ≤ (∑ γ ∈ t, ‖f γ‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (t.card : ℝ)*(∑ γ ∈ t, ‖f γ‖^2) := by
      simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) (fun γ => ‖f γ‖)
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end ArtinMatthews
