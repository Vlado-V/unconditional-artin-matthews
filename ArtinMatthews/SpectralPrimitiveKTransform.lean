module

public import ArtinMatthews.SpectralCuspBesselOrderAnalytic
public import ArtinMatthews.SpectralPrimitiveEisensteinBessel


set_option backward.privateInPublic true
@[expose] public section

/-! The literal true-width K transform used by the primitive Poincare
seed is entire in the Eisenstein parameter. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff Topology

namespace ArtinMatthews

def gamma0PrimitiveKTransform (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (n : ℤ) (ρ : ℝ → ℝ) (s : ℂ) : ℂ :=
  cuspBesselTransform (s-1/2) (2*Real.pi*|(n : ℝ)|) (Y/(gamma0CuspTrueWidth N r : ℝ))
    (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u))

theorem gamma0PrimitiveKTransform_analytic (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hsρ : tsupport ρ ⊆ Ioi Y) :
    AnalyticOnNhd ℂ (gamma0PrimitiveKTransform N r Y n ρ) univ := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hq : 0 < 2*Real.pi*|(n : ℝ)| :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hn))
  have hσ : ContDiff ℝ ∞ (fun u => ρ (w*u)) := hρ.comp (contDiff_const.mul contDiff_id)
  have hcσ : HasCompactSupport (fun u => ρ (w*u)) := by
    simpa only [Function.comp_def,Homeomorph.coe_mulLeft₀] using
      hcρ.comp_homeomorph (Homeomorph.mulLeft₀ w hw.ne')
  have hsσ : tsupport (fun u => ρ (w*u)) ⊆ Ioi (Y/w) := by
    intro u hu
    have hm : w*u ∈ tsupport ρ :=
      tsupport_comp_subset_preimage ρ (continuous_const.mul continuous_id) hu
    show Y/w < u
    exact (div_lt_iff₀ hw).mpr (by simpa only [mem_Ioi,mul_comm] using hsρ hm)
  exact cuspBesselTransform_shifted_order_analytic hq (div_pos hY hw) _ hσ hcσ hsσ

theorem gamma0PrimitiveEisensteinTransform_initial_factor (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (s : ℂ) (hs : 1 < s.re) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) :
    gamma0PrimitiveEisensteinTransform N a r Y hY n s ρ =
      gamma0CuspInitialFourierAmplitude N r a n s*gamma0PrimitiveKTransform N r Y n ρ s :=
  gamma0PrimitiveEisensteinTransform_initial_bessel N a r Y hY n hn s hs ρ hρ hcρ hpρ hsρ

end ArtinMatthews
