module

public import ArtinMatthews.SpectralEisensteinRadialApproximation
public import ArtinMatthews.SpectralEisensteinProfileLocalFinite
public import ArtinMatthews.SpectralEisensteinRemainderL2


set_option backward.privateInPublic true
@[expose] public section

/-! The true truncated Eisenstein series is the convergent row sum of its
radial remainder profile. Compact radial profiles converge to that actual sum. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinNormalizedHeight_power_summable_norm (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a =>
      ‖(cuspEisensteinNormalizedHeight N r a v z:ℂ)^s‖) := by
  simp_rw [cuspEisensteinNormalizedHeight_power,norm_mul]
  exact (cuspEisensteinRowTerm_summable_norm N r a s hs z).mul_left _

theorem gamma0CuspEisenstein_eq_height_tsum (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (z : UpperHalfPlane) :
    gamma0CuspEisenstein N a s z=
      (1/2:ℂ)*∑' v : Gamma0CuspEisensteinRows N 1 a,
        (cuspEisensteinNormalizedHeight N 1 a v z:ℂ)^s := by
  simp_rw [cuspEisensteinNormalizedHeight_power]
  rw [tsum_mul_left]
  unfold gamma0CuspEisenstein cuspEisensteinRowSum
  ring

theorem eisensteinRemainderProfile_norm_le (s : ℂ) {h : ℝ} (hh : 0 < h) :
    ‖eisensteinRemainderProfile s h‖ ≤ h^s.re := by
  rw [eisensteinRemainderProfile,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (eisensteinHeightCutoff_range h).2),
    Complex.norm_cpow_eq_rpow_re_of_pos hh]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hh.le _)
  linarith [(eisensteinHeightCutoff_range h).1]

theorem cuspEisensteinRemainderProfile_summable_norm (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a =>
      ‖eisensteinRemainderProfile s (cuspEisensteinNormalizedHeight N r a v z)‖) := by
  apply (cuspEisensteinNormalizedHeight_power_summable_norm N r a s hs z).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro v
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (cuspEisensteinNormalizedHeight_pos N r a v z)]
  exact eisensteinRemainderProfile_norm_le s (cuspEisensteinNormalizedHeight_pos N r a v z)

theorem gamma0CuspEisensteinRemainder_eq_tsum (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    gamma0CuspEisensteinRemainder N a s z=
      (1/2:ℂ)*∑' v : Gamma0CuspEisensteinRows N 1 a,
        eisensteinRemainderProfile s (cuspEisensteinNormalizedHeight N 1 a v z) := by
  rw [gamma0CuspEisensteinRemainder,gamma0CuspEisenstein_eq_height_tsum,
    gamma0CuspEisensteinCutoff,← mul_sub,
    ← (cuspEisensteinNormalizedHeight_power_summable_norm N 1 a s hs z).of_norm.tsum_sub
      (cuspEisensteinCutoffTerm_summable_norm N 1 a s hs z).of_norm]
  congr 1
  apply tsum_congr
  intro v
  simp only [eisensteinRemainderProfile,cuspEisensteinCutoffTerm,Complex.ofReal_sub,
    Complex.ofReal_one]
  ring

theorem gamma0CuspEisensteinRadialApprox_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Tendsto (fun n : ℕ => gamma0CuspHeightProfile N a (eisensteinRadialApprox s (n+1:ℕ)) z)
      atTop (𝓝 (gamma0CuspEisensteinRemainder N a s z)) := by
  have ht := tendsto_tsum_of_dominated_convergence
    (cuspEisensteinNormalizedHeight_power_summable_norm N 1 a s hs z)
    (fun v => eisensteinRadialApprox_tendsto s (cuspEisensteinNormalizedHeight_pos N 1 a v z))
    (Filter.Eventually.of_forall (fun n v => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (cuspEisensteinNormalizedHeight_pos N 1 a v z)]
      exact eisensteinRadialApprox_norm_le s _ _ (cuspEisensteinNormalizedHeight_pos N 1 a v z)))
  rw [gamma0CuspEisensteinRemainder_eq_tsum N a s hs z]
  convert tendsto_const_nhds.mul ht using 1
  funext n
  exact gamma0CuspHeightProfile_eq_tsum N a _
    (one_div_pos.mpr (by positivity : (0:ℝ)<(n+1:ℕ)))
    (fun t ht => eisensteinRadialApprox_small_zero s (by positivity) ht) z

end ArtinMatthews
