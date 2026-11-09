module

public import ArtinMatthews.SpectralPeterssonCuspDecay
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-! Global Petersson-weighted bounds for the actual holomorphic series.
Decay is checked in every true-width chart before using finite index. -/

noncomputable section
open Filter Matrix UpperHalfPlane Asymptotics
open scoped MatrixGroups Topology

namespace ArtinMatthews

def spectralPeterssonWeightedNorm (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℝ :=
  ‖F z‖*z.im^((k : ℝ)/2)

theorem spectralPeterssonWeightedNorm_nonneg (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    0 ≤ spectralPeterssonWeightedNorm k F z := by
  unfold spectralPeterssonWeightedNorm
  positivity

theorem spectralPeterssonWeightedNorm_continuous (k : ℕ) (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    Continuous (spectralPeterssonWeightedNorm k F) :=
  hF.norm.mul (continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero))

theorem spectralPeterssonWeightedNorm_sq (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    spectralPeterssonWeightedNorm k F z ^ 2 = ‖UpperHalfPlane.petersson (k : ℤ) F F z‖ := by
  have hy : (z.im^((k : ℝ)/2))^2 = z.im^k := by
    rw [← Real.rpow_mul_natCast z.im_pos.le,show (k : ℝ)/2*(2 : ℕ) = k by ring,Real.rpow_natCast]
  unfold spectralPeterssonWeightedNorm UpperHalfPlane.petersson
  rw [mul_pow,hy]
  simp only [norm_mul,Complex.norm_conj,zpow_natCast,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg z.im_pos.le,pow_two]

theorem spectralPeterssonWeightedNorm_slash (k : ℕ) (g : SL(2, ℝ))
    (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    spectralPeterssonWeightedNorm k (spectralHolomorphicSlash k g F) z =
      spectralPeterssonWeightedNorm k F (g • z) := by
  have h : spectralPeterssonWeightedNorm k (spectralHolomorphicSlash k g F) z ^ 2 =
      spectralPeterssonWeightedNorm k F (g • z) ^ 2 := by
    rw [spectralPeterssonWeightedNorm_sq,spectralPeterssonWeightedNorm_sq,spectralHolomorphicPetersson_slash]
  exact le_antisymm (le_of_sq_le_sq h.le (spectralPeterssonWeightedNorm_nonneg k F _))
    (le_of_sq_le_sq h.ge (spectralPeterssonWeightedNorm_nonneg k _ _))

theorem spectralPeterssonWeightedNorm_zeroAtImInfty (k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : F =O[atImInfty] fun z => Real.exp (-(2*Real.pi*z.im))) :
    IsZeroAtImInfty (spectralPeterssonWeightedNorm k F) := by
  have hW := hF.norm_left.mul (isBigO_refl (fun z : UpperHalfPlane => z.im^((k : ℝ)/2)) atImInfty)
  have hy : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ)/2)
    (2*Real.pi) (mul_pos two_pos Real.pi_pos)).comp hy
  change Tendsto (spectralPeterssonWeightedNorm k F) atImInfty (𝓝 0)
  apply hW.trans_tendsto
  simpa only [Function.comp_def,mul_comm,neg_mul] using hlim

theorem gamma0PeterssonPoincare_weighted_bound (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m : ℕ+) :
    ∃ M : ℝ, ∀ z, spectralPeterssonWeightedNorm k (gamma0PeterssonPoincare N a k (m : ℕ)) z ≤ M := by
  let P := gamma0PeterssonPoincare N a k (m : ℕ)
  let W := spectralPeterssonWeightedNorm k P
  have hP : Continuous P := gamma0PeterssonPoincareChart_continuous N 1 a k (m : ℕ) hk
  have hW : Continuous W := spectralPeterssonWeightedNorm_continuous k P hP
  have hcusps (g : SL(2, ℤ)) : IsBoundedAtImInfty (fun z => W (g • z)) := by
    let b := g⁻¹
    let D := gamma0PeterssonWidthDilation N b
    let w := (gamma0CuspTrueWidth N b : ℝ)
    have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
    have hσ : gamma0TrueCuspScaling N b = atkinRealMap g*D := by
      change (atkinRealMap g⁻¹)⁻¹*D = _
      simp only [map_inv,inv_inv]
    have hnorm (z : UpperHalfPlane) : W (g • z) = spectralPeterssonWeightedNorm k
        (gamma0PeterssonPoincareChart N b a k (m : ℕ)) (D⁻¹ • z) := by
      rw [← gamma0PeterssonPoincare_slash_cusp N b a k (m : ℕ) hk hEven,
        spectralPeterssonWeightedNorm_slash,hσ,mul_smul,smul_inv_smul,atkinRealMap_smul]
    have hDIm (z : UpperHalfPlane) : (D⁻¹ • z).im = w⁻¹*z.im := by
      have h := cuspWidthDilation_im_smul w hw (D⁻¹ • z)
      change (D • (D⁻¹ • z)).im = w*(D⁻¹ • z).im at h
      rw [smul_inv_smul] at h
      calc
        _ = w⁻¹*(w*(D⁻¹ • z).im) := by rw [← mul_assoc,inv_mul_cancel₀ hw.ne',one_mul]
        _ = _ := by rw [← h]
    have hy : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
    have hD : Tendsto (fun z : UpperHalfPlane => D⁻¹ • z) atImInfty atImInfty := by
      change Tendsto _ atImInfty (comap UpperHalfPlane.im atTop)
      rw [tendsto_comap_iff]
      simpa only [Function.comp_def,id_eq,hDIm] using (tendsto_id.const_mul_atTop (inv_pos.mpr hw)).comp hy
    have hlim : Tendsto (spectralPeterssonWeightedNorm k
        (gamma0PeterssonPoincareChart N b a k (m : ℕ))) atImInfty (𝓝 0) :=
      spectralPeterssonWeightedNorm_zeroAtImInfty k _
        (gamma0PeterssonPoincareChart_exponential_decay N b a k hk hEven m)
    apply IsZeroAtImInfty.isBoundedAtImInfty
    change Tendsto _ atImInfty (𝓝 0)
    exact hlim.comp hD |>.congr (fun z => (hnorm z).symm)
  have hInv (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
      W (g • z) = W z := by
    have h := spectralPeterssonWeightedNorm_slash k (atkinRealMap g) P z
    rw [gamma0PeterssonPoincare_slash_gamma0 N a ⟨g,hg⟩ k (m : ℕ) hk hEven,
      atkinRealMap_smul] at h
    exact h.symm
  obtain ⟨M,hM⟩ := ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO
    (Γ := CongruenceSubgroup.Gamma0 N) (t := 0) hW le_rfl
    (fun g => by
      have hg : (fun z => W (g • z)) =O[atImInfty] (1 : UpperHalfPlane → ℝ) := hcusps g
      change (fun z => W (g • z)) =O[atImInfty] (fun _ => (1 : ℝ)) at hg
      simpa only [Real.rpow_zero] using hg) hInv
  refine ⟨M,fun z => ?_⟩
  have hbound : ‖W z‖ ≤ M := by simpa only [Real.rpow_zero,mul_one] using hM z
  rw [Real.norm_of_nonneg (show 0 ≤ W z from spectralPeterssonWeightedNorm_nonneg k P z)] at hbound
  exact hbound

theorem gamma0PeterssonPoincareChart_weighted_bound (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m : ℕ+) :
    ∃ M : ℝ, ∀ z, ‖gamma0PeterssonPoincareChart N b a k (m : ℕ) z‖*z.im^((k : ℝ)/2) ≤ M := by
  obtain ⟨M,hM⟩ := gamma0PeterssonPoincare_weighted_bound N a k hk hEven m
  refine ⟨M,fun z => ?_⟩
  change spectralPeterssonWeightedNorm k (gamma0PeterssonPoincareChart N b a k (m : ℕ)) z ≤ M
  rw [← gamma0PeterssonPoincare_slash_cusp N b a k (m : ℕ) hk hEven,spectralPeterssonWeightedNorm_slash]
  exact hM _

end ArtinMatthews
