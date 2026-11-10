module

public import ArtinMatthews.SpectralGamma0EisensteinSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine local convergence of the Γ₀(N) row series on the upper half-plane. -/
noncomputable section
open Set Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0EisensteinSummand_continuous (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (v : Gamma0EisensteinRows N) : Continuous (gamma0EisensteinSummand N s v) := by
  have hh : Continuous (gamma0EisensteinHeight N v) := by
    change Continuous (fun z : UpperHalfPlane =>
      (Matrix.SpecialLinearGroup.mapGL ℝ (gamma0EisensteinRowRepresentative N v : SL(2,ℤ)) • z).im)
    exact UpperHalfPlane.continuous_im.comp (continuous_const_smul _)
  exact (Complex.continuous_ofReal_cpow_const (by linarith : 0 < s.re)).comp hh

theorem gamma0EisensteinSummand_compact_majorant (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : Gamma0EisensteinRows N → ℝ, Summable u ∧
      ∀ v z, z ∈ K → ‖gamma0EisensteinSummand N s v z‖ ≤ u v := by
  obtain ⟨A,B,hB,hKB⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  obtain ⟨M,hM⟩ := hK.bddAbove_image UpperHalfPlane.continuous_im.continuousOn
  let H : ℝ := max M 1
  have hH : 0 < H := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  let C : ℝ := H^s.re * (EisensteinSeries.r ⟨⟨A,B⟩,hB⟩)^(-(2*s.re))
  refine ⟨fun v => C*‖v.val‖^(-(2*s.re)),?_,?_⟩
  · exact ((EisensteinSeries.summable_one_div_norm_rpow (show 2 < 2*s.re by linarith)).subtype
      (fun v => v ∈ Set.range (gamma0EisensteinRow N))).mul_left C
  · intro v z hz
    have him : z.im ≤ H := (hM ⟨z,hz,rfl⟩).trans (le_max_left _ _)
    have hh := EisensteinSeries.summand_bound_of_mem_verticalStrip
      (show 0 ≤ 2*s.re by linarith) v.val hB (hKB hz)
    rw [gamma0EisensteinSummand_norm_row]
    calc
      _ ≤ H^s.re * ((EisensteinSeries.r ⟨⟨A,B⟩,hB⟩)^(-(2*s.re))*‖v.val‖^(-(2*s.re))) :=
        mul_le_mul (Real.rpow_le_rpow z.im_pos.le him (by linarith)) hh
          (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hH.le _)
      _ = _ := (mul_assoc _ _ _).symm

theorem gamma0Eisenstein_tendstoLocallyUniformly (N : ℕ) (s : ℂ) (hs : 1 < s.re) :
    TendstoLocallyUniformly
      (fun t : Finset (Gamma0EisensteinRows N) => fun z =>
        ∑ v ∈ t, (1/2 : ℂ)*gamma0EisensteinSummand N s v z)
      (gamma0Eisenstein N s) atTop := by
  unfold gamma0Eisenstein
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨u,hu,hb⟩ := gamma0EisensteinSummand_compact_majorant N s hs hK
  have h := tendstoUniformlyOn_tsum
    (f := fun (v : Gamma0EisensteinRows N) (z : UpperHalfPlane) => (1/2 : ℂ)*gamma0EisensteinSummand N s v z)
    (s := K) (hu := hu.mul_left ‖(1/2 : ℂ)‖)
    (fun v z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb v z hz) (norm_nonneg _))
  simpa only [tsum_mul_left] using h

theorem gamma0Eisenstein_continuous (N : ℕ) (s : ℂ) (hs : 1 < s.re) :
    Continuous (gamma0Eisenstein N s) := by
  apply (gamma0Eisenstein_tendstoLocallyUniformly N s hs).continuous
  have h (t : Finset (Gamma0EisensteinRows N)) : Continuous (fun z : UpperHalfPlane =>
      ∑ v ∈ t, (1/2 : ℂ)*gamma0EisensteinSummand N s v z) :=
    continuous_finsetSum t (fun v _ => continuous_const.mul (gamma0EisensteinSummand_continuous N s hs v))
  exact (Eventually.of_forall h).frequently

end ArtinMatthews
