module

public import ArtinMatthews.SpectralGamma0TailComparison
public import ArtinMatthews.SpectralGamma0TruncatedMeanZero
public import ArtinMatthews.SpectralGamma0TruncatedCore


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compact mass inclusion on the constructed all-height mean-zero
energy space. Identification with the full automorphic cusp space is separate. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspTailMass_truncated_le (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A)
    (Y : ℝ) (hY : 1 ≤ Y) (hAY : A≤Y) (u : gamma0TruncatedMeanZeroEnergy N A hA) :
    gamma0CuspTailMass N Y hY u.val ≤
      2*(Fintype.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ)*
        ((N : ℝ)^2/Y^2)*(((N : ℝ)+1)*‖u‖^2) := by
  unfold gamma0CuspTailMass
  let B := ((N : ℝ)^2/Y^2)*(((N : ℝ)+1)*‖u‖^2)
  calc
    _ ≤ ∑ _q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (B+B) :=
      Finset.sum_le_sum (fun q _ => add_le_add
        (gamma0TruncatedMeanZeroEnergy_tail_bound N A hA u q.out hY hAY)
        (gamma0TruncatedMeanZeroEnergy_tail_bound N A hA u (ModularGroup.T*q.out) hY hAY))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp only [B]
      ring

def gamma0TruncatedMassInclusion (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A) :
    gamma0TruncatedMeanZeroEnergy N A hA →L[ℂ] Gamma0RegionL2 N :=
  (gamma0EnergyInclusion N).comp (gamma0TruncatedMeanZeroEnergy N A hA).subtypeL

/-- Every positive tolerance admits a genuine compact finite-chart mass
approximant, with its operator-norm error proved from the actual cusp tails. -/
theorem gamma0TruncatedMassInclusion_compact_approx (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : gamma0EnergySpace N →L[ℝ] Gamma0RegionL2 N,
      IsCompactOperator K ∧ ∀ u : gamma0TruncatedMeanZeroEnergy N A hA,
        ‖gamma0TruncatedMassInclusion N A hA u-K u.val‖ ≤ ε*‖u‖ := by
  let D : ℝ := 2*(Fintype.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ)*
    (N : ℝ)^2*((N : ℝ)+1)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let C := Real.sqrt D+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hDC : D ≤ C^2 := by
    have hs := Real.sq_sqrt hD
    have hn := Real.sqrt_nonneg D
    dsimp only [C]
    nlinarith
  let Y := max 1 A+C/ε
  have hY : 1 ≤ Y := (le_max_left (1:ℝ) A).trans
    (le_add_of_nonneg_right (div_nonneg hC.le hε.le))
  have hAY : A≤Y := (le_max_right (1:ℝ) A).trans
    (le_add_of_nonneg_right (div_nonneg hC.le hε.le))
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  obtain ⟨R0,a,b,φ,ha,hab,hs,hplateau,_,hres⟩ := gamma0TruncatedCore_cutoff N Y
  let K := gamma0CompactMassMap φ ha hab hs N
  have hK : IsCompactOperator K := gamma0CompactMassMap_compact φ ha hab hs N
  have hpoint (u : gamma0TruncatedMeanZeroEnergy N A hA) :
      ‖gamma0TruncatedMassInclusion N A hA u-K u.val‖ ≤ (C/Y)*‖u‖ := by
    have hbound := (gamma0CompactMassMap_remainder_le_cusp_tails φ ha hab hs N Y hY
      hplateau hres u.val).trans (gamma0CuspTailMass_truncated_le N A hA Y hY hAY u)
    have he : 2*(Fintype.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ)*
        ((N : ℝ)^2/Y^2)*(((N : ℝ)+1)*‖u‖^2) = (D/Y^2)*‖u‖^2 := by
      dsimp only [D]
      ring
    rw [he] at hbound
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (div_nonneg hC.le hYpos.le) (norm_nonneg _))).mp
    calc
      _ ≤ (D/Y^2)*‖u‖^2 := hbound
      _ ≤ (C^2/Y^2)*‖u‖^2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hDC (sq_nonneg _)) (sq_nonneg _)
      _ = ((C/Y)*‖u‖)^2 := by rw [mul_pow, div_pow]
  have hratio : C/Y < ε := by
    apply (div_lt_iff₀ hYpos).mpr
    have he : ε*Y = ε*max 1 A+C := by
      dsimp only [Y]
      field_simp [ne_of_gt hε]
    rw [he]
    nlinarith [le_max_left (1:ℝ) A]
  exact ⟨K,hK,fun u => (hpoint u).trans
    (mul_le_mul_of_nonneg_right hratio.le (norm_nonneg _))⟩

/-- Compactness is discharged by genuine norm approximation with the actual
localizations and the actual truncated constant-mode cusp-tail estimate. -/
theorem gamma0TruncatedMassInclusion_compact (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A) :
    IsCompactOperator (gamma0TruncatedMassInclusion N A hA) := by
  have ht : TotallyBounded (gamma0TruncatedMassInclusion N A hA ''
      Metric.closedBall 0 1) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨K,hK,hnear⟩ := gamma0TruncatedMassInclusion_compact_approx N A hA (half_pos hε)
    obtain ⟨t,ht,hcover⟩ := Metric.totallyBounded_iff.mp
      (hK.isCompact_closure_image_closedBall 1).totallyBounded (ε/2) (half_pos hε)
    refine ⟨t,ht,?_⟩
    rintro _ ⟨u,hu,rfl⟩
    have hu' : ‖u‖ ≤ 1 := (mem_closedBall_zero_iff).mp hu
    have hmem : K u.val ∈ closure (K '' Metric.closedBall 0 1) :=
      subset_closure ⟨u.val, mem_closedBall_zero_iff.mpr hu',rfl⟩
    obtain ⟨z,hz,hzball⟩ := Set.mem_iUnion₂.mp (hcover hmem)
    apply Set.mem_iUnion₂.mpr
    refine ⟨z,hz,?_⟩
    have hdist : dist (gamma0TruncatedMassInclusion N A hA u) (K u.val) ≤ ε/2 := by
      rw [dist_eq_norm]
      exact (hnear u).trans (by nlinarith [norm_nonneg u])
    have hzdist : dist (K u.val) z < ε/2 := hzball
    exact (dist_triangle _ (K u.val) z).trans_lt (by linarith)
  exact (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
    (gamma0TruncatedMassInclusion N A hA)).mpr
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ zero_lt_one,
      ht.closure.isCompact_of_isClosed isClosed_closure⟩

end ArtinMatthews
