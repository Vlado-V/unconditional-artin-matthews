module

public import ArtinMatthews.SpectralGamma0TailComparison
public import ArtinMatthews.SpectralGamma0AllHeightMeanZero
public import ArtinMatthews.SpectralGamma0TruncatedCore
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compact mass inclusion on the constructed all-height mean-zero
energy space. Identification with the full automorphic cusp space is separate. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspTailMass_allHeight_le (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (u : gamma0AllHeightMeanZeroEnergy N) :
    gamma0CuspTailMass N Y hY u.val ≤
      2*(Fintype.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ)*
        ((N : ℝ)^2/Y^2)*(((N : ℝ)+1)*‖u‖^2) := by
  unfold gamma0CuspTailMass
  let B := ((N : ℝ)^2/Y^2)*(((N : ℝ)+1)*‖u‖^2)
  calc
    _ ≤ ∑ _q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (B+B) :=
      Finset.sum_le_sum (fun q _ => add_le_add
        (gamma0AllHeightMeanZeroEnergy_tail_bound N q.out u hY)
        (gamma0AllHeightMeanZeroEnergy_tail_bound N (ModularGroup.T*q.out) u hY))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp only [B]
      ring

def gamma0AllHeightMassInclusion (N : ℕ) [NeZero N] :
    gamma0AllHeightMeanZeroEnergy N →L[ℂ] Gamma0RegionL2 N :=
  (gamma0EnergyInclusion N).comp (gamma0AllHeightMeanZeroEnergy N).subtypeL

/-- Every positive tolerance admits a genuine compact finite-chart mass
approximant, with its operator-norm error proved from the actual cusp tails. -/
theorem gamma0AllHeightMassInclusion_compact_approx (N : ℕ) [NeZero N]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : gamma0EnergySpace N →L[ℝ] Gamma0RegionL2 N,
      IsCompactOperator K ∧ ∀ u : gamma0AllHeightMeanZeroEnergy N,
        ‖gamma0AllHeightMassInclusion N u-K u.val‖ ≤ ε*‖u‖ := by
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
  let Y := 1+C/ε
  have hY : 1 ≤ Y := by dsimp only [Y]; exact le_add_of_nonneg_right (div_nonneg hC.le hε.le)
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  obtain ⟨A,a,b,φ,ha,hab,hs,hplateau,_,hres⟩ := gamma0TruncatedCore_cutoff N Y
  let K := gamma0CompactMassMap φ ha hab hs N
  have hK : IsCompactOperator K := gamma0CompactMassMap_compact φ ha hab hs N
  have hpoint (u : gamma0AllHeightMeanZeroEnergy N) :
      ‖gamma0AllHeightMassInclusion N u-K u.val‖ ≤ (C/Y)*‖u‖ := by
    have hbound := (gamma0CompactMassMap_remainder_le_cusp_tails φ ha hab hs N Y hY
      hplateau hres u.val).trans (gamma0CuspTailMass_allHeight_le N Y hY u)
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
    have he : ε*Y = ε+C := by
      dsimp only [Y]
      field_simp [ne_of_gt hε]
    rw [he]
    linarith
  exact ⟨K,hK,fun u => (hpoint u).trans
    (mul_le_mul_of_nonneg_right hratio.le (norm_nonneg _))⟩

/-- Compactness is discharged by genuine norm approximation with the actual
localizations and the actual all-height mean-zero cusp-tail estimate. -/
theorem gamma0AllHeightMassInclusion_compact (N : ℕ) [NeZero N] :
    IsCompactOperator (gamma0AllHeightMassInclusion N) := by
  have ht : TotallyBounded (gamma0AllHeightMassInclusion N ''
      Metric.closedBall 0 1) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨K,hK,hnear⟩ := gamma0AllHeightMassInclusion_compact_approx N (half_pos hε)
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
    have hdist : dist (gamma0AllHeightMassInclusion N u) (K u.val) ≤ ε/2 := by
      rw [dist_eq_norm]
      exact (hnear u).trans (by nlinarith [norm_nonneg u])
    have hzdist : dist (K u.val) z < ε/2 := hzball
    exact (dist_triangle _ (K u.val) z).trans_lt (by linarith)
  exact (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
    (gamma0AllHeightMassInclusion N)).mpr
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ zero_lt_one,
      ht.closure.isCompact_of_isClosed isClosed_closure⟩

end ArtinMatthews
