module

public import ArtinMatthews.CubicThetaCircleVoronoi
public import ArtinMatthews.CircleVoronoiAverage
public import ArtinMatthews.CircleThetaErrorRate


set_option backward.privateInPublic true
@[expose] public section

/-! Reduction of the genuine shifted theta source to the nonzero dual sum.
The two residual terms here are precisely the detector error and zero dual
frequency, whose explicit decay estimates are already proved separately. -/

noncomputable section
open Complex UpperHalfPlane Set OAI
open scoped MatrixGroups ContDiff BigOperators
namespace ArtinMatthews

local instance : FunLike (ℍ → ℂ) ℍ ℂ := ⟨id, Function.injective_id⟩

def thetaShiftedFiniteSum (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 T1 T2 : ℕ) (H1 H2 : ℝ → ℂ) : ℂ :=
  ∑ n ∈ (Finset.range (T1 + 1)).filter (fun n => m1*n+1 ≤ T1 ∧ m2*n+1 ≤ T2),
    cuspSourcePair (heckeTheta χ) H1 H2 (m1*n+1, m2*n+1)

theorem circleThetaSourceError_eq_dual_difference
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n = idealThetaCoeff χ n)
    (m1 m2 T1 T2 L : ℕ) (hL : 0 < L)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hne : m1 ≠ m2)
    (hsq1 : Squarefree m1) (hsq2 : Squarefree m2)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ)
    (hs1 : ContDiff ℝ ∞ (fun x => W1 (x / K1)))
    (hs2 : ContDiff ℝ ∞ (fun x => W2 (x / K2)))
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hv1 : v1 ≤ T1) (hv2 : v2 ≤ T2)
    (hw1 : Function.support (fun x => W1 (x / K1)) ⊆ Icc u1 v1)
    (hw2 : Function.support (fun x => W2 (x / K2)) ⊆ Icc u2 v2) :
    let D := shiftedCommonPrimePart m1 m2
    let m3 := m1 / m1.gcd m2
    let m4 := m2 / m1.gcd m2
    circleThetaSourceError χ m1 m2 T1 T2 (fun x => W1 (x / K1)) (fun x => W2 (x / K2))
      (N * D^2) (m3*m4) L =
      ‖thetaDualCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L -
        thetaShiftedFiniteSum χ m1 m2 T1 T2 (fun x => W1 (x / K1)) (fun x => W2 (x / K2))‖ := by
  intro D m3 m4
  have hpair : cuspSourcePair f (fun x => W1 (x / K1)) (fun x => W2 (x / K2)) =
      cuspSourcePair (heckeTheta χ) (fun x => W1 (x / K1)) (fun x => W2 (x / K2)) := by
    funext k
    unfold cuspSourcePair
    change (qExpansion 1 f).coeff k.1 * (qExpansion 1 f).coeff k.2 *
      W1 ((k.1 : ℝ) / K1) * W2 ((k.2 : ℝ) / K2) =
      (qExpansion 1 (heckeTheta χ)).coeff k.1 * (qExpansion 1 (heckeTheta χ)).coeff k.2 *
        W1 ((k.1 : ℝ) / K1) * W2 ((k.2 : ℝ) / K2)
    rw [hcoeff, hcoeff, heckeTheta_qExpansion_coeff, heckeTheta_qExpansion_coeff]
  have hv := circle_weightOne_voronoi_admissible N hN f m1 m2 T1 T2 L hL hm1 hm2 hne
    hsq1 hsq2 (circleSmoothWeight L) (fun x => W1 (x / K1)) (fun x => W2 (x / K2))
    hs1 hs2 u1 v1 u2 v2 hu1 hu2 hv1 hv2 hw1 hw2
  dsimp only at hv
  rw [hpair] at hv
  simp_rw [circleVoronoiDual_eq_thetaDualNormalized N f χ hcoeff] at hv
  change circleThetaSourceError _ _ _ _ _ _ _ _ _ _ = _
  unfold circleThetaSourceError thetaShiftedFiniteSum
  dsimp only
  rw [hv]
  rfl

theorem thetaShiftedFiniteSum_nonzero_error
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n = idealThetaCoeff χ n)
    (m1 m2 T1 T2 L : ℕ) (hL : 0 < L)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hne : m1 ≠ m2)
    (hsq1 : Squarefree m1) (hsq2 : Squarefree m2)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2)
    (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hW1 : Function.support W1 ⊆ Icc 0 B1) (hW2 : Function.support W2 ⊆ Icc 0 B2)
    (hs1 : ContDiff ℝ ∞ (fun x => W1 (x / K1)))
    (hs2 : ContDiff ℝ ∞ (fun x => W2 (x / K2)))
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hv1 : v1 ≤ T1) (hv2 : v2 ≤ T2)
    (hw1 : Function.support (fun x => W1 (x / K1)) ⊆ Icc u1 v1)
    (hw2 : Function.support (fun x => W2 (x / K2)) ⊆ Icc u2 v2) :
    let D := shiftedCommonPrimePart m1 m2
    let m3 := m1 / m1.gcd m2
    let m4 := m2 / m1.gcd m2
    ‖thetaShiftedFiniteSum χ m1 m2 T1 T2 (fun x => W1 (x / K1)) (fun x => W2 (x / K2)) -
        thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L‖ ≤
      circleThetaSourceError χ m1 m2 T1 T2 (fun x => W1 (x / K1)) (fun x => W2 (x / K2))
        (N * D^2) (m3*m4) L +
      ‖thetaDualZeroCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L‖ := by
  intro D m3 m4
  have he := circleThetaSourceError_eq_dual_difference N hN f χ hcoeff
    m1 m2 T1 T2 L hL hm1 hm2 hne hsq1 hsq2 W1 W2 K1 K2
    hs1 hs2 u1 v1 u2 v2 hu1 hu2 hv1 hv2 hw1 hw2
  dsimp only at he
  rw [he]
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (thetaShiftedFiniteSum χ m1 m2 T1 T2 (fun x => W1 (x / K1)) (fun x => W2 (x / K2)))
    (thetaDualCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L)
    (thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L)
  rw [norm_sub_rev (thetaShiftedFiniteSum χ m1 m2 T1 T2
      (fun x => W1 (x / K1)) (fun x => W2 (x / K2)))
    (thetaDualCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L)] at ht
  have hz : thetaDualCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L -
      thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L =
      thetaDualZeroCircleAverage χ W1 W2 K1 K2 D m3 m4 (N * D^2) (m3*m4) L := by
    rw [thetaDualCircleAverage_split χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2,
      add_sub_cancel_right]
  rw [hz] at ht
  exact ht

end ArtinMatthews
