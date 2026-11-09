module

public import ArtinMatthews.CircleVoronoiModulus
public import ArtinMatthews.CubicThetaDualSplit
public import ArtinMatthews.CubicTheta


set_option backward.privateInPublic true
@[expose] public section

/-! Identify the exact theta dual sum with the dual expression in the proved
cusp-form Voronoi formula. Instantiation still requires the genuine cusp form
whose underlying function is the actual Hecke theta; no modularity is assumed
for an arbitrary coefficient sequence. -/

noncomputable section
open Complex UpperHalfPlane OAI
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspBesselPair_eq_thetaBesselCoeff
    {F : Type*} [FunLike F ℍ ℂ] (f : F)
    (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n = idealThetaCoeff χ n)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (q : ℕ) (k : ℕ × ℕ) :
    cuspBesselPair f q (fun x => W1 (x / K1)) (fun x => W2 (x / K2)) k =
      thetaBesselCoeff χ W1 K1 ((q : ℝ)^2) k.1 *
        thetaBesselCoeff χ W2 K2 ((q : ℝ)^2) k.2 := by
  unfold cuspBesselPair cuspSourcePair thetaBesselCoeff
  rw [hcoeff k.1, hcoeff k.2]
  ring

theorem circleVoronoiDual_eq_thetaDualNormalized
    (N : ℕ) [NeZero N] (f : CuspForm (cubicThetaKernel N) 1)
    (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n = idealThetaCoeff χ n)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (m1 m2 q : ℕ) :
    circleVoronoiDual N f m1 m2 q (fun x => W1 (x / K1)) (fun x => W2 (x / K2)) =
      thetaDualNormalized χ W1 W2 K1 K2 (shiftedCommonPrimePart m1 m2)
        (m1 / m1.gcd m2) (m2 / m1.gcd m2) q := by
  unfold circleVoronoiDual thetaDualNormalized
  split_ifs with hq
  · rfl
  · dsimp only
    congr 1
    apply tsum_congr
    intro k
    rw [cuspBesselPair_eq_thetaBesselCoeff f χ hcoeff]
    rfl

theorem circleVoronoiDual_eq_actualHeckeTheta
    (N : ℕ) [NeZero N] (f : CuspForm (cubicThetaKernel N) 1)
    (χ : SevenEighths.HeckeFamily.Character) (hf : (fun τ => f τ) = heckeTheta χ)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (m1 m2 q : ℕ) :
    circleVoronoiDual N f m1 m2 q (fun x => W1 (x / K1)) (fun x => W2 (x / K2)) =
      thetaDualNormalized χ W1 W2 K1 K2 (shiftedCommonPrimePart m1 m2)
        (m1 / m1.gcd m2) (m2 / m1.gcd m2) q := by
  apply circleVoronoiDual_eq_thetaDualNormalized N f χ
  intro n
  change (qExpansion 1 (fun τ => f τ)).coeff n = _
  rw [hf]
  exact heckeTheta_qExpansion_coeff χ n

end ArtinMatthews
