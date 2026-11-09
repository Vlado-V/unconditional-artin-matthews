module

public import ArtinMatthews.ShiftedVoronoiResidue
public import ArtinMatthews.ShiftedVoronoiCircleDivisibility
public import Mathlib.Analysis.Normed.Ring.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-!
# The separable double Voronoi transformation

Both one-variable identities are actual theorems for an arithmetic cusp form.
Their absolutely convergent tensor product has the exact q⁻² normalization and
negative inverse phases. These are products, not sesquilinear correlations;
using this identity for a correlation requires real coefficients or a separate
conjugation argument.
-/

noncomputable section
open Complex UpperHalfPlane Set
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

set_option maxHeartbeats 800000 in
/-- Absolute convergence of the two-variable Bessel series, independent of
any assumed Voronoi or spectral identity. -/
theorem weightOne_double_dual_summable
    (N : ℕ) [NeZero N] (f : CuspForm (cubicThetaKernel N) 1)
    (q : ℕ) [NeZero q] (a1 a2 : ZMod q)
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    Summable (fun k : ℕ × ℕ ↦
      (cuspResidueCoeff f q a1 k.1 * weightOneBesselTransform H1 ((k.1 : ℝ) / (q : ℝ)^2)) *
      (cuspResidueCoeff f q a2 k.2 * weightOneBesselTransform H2 ((k.2 : ℝ) / (q : ℝ)^2))) := by
  have h1 := weightOne_dual_residue_summable f (cubicThetaKernel_periodOne N) q a1
    H1 hs1 u1 v1 hu1 hw1
  have h2 := weightOne_dual_residue_summable f (cubicThetaKernel_periodOne N) q a2
    H2 hs2 u2 v2 hu2 hw2
  exact summable_mul_of_summable_norm
    (f := fun n : ℕ ↦ cuspResidueCoeff f q a1 n *
      weightOneBesselTransform H1 ((n : ℝ) / (q : ℝ)^2))
    (g := fun n : ℕ ↦ cuspResidueCoeff f q a2 n *
      weightOneBesselTransform H2 ((n : ℝ) / (q : ℝ)^2)) h1.norm h2.norm

/-- Tensoring the proved one-variable formulas preserves the exact q⁻² factor.
No source/dual summability or transformed identity is an input hypothesis. -/
theorem weightOne_double_voronoi_residue
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (q : ℕ) [NeZero q] (hlevel : N ∣ q) (a1 a2 : ℤ)
    (ha1 : IsUnit (a1 : ZMod q)) (ha2 : IsUnit (a2 : ZMod q))
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    (∑' k : ℕ × ℕ, (cuspResidueCoeff f q (a1 : ZMod q) k.1 * H1 k.1) *
      (cuspResidueCoeff f q (a2 : ZMod q) k.2 * H2 k.2)) =
        (cubicThetaNebentypus a1 * cubicThetaNebentypus a2 / (q : ℂ)^2) *
          ∑' k : ℕ × ℕ,
            (cuspResidueCoeff f q (-(a1 : ZMod q)⁻¹) k.1 *
              weightOneBesselTransform H1 ((k.1 : ℝ) / (q : ℝ)^2)) *
            (cuspResidueCoeff f q (-(a2 : ZMod q)⁻¹) k.2 *
              weightOneBesselTransform H2 ((k.2 : ℝ) / (q : ℝ)^2)) := by
  have hS1 := weightOne_source_residue_summable f (cubicThetaKernel_periodOne N) q (a1 : ZMod q)
    H1 hs1 u1 v1 hu1 hw1
  have hS2 := weightOne_source_residue_summable f (cubicThetaKernel_periodOne N) q (a2 : ZMod q)
    H2 hs2 u2 v2 hu2 hw2
  have hD1 := weightOne_dual_residue_summable f (cubicThetaKernel_periodOne N) q (-(a1 : ZMod q)⁻¹)
    H1 hs1 u1 v1 hu1 hw1
  have hD2 := weightOne_dual_residue_summable f (cubicThetaKernel_periodOne N) q (-(a2 : ZMod q)⁻¹)
    H2 hs2 u2 v2 hu2 hw2
  rw [← tsum_mul_tsum_of_summable_norm hS1.norm hS2.norm,
    weightOne_voronoi_residue N hN f q hlevel a1 ha1 H1 hs1 u1 v1 hu1 hw1,
    weightOne_voronoi_residue N hN f q hlevel a2 ha2 H2 hs2 u2 v2 hu2 hw2,
    ← tsum_mul_tsum_of_summable_norm hD1.norm hD2.norm]
  ring

/-- The product of two residue twists is the ordinary additive character of
the sum of their phases. This explicitly retains the coefficient product. -/
theorem cuspResidueCoeff_product {F : Type*} [FunLike F ℍ ℂ] (f : F)
    (q : ℕ) [NeZero q] (a1 a2 : ZMod q) (k1 k2 : ℕ) (W1 W2 : ℂ) :
    (cuspResidueCoeff f q a1 k1 * W1) * (cuspResidueCoeff f q a2 k2 * W2) =
      (qExpansion 1 f).coeff k1 * (qExpansion 1 f).coeff k2 *
        ZMod.stdAddChar (a1 * (k1 : ZMod q) + a2 * (k2 : ZMod q)) * W1 * W2 := by
  unfold cuspResidueCoeff
  rw [AddChar.map_add_eq_mul]
  ring

set_option maxHeartbeats 800000 in
/-- The exact separable double transform at the circle numerators of (5.7).
The scalar is ψ(−m3*m4)/q², independent of a and j. -/
theorem weightOne_double_voronoi_circle
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (D d q a m3 m4 : ℕ) [NeZero q]
    (hd : 0 < d) (hdD : d ∣ D) (hQ : N*D^2 ∣ q)
    (ha : a.Coprime q) (hm : (m3*m4).Coprime q) (j : ℤ)
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    (∑' k : ℕ × ℕ, (qExpansion 1 f).coeff k.1 * (qExpansion 1 f).coeff k.2 *
      ZMod.stdAddChar (((m4 : ZMod q)*(a : ZMod q)*(1+(j : ZMod q)*((q/d : ℕ) : ZMod q))) * (k.1 : ZMod q) +
        (-(m3 : ZMod q)*(a : ZMod q)) * (k.2 : ZMod q)) * H1 k.1 * H2 k.2) =
      (cubicThetaNebentypus (-(m3 : ℤ)*m4) / (q : ℂ)^2) * ∑' k : ℕ × ℕ,
        (qExpansion 1 f).coeff k.1 * (qExpansion 1 f).coeff k.2 *
          ZMod.stdAddChar (-((m4 : ZMod q)*(a : ZMod q)*(1+(j : ZMod q)*((q/d : ℕ) : ZMod q)))⁻¹ * (k.1 : ZMod q) +
            -(-(m3 : ZMod q)*(a : ZMod q))⁻¹ * (k.2 : ZMod q)) *
          weightOneBesselTransform H1 ((k.1 : ℝ) / (q : ℝ)^2) *
          weightOneBesselTransform H2 ((k.2 : ℝ) / (q : ℝ)^2) := by
  obtain ⟨⟨ha1, ha2⟩, hψ⟩ := doubleVoronoi_circle_arithmetic hd hdD hQ hN ha hm j
  have hlevel : N ∣ q := (dvd_mul_right N (D^2)).trans hQ
  have h1 : IsUnit (((m4 : ℤ)*a*(1+j*(q/d : ℕ)) : ℤ) : ZMod q) := by
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast] using ha1
  have h2 : IsUnit ((-(m3 : ℤ)*a : ℤ) : ZMod q) := by
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_natCast] using ha2
  have hv := weightOne_double_voronoi_residue N hN f q hlevel
    ((m4 : ℤ)*a*(1+j*(q/d : ℕ))) (-(m3 : ℤ)*a) h1 h2
    H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2
  rw [hψ] at hv
  simpa only [cuspResidueCoeff_product, Int.cast_mul, Int.cast_add,
    Int.cast_one, Int.cast_natCast, Int.cast_neg] using hv

end ArtinMatthews
