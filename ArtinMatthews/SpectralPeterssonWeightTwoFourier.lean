module

public import ArtinMatthews.SpectralWeightTwoFourierCalculus
public import ArtinMatthews.SpectralPeterssonHeckeHolomorphic
public import ArtinMatthews.SpectralPeterssonFourierGeometric


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Set MeasureTheory UpperHalfPlane Matrix
open scoped MatrixGroups UpperHalfPlane Manifold
noncomputable section

theorem gamma0PeterssonWeightTwoModulus_fourier (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (m n : ℕ+) (c : Ioi (0 : ℕ)) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (gamma0PeterssonHeckeModulus N b a 0 m c) n y hy =
      gamma0PeterssonPositiveModulusTerm N b a 2 m n c := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let F (R : gamma0TrueWidthReducedMatrix N b a c.val) :=
    spectralPeterssonHeckeOrbital 0 m (gamma0TrueWidthMatrix N b a R.val)
  have hC (R : gamma0TrueWidthReducedMatrix N b a c.val) :
      0 < gamma0TrueWidthMatrix N b a R.val 1 0 := by
    rw [gamma0TrueWidthMatrix_lower N b a R.val (c.val : ℤ) R.property.2.1]
    exact gamma0TrueWidthModulus_pos N b a (Nat.cast_pos.mpr c.property)
  have hF (R : gamma0TrueWidthReducedMatrix N b a c.val) : Continuous (F R) :=
    (spectralPeterssonHeckeOrbital_zero_mdifferentiable m _ (hC R)).continuous
  change spectralPeterssonFourierAtHeight (fun z => ∑ R, F R z) n y hy = _
  rw [spectralWeightTwoFourier_sum F hF n y hy]
  have hrow (R : gamma0TrueWidthReducedMatrix N b a c.val) :
      spectralPeterssonFourierAtHeight (F R) n y hy =
        spectralPeterssonWeylOrbitalCoefficient 2 m n (gamma0TrueWidthMatrix N b a R.val) := by
    have heq : F R = fun z => ∑' l : ℤ,
        spectralHolomorphicSlash 2 (gamma0TrueWidthMatrix N b a R.val * realTranslation (l : ℝ))
          (spectralHolomorphicCuspSeed (m : ℕ)) z := by
      funext z
      dsimp only [F, spectralPeterssonHeckeOrbital]
      rw [spectralPeterssonHeckeSeed_zero]
    rw [heq]
    exact spectralPeterssonWeylOrbital_fourier 2 (by norm_num) m n _ (hC R) y hy
  simp_rw [hrow]
  exact gamma0PeterssonWeylOrbitalCoefficient_sum N b a 2 m n c

theorem gamma0PeterssonWeightTwoZeroSector_fourier (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (m n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (gamma0PeterssonHeckeZeroSector N b a 0 m) n y hy =
      gamma0PeterssonZeroFourierTerm N b a 2 m n y hy := by
  classical
  rcases isEmpty_or_nonempty (Gamma0PeterssonZeroRow N b a) with h | h
  · let _ := h
    simp only [gamma0PeterssonHeckeZeroSector, gamma0PeterssonZeroFourierTerm, tsum_empty,
      spectralPeterssonFourierAtHeight, zero_mul, integral_zero]
  · let p : Gamma0PeterssonZeroRow N b a := h.some
    have hzero : gamma0PeterssonHeckeZeroSector N b a 0 m =
        gamma0PeterssonHeckeSignedSummand N b a 0 m p.val.val := by
      funext z
      unfold gamma0PeterssonHeckeZeroSector
      exact tsum_eq_single p (fun q hq => (hq (Subsingleton.elim q p)).elim)
    have hcoeff : gamma0PeterssonZeroFourierTerm N b a 2 m n y hy =
        spectralPeterssonFourierAtHeight (gamma0PeterssonSignedSummand N b a 2 (m : ℕ) p.val.val) n y hy := by
      unfold gamma0PeterssonZeroFourierTerm
      exact tsum_eq_single p (fun q hq => (hq (Subsingleton.elim q p)).elim)
    rw [hzero, hcoeff]
    congr 1
    simp only [gamma0PeterssonHeckeSignedSummand, gamma0PeterssonHeckeMatrixSeed,
      spectralPeterssonHeckeSeed_zero, gamma0PeterssonSignedSummand, gamma0PeterssonMatrixSeed]

theorem gamma0PeterssonWeightTwoFourierAtHeight_geometric (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (m n : ℕ+) (y : ℝ) (hy : 0 < y) :
    Summable (gamma0PeterssonPositiveModulusTerm N b 1 2 m n) ∧
      spectralPeterssonFourierAtHeight (gamma0PeterssonHeckeGrouped N b 1 0 m) n y hy =
        gamma0PeterssonZeroFourierTerm N b 1 2 m n y hy +
          ∑' c, gamma0PeterssonPositiveModulusTerm N b 1 2 m n c := by
  let F (c : Ioi (0 : ℕ)) := gamma0PeterssonHeckeModulus N b 1 0 m c
  obtain ⟨D, hD, hbound⟩ := gamma0PeterssonHeckeModulus_majorant N b m y hy
  let u (c : Ioi (0 : ℕ)) : ℝ := (D / y) * (c.val : ℝ) ^ (-(5 / 4 : ℝ))
  have hu : Summable u := gamma0PeterssonHecke_rawModulusMajorant_summable.mul_left (D / y)
  have hF (c : Ioi (0 : ℕ)) : Continuous (F c) :=
    (gamma0PeterssonHeckeModulus_zero_mdifferentiable N b 1 m c).continuous
  have hrow (c : Ioi (0 : ℕ)) (x : ℝ) (_hx : x ∈ Ioc (0 : ℝ) 1) :
      ‖F c (spectralPeterssonHeightPoint x y hy)‖ ≤ u c := by
    have h := hbound 0 c (spectralPeterssonHeightPoint x y hy) ⟨le_rfl, zero_le_one⟩ le_rfl
    change ‖F c (spectralPeterssonHeightPoint x y hy)‖ * y ≤
      D * (c.val : ℝ) ^ (-(5 / 4 : ℝ)) at h
    dsimp only [u]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hy).mpr h
  have hsum := spectralPeterssonFourierAtHeight_tsum F n y hy u hu hF hrow
  have hzero : Continuous (gamma0PeterssonHeckeZeroSector N b 1 0 m) :=
    (gamma0PeterssonHeckeZeroSector_zero_mdifferentiable N b 1 m).continuous
  have hsum_cont : Continuous (fun z => ∑' c, F c z) := by
    have h := (gamma0PeterssonHeckeGrouped_zero_mdifferentiable N b m).continuous.sub hzero
    change Continuous (fun z => gamma0PeterssonHeckeGrouped N b 1 0 m z -
      gamma0PeterssonHeckeZeroSector N b 1 0 m z) at h
    have heq : (fun z => gamma0PeterssonHeckeGrouped N b 1 0 m z -
        gamma0PeterssonHeckeZeroSector N b 1 0 m z) = (fun z => ∑' c, F c z) := by
      funext z
      simp only [gamma0PeterssonHeckeGrouped, F, add_sub_cancel_left]
    rwa [heq] at h
  refine ⟨hsum.1.congr (fun c => gamma0PeterssonWeightTwoModulus_fourier N b 1 m n c y hy), ?_⟩
  change spectralPeterssonFourierAtHeight (fun z =>
    gamma0PeterssonHeckeZeroSector N b 1 0 m z + ∑' c, F c z) n y hy = _
  rw [spectralWeightTwoFourier_add _ _ hzero hsum_cont n y hy, hsum.2,
    gamma0PeterssonWeightTwoZeroSector_fourier N b 1 m n y hy]
  congr 1
  exact tsum_congr (fun c => gamma0PeterssonWeightTwoModulus_fourier N b 1 m n c y hy)

end
end ArtinMatthews
