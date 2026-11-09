module

public import ArtinMatthews.SpectralCuspInteriorParseval
public import ArtinMatthews.SpectralGamma0GreenSpectralBound
public import ArtinMatthews.SpectralGamma0LocalFourierRepresentative


set_option backward.privateInPublic true
@[expose] public section

/-! Honest period-N Fourier representatives of the actual completed cusp coefficients. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

def gamma0FullCuspidalFourierRepresentative (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N) (n : ℤ) : ℝ → ℂ :=
  cuspInteriorFourierCoefficient (N:ℝ) n (gamma0FullCuspidalPlaneRepresentative N r Y hY i)

theorem gamma0FullCuspidalFourierRepresentative_native_ae (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N) (n : ℤ) :
    gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val
      =ᵐ[volume.restrict (Ioi Y)] gamma0FullCuspidalFourierRepresentative N r Y hY i n :=
  gamma0CuspLocalFourierRepresentative_ae N r Y hY n _ _
    (gamma0FullCuspidalPlaneRepresentative_spec N r Y hY i).2.1

theorem gamma0FullCuspidalFourierRepresentative_twoCell_ae (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N) (n : ℤ) :
    gamma0CuspTwoCellFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val
      =ᵐ[volume.restrict (Ioi Y)] gamma0FullCuspidalFourierRepresentative N r Y hY i n := by
  have he : (fun y => gamma0CuspTwoCellFourierCoefficient N r Y hY n
      (gamma0FullCuspidalSpectralBasis N i).val y) =ᵐ[volume.restrict (Ioi Y)]
      (fun y => gamma0CuspFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val y) :=
    (spectralHorizontal_cuspVertical_ae_iff hY).mp
      (gamma0CuspTwoCellFourierCoefficient_ae N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val)
  exact he.trans (gamma0FullCuspidalFourierRepresentative_native_ae N r Y hY i n)

theorem gamma0FullCuspidalFourierRepresentative_continuousOn (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N) (n : ℤ) :
    ContinuousOn (gamma0FullCuspidalFourierRepresentative N r Y hY i n) (Ioi Y) :=
  cuspInteriorFourierCoefficient_continuousOn (N:ℝ) Y (Nat.cast_pos.mpr (NeZero.pos N)) hY.le n _
    (gamma0FullCuspidalPlaneRepresentative_spec N r Y hY i).1

theorem gamma0FullCuspidalFourierRepresentative_parseval (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N)
    (y : ℝ) (hy : Y < y) :
    HasSum (fun n : ℤ => ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2)
      ((N:ℝ)⁻¹*(∫ x in (0:ℝ)..(N:ℝ),
        ‖gamma0FullCuspidalPlaneRepresentative N r Y hY i (x+(N:ℝ)/2,y)‖^2)) := by
  have hN : 0 < (N:ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  exact cuspInteriorFourierCoefficient_hasSum_sq (N:ℝ) hN _ y
    (cuspInterior_shift_slice_memLp (N:ℝ) Y hN _
      (gamma0FullCuspidalPlaneRepresentative_spec N r Y hY i).1 y hy)

theorem gamma0FullCuspidalFourierRepresentative_frequency_window (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N)
    (y : ℝ) (hy : Y < y) (s : Finset ℤ) :
    (∑ n ∈ s, ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2) ≤
      (N:ℝ)⁻¹*(∫ x in (0:ℝ)..(N:ℝ),
        ‖gamma0FullCuspidalPlaneRepresentative N r Y hY i (x+(N:ℝ)/2,y)‖^2) := by
  have h := gamma0FullCuspidalFourierRepresentative_parseval N r Y hY i y hy
  exact (h.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)).trans_eq h.tsum_eq

end ArtinMatthews
