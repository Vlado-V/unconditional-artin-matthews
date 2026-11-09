module

public import ArtinMatthews.SpectralGamma0FiniteMassCombination
public import ArtinMatthews.SpectralGamma0EllipticStripPeriod


set_option backward.privateInPublic true
@[expose] public section

/-! Finite spectral Green sums are honest smooth representatives of the actual Green image. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0CuspTwoCellCoordinateRestriction_real_sum_ae
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ)
    (f : Gamma0AllHeightSpectralIndex N → Gamma0RegionL2 N) :
    ∀ᵐ p ∂volume, (0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) →
      gamma0CuspTwoCellCoordinateRestriction N r Y hY (∑ i ∈ s, c i • f i) p =
        ∑ i ∈ s, c i • gamma0CuspTwoCellCoordinateRestriction N r Y hY (f i) p := by
  let R := gamma0CuspTwoCellCoordinateRestriction N r Y hY
  have hsum : R (∑ i ∈ s, c i • f i) =ᵐ[cuspStripMeasure (2*(N:ℝ)) Y]
      fun p => ∑ i ∈ s, c i • R (f i) p := by
    rw [map_sum]
    simp_rw [map_smul]
    have hs := Lp.coeFn_finsetSum s (fun i => c i • R (f i))
    have hc := ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (R (f i)))
    filter_upwards [hs,hc] with p hp hcp
    simp only [Finset.sum_apply] at hp
    exact hp.trans (Finset.sum_congr rfl fun i _ => hcp i)
  have hS : MeasurableSet (Ioc 0 (2*(N:ℝ)) ×ˢ Ioi Y) := measurableSet_Ioc.prod measurableSet_Ioi
  have hv := (cuspStrip_volume_absolutelyContinuous (2*(N:ℝ)) hY).ae_eq hsum
  filter_upwards [(ae_restrict_iff' hS).mp hv] with p hp
  exact fun h => hp ⟨⟨h.1,h.2.1.le⟩,h.2.2⟩

def gamma0FiniteGreenPlane (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ)
    (p : ℝ × ℝ) : ℂ :=
  ∑ i ∈ s, (i.1.re*c i) • gamma0FullCuspidalPlaneRepresentative N r Y hY i p

theorem gamma0FiniteGreenPlane_smooth (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    ContDiffOn ℝ ∞ (gamma0FiniteGreenPlane N r Y hY s c)
      {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2} := by
  apply ContDiffOn.sum
  intro i _
  exact (contDiffOn_const (c := (i.1.re*c i : ℝ))).smul
    (gamma0FullCuspidalPlaneRepresentative_spec N r Y hY i).1

theorem gamma0FiniteGreenPlane_mass_ae (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    ∀ᵐ p ∂volume, (0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) →
      gamma0FiniteGreenPlane N r Y hY s c p =
        gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0Green N (gamma0FiniteMassCombination N s c)) p := by
  have hs := gamma0CuspTwoCellCoordinateRestriction_real_sum_ae N r Y hY s
    (fun i => i.1.re*c i) (fun i => (gamma0FullCuspidalSpectralBasis N i).val)
  have hF := ae_all_iff.mpr (fun i => (gamma0FullCuspidalPlaneRepresentative_spec N r Y hY i).2.1)
  filter_upwards [hs,hF] with p hp hFp
  intro hpΩ
  rw [gamma0Green_finiteMassCombination,gamma0FiniteMassCombination_eq_real_sum]
  change (∑ i ∈ s, (i.1.re*c i) • gamma0FullCuspidalPlaneRepresentative N r Y hY i p) = _
  exact (Finset.sum_congr rfl (fun i _ => congrArg (fun z : ℂ => (i.1.re*c i) • z)
    (hFp i hpΩ))).trans (hp hpΩ).symm

end ArtinMatthews
