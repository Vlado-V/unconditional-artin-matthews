module

public import ArtinMatthews.SpectralAmbientEllipticActual
public import ArtinMatthews.SpectralGamma0EllipticBandCutoff
public import ArtinMatthews.SpectralGamma0EllipticPotentialClassical


set_option backward.privateInPublic true
@[expose] public section

/-! Local smooth representatives derived from the actual ambient energy and eigen-equation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem gamma0AmbientEigen_local_potential_data
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (L : ℂ →L[ℝ] ℝ)
    {x : Fin 2 → ℝ} (hx : x ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y) :
    ∃ (W : Set (Fin 2 → ℝ)) (p : H1Pair 1)
      (B : (Fin 2 → ℝ) → ℝ →L[ℝ] ℝ) (hB : SmoothBounded B)
      (M : ℝ) (hM : ∀ y, ‖B y‖ ≤ M),
      IsOpen W ∧ x ∈ W ∧ W ⊆ spectralEllipticOpenStrip (2*(N:ℝ)) Y ∧
      p ∈ H1Zero (univ : Set (Fin 2 → ℝ)) ∧
      WeakDivergenceEquation W p.2
        (fieldMultiplierCLM B hB.1.continuous.aestronglyMeasurable
          (Eventually.of_forall hM) p.1) ∧
      (∀ᵐ y ∂volume, y ∈ W → p.1 y = L (gamma0CuspTwoCellCoordinateRestriction
        N r Y hY (gamma0EnergyInclusion N v) (spectralEllipticCoordinates y))) ∧
      (∀ y ∈ W, ∀ v : ℝ, B y v = eig / (y 1)^2 * v) := by
  let c := (Y+x 1)/2
  let d := x 1+1
  have hYc : Y < c := by dsimp [c]; linarith [hx.2.2]
  have hc : 0 < c := hY.trans hYc
  have hcx : c < x 1 := by dsimp [c]; linarith [hx.2.2]
  have hxd : x 1 < d := by dsimp [d]; linarith
  obtain ⟨A,a,b,φ,ha,hab,hφ,hplateau,_⟩ :=
    exists_spectralEllipticBand_cutoff (w := 2*(N:ℝ)) (c := c) (d := d)
      (by positivity) hc
      (hcx.le.trans hxd.le)
  let W := spectralEllipticOpenStrip (2*(N:ℝ)) Y ∩ {y : Fin 2 → ℝ | c < y 1 ∧ y 1 < d}
  have hW : IsOpen W := (spectralEllipticOpenStrip_isOpen _ _).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt (continuous_apply 1) continuous_const))
  have hxW : x ∈ W := ⟨hx,hcx,hxd⟩
  have hWS : W ⊆ spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d := by
    intro y hy
    exact ⟨⟨hy.1.1,hy.1.2.1.le⟩,hy.2.1.le,hy.2.2.le⟩
  let p := gamma0EllipticPair φ ha hφ r L N v
  let B := spectralEllipticPotentialCoefficient φ ha hφ (eig)
  have hB : SmoothBounded B := spectralEllipticPotentialCoefficient_smoothBounded φ ha hφ _
  obtain ⟨M,hM⟩ := hB.bound
  have he := gamma0AmbientElliptic_weakDivergence φ ha hab hφ r L N v eig hl hG hY hYc hplateau hWS hM
  have hv := gamma0EllipticMass_band_ae φ ha hab hφ r L N hY hYc hplateau
    (gamma0EnergyInclusion N v)
  rw [gamma0EllipticMass_energy φ ha hab hφ r L N] at hv
  have hS : MeasurableSet (spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d) :=
    (spectralEllipticBand_measurable _ _ _).preimage spectralEllipticCoordinates.continuous.measurable
  refine ⟨W,p,B,hB,M,hM,hW,hxW,inter_subset_left,
    gamma0EllipticPair_mem_H1Zero φ ha hφ r L N _,he,?_,?_⟩
  · filter_upwards [(ae_restrict_iff' hS).mp hv] with y hy
    exact fun hyW => hy (hWS hyW)
  · intro y hy v
    exact spectralEllipticPotentialCoefficient_apply_eq φ ha hφ _
      (hY.trans hy.1.2.2) (hplateau _ (hWS hy)) v

theorem gamma0AmbientEigen_local_real_representative
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (L : ℂ →L[ℝ] ℝ) (q : ℕ)
    {x : Fin 2 → ℝ} (hx : x ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y) :
    ∃ (V : Set (Fin 2 → ℝ)) (u : (Fin 2 → ℝ) → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ spectralEllipticOpenStrip (2*(N:ℝ)) Y ∧
      ContDiff ℝ q u ∧ (∀ᵐ y ∂volume, y ∈ V →
        L (gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0EnergyInclusion N v) (spectralEllipticCoordinates y)) = u y) := by
  obtain ⟨W,p,B,hB,M,hM,hW,hxW,hWΩ,hp,he,hpf,_⟩ :=
    gamma0AmbientEigen_local_potential_data N v eig hl hG r Y hY L hx
  obtain ⟨V,u,hV,hxV,hVW,hu,hpu⟩ :=
    spectralElliptic_potential_contDiff_local_representative B hB hM p hp hW he q hxW
  refine ⟨V,u,hV,hxV,hVW.trans hWΩ,hu,?_⟩
  filter_upwards [hpf,hpu] with y hy hz
  exact fun hyV => (hy (hVW hyV)).symm.trans (hz hyV)

theorem gamma0AmbientEigen_real_smooth_classical
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (L : ℂ →L[ℝ] ℝ) :
    ∃ u : (Fin 2 → ℝ) → ℝ,
      ContDiffOn ℝ ∞ u (spectralEllipticOpenStrip (2*(N:ℝ)) Y) ∧
      (∀ᵐ y ∂volume, y ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
        u y = L (gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0EnergyInclusion N v) (spectralEllipticCoordinates y))) ∧
      ∀ y ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y,
        spectralEllipticPositiveLaplacian u y =
          eig / (y 1)^2 * u y := by
  obtain ⟨u,hu,huf⟩ := exists_smoothOn_representative (spectralEllipticOpenStrip_isOpen _ _)
    (fun y => L (gamma0CuspTwoCellCoordinateRestriction N r Y hY
      (gamma0EnergyInclusion N v) (spectralEllipticCoordinates y)))
    (fun q _x hx => gamma0AmbientEigen_local_real_representative N v eig hl hG r Y hY L q hx)
  refine ⟨u,hu,huf,?_⟩
  intro x hx
  obtain ⟨W,p,B,hB,M,hM,hW,hxW,hWΩ,hp,he,hpf,hBv⟩ :=
    gamma0AmbientEigen_local_potential_data N v eig hl hG r Y hY L hx
  obtain ⟨v,hv,hvp,hvPDE⟩ :=
    spectralElliptic_potential_smooth_classical_representative B hB hM p hp hW he
  have huv : EqOn u v W := by
    apply continuous_eqOn_of_local_ae hW (hu.continuousOn.mono hWΩ) hv.continuousOn
    filter_upwards [huf,hpf,hvp] with y h1 h2 h3
    exact fun hyW => (h1 (hWΩ hyW)).trans ((h2 hyW).symm.trans (h3 hyW).symm)
  have hlocal : u =ᶠ[nhds x] v := Filter.eventuallyEq_of_mem (hW.mem_nhds hxW) huv
  rw [spectralEllipticPositiveLaplacian_germ hlocal,huv hxW]
  exact (hvPDE x hxW).trans (hBv x hxW (v x))

end ArtinMatthews
