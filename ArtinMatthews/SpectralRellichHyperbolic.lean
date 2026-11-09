module

public import ArtinMatthews.SpectralRellichGreenEnergy
public import ArtinMatthews.SpectralHyperbolicL2


set_option backward.privateInPublic true
@[expose] public section

/-! Actual hyperbolic L2 compactness from the proved local rectangle Rellich theorem. -/
namespace ArtinMatthews

open MeasureTheory Set

theorem spectral_plane_normsq_integrable {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) : Integrable (fun p => ‖F p‖^2) := by
  have hcont : Continuous (fun p => ‖F p‖^2) := hF.norm.pow 2
  have hs : HasCompactSupport (fun p => ‖F p‖^2) :=
    hc.comp_left (g := fun z : ℂ => ‖z‖^2) (by simp)
  exact hcont.integrable_of_hasCompactSupport hs

theorem spectral_rectangle_height_band {F : ℝ × ℝ → ℂ} {A a b : ℝ}
    (hs : tsupport F ⊆ spectralPlaneRectangle A a b) :
    ∀ p, F p ≠ 0 → a ≤ p.2 ∧ p.2 ≤ b := by
  intro p hp
  exact (hs (subset_tsupport _ hp)).2

theorem spectral_rectangle_hyperbolic_memLp {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hs : tsupport F ⊆ spectralPlaneRectangle A a b) :
    MemLp (fun z : UpperHalfPlane => F (z.re,z.im)) 2 volume := by
  have hc : HasCompactSupport (F : ℝ × ℝ → ℂ) :=
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hs
  exact (hyperbolic_L2_band_transfer F.continuous.measurable
    (spectral_plane_normsq_integrable F.continuous hc) ha hab (spectral_rectangle_height_band hs)).1

/-- The actual L2 representative for the invariant hyperbolic volume. -/
noncomputable def spectralHyperbolicRectangleLp {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hs : tsupport F ⊆ spectralPlaneRectangle A a b) :
    Lp ℂ 2 (volume : Measure UpperHalfPlane) :=
  (spectral_rectangle_hyperbolic_memLp ha hab F hs).toLp (fun z : UpperHalfPlane => F (z.re,z.im))

theorem spectralHyperbolicRectangleLp_ae {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hs : tsupport F ⊆ spectralPlaneRectangle A a b) :
    spectralHyperbolicRectangleLp ha hab F hs =ᵐ[volume]
      (fun z : UpperHalfPlane => F (z.re,z.im)) := MemLp.coeFn_toLp _

theorem spectralHyperbolicRectangleLp_dist_square {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (F G : SchwartzMap (ℝ × ℝ) ℂ) (hF : tsupport F ⊆ spectralPlaneRectangle A a b)
    (hG : tsupport G ⊆ spectralPlaneRectangle A a b) :
    dist (spectralHyperbolicRectangleLp ha hab F hF) (spectralHyperbolicRectangleLp ha hab G hG)^2 =
      ∫ z : UpperHalfPlane, ‖F (z.re,z.im)-G (z.re,z.im)‖^2 := by
  rw [dist_eq_norm,← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (spectralHyperbolicRectangleLp ha hab F hF)
      (spectralHyperbolicRectangleLp ha hab G hG),
    spectralHyperbolicRectangleLp_ae ha hab F hF,spectralHyperbolicRectangleLp_ae ha hab G hG]
      with z hs hF hG
  rw [hs,Pi.sub_apply,hF,hG,real_inner_self_eq_norm_sq]

/-- The band estimate is applied to the actual difference F-G, giving the
uniform Lipschitz constant 1/a between the two actual L2 metrics. -/
theorem spectralHyperbolicRectangleLp_dist_le {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (F G : SchwartzMap (ℝ × ℝ) ℂ) (hF : tsupport F ⊆ spectralPlaneRectangle A a b)
    (hG : tsupport G ⊆ spectralPlaneRectangle A a b) :
    let hcF : HasCompactSupport (F : ℝ × ℝ → ℂ) :=
      (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hF
    let hcG : HasCompactSupport (G : ℝ × ℝ → ℂ) :=
      (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hG
    dist (spectralHyperbolicRectangleLp ha hab F hF) (spectralHyperbolicRectangleLp ha hab G hG) ≤
      (1/a)*dist (spectralPlaneLp F F.continuous hcF) (spectralPlaneLp G G.continuous hcG) := by
  dsimp only
  have hs : tsupport (fun p => F p-G p) ⊆ spectralPlaneRectangle A a b :=
    (tsupport_sub _ _).trans (union_subset hF hG)
  have hc : HasCompactSupport (fun p => F p-G p) :=
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hs
  have hh := (hyperbolic_L2_band_transfer (F.continuous.sub G.continuous).measurable
    (spectral_plane_normsq_integrable (F.continuous.sub G.continuous) hc)
    ha hab (spectral_rectangle_height_band hs)).2.2
  simp only [Pi.sub_apply] at hh
  have hcF : HasCompactSupport (F : ℝ × ℝ → ℂ) :=
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hF
  have hcG : HasCompactSupport (G : ℝ × ℝ → ℂ) :=
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hG
  rw [← spectralHyperbolicRectangleLp_dist_square ha hab F G hF hG,
    ← spectralPlaneLp_dist_square F G F.continuous G.continuous hcF hcG] at hh
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg (by positivity : 0 ≤ 1/a) dist_nonneg)).mp
  calc
    _ ≤ _ := hh
    _ = _ := by ring

/-- Actual hyperbolic local Rellich: the invariant-measure L2 representatives
of the fixed-rectangle Dirichlet-energy-bounded family are totally bounded. -/
theorem spectral_rellich_hyperbolic_rectangle {J : Type*} (A a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (F : J → SchwartzMap (ℝ × ℝ) ℂ)
    (hs : ∀ j, tsupport (F j) ⊆ spectralPlaneRectangle A a b) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, (∫ p, ‖F j p‖^2)+∫ p, h2DirichletDensity (F j) (F j) p ≤ B) :
    TotallyBounded (range (fun j => spectralHyperbolicRectangleLp ha hab (F j) (hs j))) := by
  let hc : ∀ j, HasCompactSupport (F j : ℝ × ℝ → ℂ) := fun j =>
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) (hs j)
  have ht : TotallyBounded (range (fun j => spectralPlaneLp (F j) (F j).continuous (hc j))) :=
    (spectral_rellich_rectangle_dirichlet A a b F hs hB henergy).totallyBounded.subset subset_closure
  exact spectral_totallyBounded_range_of_dist_le
    (fun j => spectralHyperbolicRectangleLp ha hab (F j) (hs j))
    (fun j => spectralPlaneLp (F j) (F j).continuous (hc j)) (one_div_pos.mpr ha)
    (fun i j => spectralHyperbolicRectangleLp_dist_le ha hab (F i) (F j) (hs i) (hs j)) ht

theorem spectral_rellich_hyperbolic_rectangle_compact_closure {J : Type*} (A a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (F : J → SchwartzMap (ℝ × ℝ) ℂ)
    (hs : ∀ j, tsupport (F j) ⊆ spectralPlaneRectangle A a b) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, (∫ p, ‖F j p‖^2)+∫ p, h2DirichletDensity (F j) (F j) p ≤ B) :
    IsCompact (closure (range (fun j => spectralHyperbolicRectangleLp ha hab (F j) (hs j)))) := by
  exact (spectral_rellich_hyperbolic_rectangle A a b ha hab F hs hB henergy).closure.isCompact_of_isClosed
    isClosed_closure

end ArtinMatthews
