module

public import ArtinMatthews.SpectralHyperbolicCoordinates
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.MeasureTheory.Group.Prod


set_option backward.privateInPublic true
@[expose] public section

/-!
The actual H² Laplacian `-y²(∂x²+∂y²)` and its local Dirichlet identity.
The integration by parts is reused from Mathlib's Schwartz-space theorem.
The first test has support above the boundary; all Euclidean pairings are
integrable because they are pairings of actual Schwartz functions.
-/

noncomputable section
open MeasureTheory Set
open scoped SchwartzMap LineDeriv

namespace ArtinMatthews

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  change (volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure
  infer_instance

def h2PositiveLaplacian (g : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) : ℂ :=
  (-(p.2 ^ 2)) •
    ((∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} g)) p + (∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} g)) p)

def h2DirichletDensity (f g : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) : ℝ :=
  inner ℝ ((∂_{((1, 0) : ℝ × ℝ)} f) p) ((∂_{((1, 0) : ℝ × ℝ)} g) p) +
    inner ℝ ((∂_{((0, 1) : ℝ × ℝ)} f) p) ((∂_{((0, 1) : ℝ × ℝ)} g) p)

private theorem schwartz_inner_integrable (f g : SchwartzMap (ℝ × ℝ) ℂ) :
    Integrable (fun p => inner ℝ (f p) (g p)) :=
  (SchwartzMap.pairing (innerSL ℝ) f g).integrable

theorem h2DirichletDensity_integrable (f g : SchwartzMap (ℝ × ℝ) ℂ) :
    Integrable (h2DirichletDensity f g) :=
  (schwartz_inner_integrable _ _).add (schwartz_inner_integrable _ _)

private theorem h2_flat_green (f g : SchwartzMap (ℝ × ℝ) ℂ) :
    (∫ p : ℝ × ℝ, -inner ℝ (f p)
      ((∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} g)) p + (∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} g)) p)) =
      ∫ p, h2DirichletDensity f g p := by
  have hx := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
    f (∂_{((1, 0) : ℝ × ℝ)} g) (innerSL ℝ) ((1, 0) : ℝ × ℝ) (μ := volume)
  have hy := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
    f (∂_{((0, 1) : ℝ × ℝ)} g) (innerSL ℝ) ((0, 1) : ℝ × ℝ) (μ := volume)
  change (∫ p, inner ℝ (f p) ((∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} g)) p)) =
    -∫ p, inner ℝ ((∂_{((1, 0) : ℝ × ℝ)} f) p) ((∂_{((1, 0) : ℝ × ℝ)} g) p) at hx
  change (∫ p, inner ℝ (f p) ((∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} g)) p)) =
    -∫ p, inner ℝ ((∂_{((0, 1) : ℝ × ℝ)} f) p) ((∂_{((0, 1) : ℝ × ℝ)} g) p) at hy
  simp only [inner_add_right, h2DirichletDensity]
  rw [integral_neg,
    integral_add (schwartz_inner_integrable f _) (schwartz_inner_integrable f _),
    integral_add (schwartz_inner_integrable _ _) (schwartz_inner_integrable _ _), hx, hy]
  ring

/-- Local Green identity for the actual positive hyperbolic Laplacian and
Mathlib's invariant measure.  This is a real sesquilinear energy identity for
complex-valued test fields. -/
theorem h2_positive_laplacian_green (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (hf : tsupport f ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane,
      inner ℝ (f (z.re, z.im)) (h2PositiveLaplacian g (z.re, z.im))) =
      ∫ p, h2DirichletDensity f g p := by
  rw [upperHalfPlane_integral_coordinates
    (fun p => inner ℝ (f p) (h2PositiveLaplacian g p))]
  calc
    _ = ∫ p in {p : ℝ × ℝ | 0 < p.2}, -inner ℝ (f p)
        ((∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} g)) p +
          (∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} g)) p) := by
      apply setIntegral_congr_fun (by measurability)
      intro p hp
      change 0 < p.2 at hp
      simp only [h2PositiveLaplacian, real_inner_smul_right]
      field_simp [ne_of_gt hp]
    _ = ∫ p : ℝ × ℝ, -inner ℝ (f p)
        ((∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} g)) p +
          (∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} g)) p) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : f p = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hp (hf ht))
      simp only [hz, inner_zero_left, neg_zero]
    _ = _ := h2_flat_green f g

/-- In particular the local positive Laplacian has nonnegative quadratic
form, equal to the sum of the two actual derivative-square integrals. -/
theorem h2_positive_laplacian_energy (f : SchwartzMap (ℝ × ℝ) ℂ)
    (hf : tsupport f ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane,
      inner ℝ (f (z.re, z.im)) (h2PositiveLaplacian f (z.re, z.im))) =
      ∫ p : ℝ × ℝ, ‖(∂_{((1, 0) : ℝ × ℝ)} f) p‖ ^ 2 + ‖(∂_{((0, 1) : ℝ × ℝ)} f) p‖ ^ 2 := by
  rw [h2_positive_laplacian_green f f hf]
  simp only [h2DirichletDensity, real_inner_self_eq_norm_sq]

theorem h2_positive_laplacian_nonneg (f : SchwartzMap (ℝ × ℝ) ℂ)
    (hf : tsupport f ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    0 ≤ ∫ z : UpperHalfPlane,
      inner ℝ (f (z.re, z.im)) (h2PositiveLaplacian f (z.re, z.im)) := by
  rw [h2_positive_laplacian_energy f hf]
  exact integral_nonneg (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Symmetry on genuine local test fields, for the real Hilbert structure of
the complex-valued space. -/
theorem h2_positive_laplacian_symmetric (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (hf : tsupport f ⊆ {p : ℝ × ℝ | 0 < p.2})
    (hg : tsupport g ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane,
      inner ℝ (f (z.re, z.im)) (h2PositiveLaplacian g (z.re, z.im))) =
    ∫ z : UpperHalfPlane,
      inner ℝ (h2PositiveLaplacian f (z.re, z.im)) (g (z.re, z.im)) := by
  calc
    _ = ∫ p, h2DirichletDensity f g p := h2_positive_laplacian_green f g hf
    _ = ∫ p, h2DirichletDensity g f p := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [h2DirichletDensity, real_inner_comm]
    _ = ∫ z : UpperHalfPlane,
        inner ℝ (g (z.re, z.im)) (h2PositiveLaplacian f (z.re, z.im)) :=
      (h2_positive_laplacian_green g f hg).symm
    _ = _ := by simp only [real_inner_comm]

end ArtinMatthews
