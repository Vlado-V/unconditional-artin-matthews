module

public import ArtinMatthews.SpectralPeterssonHeckePairingLimit
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Petersson integral is the inner product of the actual
weight-corrected L² vectors on the native Gamma0 region. -/

noncomputable section
open MeasureTheory UpperHalfPlane Filter
open scoped InnerProductSpace ComplexConjugate

namespace ArtinMatthews

def spectralPeterssonHilbertProfile (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  ((z.im^((k : ℝ)/2) : ℝ) : ℂ)*F z

theorem spectralPeterssonHilbertProfile_norm (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖spectralPeterssonHilbertProfile k F z‖ = spectralPeterssonWeightedNorm k F z := by
  unfold spectralPeterssonHilbertProfile spectralPeterssonWeightedNorm
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _),mul_comm]

theorem gamma0PeterssonHilbertProfile_memLp (N : ℕ) [NeZero N] (k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : Continuous F) (M : ℝ) (hM : ∀ z, spectralPeterssonWeightedNorm k F z ≤ M) :
    MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)) := by
  let _ : IsFiniteMeasure (volume.restrict (gamma0InteriorRegion N)) := ⟨by
    simpa using gamma0InteriorRegion_volume_lt_top N⟩
  have h : Continuous (spectralPeterssonHilbertProfile k F) :=
    (Complex.continuous_ofReal.comp (continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero))).mul hF
  exact MemLp.of_bound h.aestronglyMeasurable M (Eventually.of_forall fun z => by
    rw [spectralPeterssonHilbertProfile_norm]; exact hM z)

theorem gamma0PeterssonInner_eq_hilbert (N k : ℕ) (F G : UpperHalfPlane → ℂ)
    (hf : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)))
    (hg : MemLp (spectralPeterssonHilbertProfile k G) 2 (volume.restrict (gamma0InteriorRegion N))) :
    ⟪hf.toLp (spectralPeterssonHilbertProfile k F), hg.toLp (spectralPeterssonHilbertProfile k G)⟫_ℂ =
      gamma0PeterssonInner N k F G := by
  rw [MeasureTheory.L2.inner_def]
  unfold gamma0PeterssonInner
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with z hfz hgz
  rw [hfz,hgz]
  let y := z.im
  let p := y^((k : ℝ)/2)
  have hy : 0 < y := z.im_pos
  have hp : p*p = y^k := by
    dsimp only [p]
    rw [← Real.rpow_add hy,show (k : ℝ)/2+(k : ℝ)/2=k by ring,Real.rpow_natCast]
  have hpC : (p : ℂ)*(p : ℂ) = (y : ℂ)^k := by exact_mod_cast hp
  rw [RCLike.inner_apply]
  change ((p : ℂ)*G z)*conj ((p : ℂ)*F z) = _
  unfold UpperHalfPlane.petersson
  simp only [map_mul,Complex.conj_ofReal,zpow_natCast]
  calc
    _ = conj (F z)*G z*((p : ℂ)*(p : ℂ)) := by ring
    _ = _ := by rw [hpC]

theorem gamma0PeterssonHilbert_diagonal_norm (N k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N))) :
    ‖hF.toLp (spectralPeterssonHilbertProfile k F)‖^2 = (gamma0PeterssonInner N k F F).re := by
  rw [← gamma0PeterssonInner_eq_hilbert N k F F hF hF]
  exact @norm_sq_eq_re_inner ℂ _ _ _ _ _

end ArtinMatthews
