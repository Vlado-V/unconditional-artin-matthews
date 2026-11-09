module

public import ArtinMatthews.SpectralPeterssonPhysicalCauchy


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative norm comparison from exact cutoff reproduction and
its actual physical L2 bound. -/
noncomputable section
open Set Matrix MeasureTheory UpperHalfPlane

namespace ArtinMatthews

private theorem cut_scalar_compare (r q p C S : ℝ) (hr : 0 < r) (hq : 0 ≤ q)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hcs : (r*q)^2 ≤ p*q) (hp : p ≤ 2*C*(r*S)) :
    r*q ≤ 2*C*S := by
  by_cases hzero : q = 0
  · rw [hzero,mul_zero]
    positivity
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    have hsq : r^2*q ≤ p := (mul_le_mul_iff_of_pos_right hqpos).mp (by
      calc
        _ = (r*q)^2 := by ring
        _ ≤ _ := hcs)
    apply (mul_le_mul_iff_of_pos_left hr).mp
    calc
      r*(r*q) = r^2*q := by ring
      _ ≤ p := hsq
      _ ≤ 2*C*(r*S) := hp
      _ = r*(2*C*S) := by ring

theorem gamma0Petersson_density_of_cut (N k : ℕ) (F P : UpperHalfPlane → ℂ)
    (hF : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)))
    (hP : MemLp (spectralPeterssonHilbertProfile k P) 2 (volume.restrict (gamma0InteriorRegion N)))
    (A r C S : ℝ) (hr : 0 < r) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hlo : Real.exp (-A) ≤ r)
    (hpair : gamma0PeterssonInner N k P F = (r : ℂ)*gamma0PeterssonInner N k F F)
    (hp : (∫ z in gamma0InteriorRegion N, ‖P z‖^2*z.im^k) ≤ 2*C*(r*S)) :
    (∫ z in gamma0InteriorRegion N, ‖F z‖^2*z.im^k) ≤ 2*Real.exp A*C*S := by
  let q := ∫ z in gamma0InteriorRegion N, ‖F z‖^2*z.im^k
  let p := ∫ z in gamma0InteriorRegion N, ‖P z‖^2*z.im^k
  have hq : 0 ≤ q := integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (pow_nonneg z.im_pos.le _))
  have hself : gamma0PeterssonInner N k F F = (q : ℂ) := by
    simp only [gamma0PeterssonInner,spectralPetersson_self_pair,integral_complex_ofReal,q]
  have hnorm : ‖gamma0PeterssonInner N k P F‖ = r*q := by
    rw [hpair,hself,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.le,
      Complex.norm_real,Real.norm_of_nonneg hq]
  have hcs := gamma0PeterssonPhysical_cauchy N k P F hP hF
  rw [hnorm] at hcs
  have hmain := cut_scalar_compare r q p C S hr hq hC hS hcs hp
  have hfinal : Real.exp (-A)*q ≤ 2*C*S :=
    (mul_le_mul_of_nonneg_right hlo hq).trans hmain
  have hmul := mul_le_mul_of_nonneg_left hfinal (Real.exp_nonneg A)
  rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at hmul
  change q ≤ _
  nlinarith [hmul]


end ArtinMatthews
