module

public import ArtinMatthews.SpectralWeylDimensionlessKernel
public import ArtinMatthews.SpectralWeylTwoHeightKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The dimensionless kernel is identified with the actual two-height
orbital density. This is a pointwise change of variables, not a new
definition of the geometric side. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem weylTwoHeightDensity_dimensionless (N : ℕ) [NeZero N] (m n : ℤ)
    (ρ η : ℝ → ℝ) {C y v : ℝ} (hC : 0 < C) (hy : 0 < y)
    (hv : v ∈ Ioo 0 (1/(C^2*y))) :
    weylTwoHeightDensity N m n ρ η C y v =
      (((ρ y*Real.sqrt y/y)*(η v*Real.sqrt v/v)/(C^2*y*v))*
        spectralWeylDimensionlessKernel
          (cuspFourierFrequency (N : ℝ) m) (cuspFourierFrequency (N : ℝ) n) (2/C) y v : ℝ) := by
  have hv0 : 0 < v := hv.1
  have hCv : 0 < C^2*y := mul_pos (sq_pos_of_pos hC) hy
  have hsmall : C^2*y*v < 1 := by
    have hh := (lt_div_iff₀ hCv).mp hv.2
    nlinarith
  have hrad : 0 < 1/(C^2*y*v)-1 := by
    have hp : 0 < C^2*y*v := by positivity
    have hh : (1 : ℝ) < 1/(C^2*y*v) := (lt_div_iff₀ hp).mpr (by simpa only [one_mul] using hsmall)
    linarith
  let S : ℝ := Real.sqrt (1/(C^2*y*v)-1)
  have hS : 0 < S := Real.sqrt_pos.mpr hrad
  have hr : weylHeightRoot C y v = y*S := by
    unfold weylHeightRoot S
    rw [show y/(C^2*v)-y^2 = y^2*(1/(C^2*y*v)-1) by field_simp,
      Real.sqrt_mul (sq_nonneg y),Real.sqrt_sq hy.le]
  have hsmall' : y*v < (1/C)^2 := by
    rw [div_pow,one_pow]
    apply (lt_div_iff₀ (sq_pos_of_pos hC)).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hsmall
  have hX : 2*Real.sqrt (y*v) < 2/C := by
    have hh := (Real.sqrt_lt' (one_div_pos.mpr hC)).mpr hsmall'
    calc
      _ < 2*(1/C) := mul_lt_mul_of_pos_left hh two_pos
      _ = _ := by ring
  have harg : Real.sqrt ((2/C)^2/(4*y*v)-1) = S := by
    congr 1
    field_simp
    ring
  have hden : Real.sqrt ((2/C)^2/4-y*v) = (Real.sqrt y*Real.sqrt v)*S := by
    rw [show (2/C)^2/4-y*v = (y*v)*(1/(C^2*y*v)-1) by field_simp; ring,
      Real.sqrt_mul (mul_pos hy hv0).le,Real.sqrt_mul hy.le]
  have hphase : 2*Real.pi*((m : ℝ)+(n : ℝ)*v/y)*weylHeightRoot C y v/(N : ℝ) =
      (cuspFourierFrequency (N : ℝ) m*y+cuspFourierFrequency (N : ℝ) n*v)*S := by
    rw [hr]
    unfold cuspFourierFrequency
    field_simp
  unfold weylTwoHeightDensity
  rw [spectralWeylDimensionlessKernel_eq hy hv0 hX,harg,hden,← hphase,hr]
  congr 1
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsy : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hsv : Real.sqrt v ≠ 0 := (Real.sqrt_pos.mpr hv0).ne'
  field_simp [hC.ne',hy.ne',hv0.ne',hS.ne',hsy,hsv,hN]

end ArtinMatthews
