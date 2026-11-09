module

public import ArtinMatthews.SpectralBesselI


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of the actual confluent hypergeometric gamma
series.  This is used as a Tonelli majorant, not as a transform definition. -/

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

theorem spectralKummer_gamma_summable (a b z : ℂ) (ha : 0 < a.re) :
    Summable (fun n : ℕ => Complex.Gamma (a+n)*z^n/
      ((n.factorial : ℂ)*Complex.Gamma (b+n))) := by
  have hg := (Complex.regularizedHGFunSeries {a} {b}).summable (x := z) (by
    rw [Complex.radius_regularizedHGFunSeries_eq_top (by simp)]
    exact ENNReal.coe_lt_top)
  have hG : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  have hnon (k : ℕ) : a ≠ -(k : ℂ) := by
    intro h
    have hbad : a.re ≤ 0 := by rw [h]; simp
    exact (not_le.mpr ha) hbad
  apply (hg.mul_left (Complex.Gamma a)).congr
  intro n
  simp only [Complex.regularizedHGFunSeries,FormalMultilinearSeries.ofScalars_apply_eq,
    Complex.regularizedHGFunCoeff,Multiset.map_singleton,Multiset.prod_singleton,smul_eq_mul]
  rw [← Complex.Gamma_add_nat_div_Gamma_eq a hnon]
  field_simp

end ArtinMatthews
