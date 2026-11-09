module

public import ArtinMatthews.SpectralBesselLegendreTermwise
public import ArtinMatthews.SpectralJIntegerSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Exact shifted Legendre coefficients of the actual order-zero
Bessel kernel. -/
namespace ArtinMatthews
open Complex MeasureTheory Set Polynomial
open scoped Polynomial Interval

noncomputable section

private theorem spectralLegendreBesselTerm_interval_low (n m : ℕ) (x : ℝ) (hm : m < n) :
    (∫ u in (0 : ℝ)..1, spectralLegendreBesselTerm n x m u) = 0 := by
  rw [spectralLegendreBesselTerm_interval, Nat.descFactorial_of_lt hm]
  simp

private theorem spectralLegendreBesselTerm_interval_shift (n : ℕ) (x : ℝ) (m : ℕ) :
    (∫ u in (0 : ℝ)..1, spectralLegendreBesselTerm n x (m+n) u) =
      ((x : ℂ)/2)^(2*n) * (-(((x : ℂ)/2)^2))^m /
        ((m.factorial : ℂ) * ((m+(2*n+1)).factorial : ℂ)) := by
  let z : ℂ := (x : ℂ)/2
  let d : ℂ := ((m+(2*n+1)).factorial : ℂ)
  have hmd : m.factorial * (m+n).descFactorial n = (m+n).factorial := by
    have h := Nat.factorial_mul_descFactorial (n := m+n) (k := n) (by omega)
    rwa [Nat.add_sub_cancel] at h
  have hmc : (m.factorial : ℂ) * ((m+n).descFactorial n : ℂ) = ((m+n).factorial : ℂ) := by
    exact_mod_cast hmd
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hf : ((m+n).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m+n)
  have hd : d ≠ 0 := by
    change ((m+(2*n+1)).factorial : ℂ) ≠ 0
    exact_mod_cast Nat.factorial_ne_zero (m+(2*n+1))
  have hr : ((m+n).descFactorial n : ℂ) / ((m+n).factorial : ℂ) = (m.factorial : ℂ)⁻¹ := by
    apply (div_eq_iff hf).2
    rw [← hmc, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]
  have hphase : (-z^2)^n * (-1 : ℂ)^n = z^(2*n) := by
    rw [← mul_pow, show -z^2 * (-1 : ℂ) = z^2 by ring, pow_mul]
  rw [spectralLegendreBesselTerm_interval]
  push_cast
  rw [show m+n+n+1 = m+(2*n+1) by omega]
  change ((-z^2)^(m+n) / ((m+n).factorial : ℂ)^2) *
      ((-1 : ℂ)^n * (((m+n).descFactorial n : ℂ) * ((m+n).factorial : ℂ)) / d) =
    z^(2*n) * (-z^2)^m / ((m.factorial : ℂ)*d)
  calc
    _ = (-z^2)^m * ((-z^2)^n * (-1 : ℂ)^n) *
        (((m+n).descFactorial n : ℂ) / ((m+n).factorial : ℂ)) / d := by
      rw [pow_add]
      field_simp <;> ring
    _ = _ := by
      rw [hphase,hr]
      field_simp <;> ring

theorem spectral_shiftedLegendre_besselJ_zero (n : ℕ) (x : ℝ) (hx : 0 < x) :
    (∫ u in (0 : ℝ)..1, (spectralLegendreValue n u : ℂ) *
      Complex.besselJ 0 ((x : ℂ) * (Real.sqrt u : ℂ))) =
      2 * Complex.besselJ ((2*n+1 : ℕ) : ℂ) (x : ℂ) / (x : ℂ) := by
  let F := fun m : ℕ => ∫ u in (0 : ℝ)..1, spectralLegendreBesselTerm n x m u
  have hs := spectralLegendreBesselTerm_interval_hasSum n x hx.le
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hscale : (2/(x : ℂ)) * ((x : ℂ)/2)^(2*n+1) = ((x : ℂ)/2)^(2*n) := by
    rw [pow_succ]
    field_simp <;> ring
  have ht : HasSum (fun m => F (m+n))
      (2 * Complex.besselJ ((2*n+1 : ℕ) : ℂ) (x : ℂ) / (x : ℂ)) := by
    have hj := (spectral_besselJ_nat_hasSum (2*n+1) (x : ℂ)).mul_left (2/(x : ℂ))
    convert hj using 1
    · funext m
      change (∫ u in (0 : ℝ)..1, spectralLegendreBesselTerm n x (m+n) u) = _
      rw [spectralLegendreBesselTerm_interval_shift]
      rw [← hscale]
      ring
    · ring
  calc
    _ = ∑' m, F m := hs.tsum_eq.symm
    _ = (∑ m ∈ Finset.range n, F m) + ∑' m, F (m+n) :=
      (hs.summable.sum_add_tsum_nat_add n).symm
    _ = ∑' m, F (m+n) := by
      rw [Finset.sum_eq_zero (fun m hm =>
        spectralLegendreBesselTerm_interval_low n m x (Finset.mem_range.mp hm)), zero_add]
    _ = _ := ht.tsum_eq

end
end ArtinMatthews
