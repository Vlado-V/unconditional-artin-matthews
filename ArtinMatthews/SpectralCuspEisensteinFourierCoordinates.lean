module

public import ArtinMatthews.SpectralCuspEisensteinFourierIntegrals
public import ArtinMatthews.SpectralCuspEisensteinRowKernel
public import ArtinMatthews.SpectralCuspEisensteinDoubleCosets
public import ArtinMatthews.SpectralTrueWidthKloosterman


set_option backward.privateInPublic true
@[expose] public section

/-! Exact positive-row Fourier orbits and their true-width residue phases.
The target mode is the first argument of the native Kloosterman sum. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

def cuspEisensteinCoordinateFourierIntegral (N : ℕ) [NeZero N] (r a : SL(2, ℤ))
    (s : ℂ) (n : ℤ) (y : ℝ) (hy : 0 < y) (c : {c : ℕ // 0 < c})
    (d : CuspEisensteinRowFibre N r a c.val) : ℂ :=
  cuspEisensteinRowFourierIntegral N r a s n y hy
    (cuspEisensteinPositiveCoordinateRow N r a ⟨c,d⟩).val

theorem cuspEisensteinCoordinateFourierIntegral_eq (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (n : ℤ) (y : ℝ) (hy : 0 < y)
    (c : {c : ℕ // 0 < c}) (d : CuspEisensteinRowFibre N r a c.val) :
    cuspEisensteinCoordinateFourierIntegral N r a s n y hy c d =
      (gamma0CuspTrueWidth N r : ℂ)^s*∫ x in (0 : ℝ)..1,
        eisensteinRealRowTerm s ((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ)) d.val x y*
          spectralRealFourierPhase (n : ℝ) x := by
  unfold cuspEisensteinCoordinateFourierIntegral cuspEisensteinRowFourierIntegral
  simp_rw [cuspEisensteinCoordinateTerm_eq]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem cuspEisensteinCoordinateFourierIntegral_orbit (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ)
    (y : ℝ) (hy : 0 < y) (c : {c : ℕ // 0 < c})
    (d : CuspEisensteinRowResidues N r a c.val) :
    (∑' k : ℤ,cuspEisensteinCoordinateFourierIntegral N r a s n y hy c
      (cuspEisensteinResidueTranslate N r a c.val (d,k))) =
      (gamma0CuspTrueWidth N r : ℂ)^(-s)*(c.val : ℂ)^(-2*s)*
        spectralRealFourierPhase (n : ℝ)
          (-(d.val.val : ℝ)/((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ)))*
        eisensteinHorizontalFourier s (n : ℝ) y := by
  have hc : 0 < (c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ) := mul_pos
    (Nat.cast_pos.mpr c.property) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
  simp only [cuspEisensteinCoordinateFourierIntegral_eq,cuspEisensteinResidueTranslate,
    Int.cast_add,Int.cast_mul,Int.cast_natCast]
  rw [tsum_mul_left]
  have he : (fun k : ℤ => ∫ x in (0 : ℝ)..1,
      eisensteinRealRowTerm s ((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ))
        ((d.val.val : ℝ)+(gamma0CuspTrueWidth N r : ℝ)*c.val*k) x y*
          spectralRealFourierPhase (n : ℝ) x) =
      fun k : ℤ => ∫ x in (0 : ℝ)..1,
        eisensteinRealRowTerm s ((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ))
          ((d.val.val : ℝ)+((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ))*k) x y*
            spectralRealFourierPhase (n : ℝ) x := by
    funext k
    congr 1
    funext x
    congr 2
    ring
  rw [he,eisensteinRealRowTerm_phased_orbit s (by linarith) _ _ y hc hy n]
  have hp : (gamma0CuspTrueWidth N r : ℂ)^s *
      (((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ) : ℝ) : ℂ)^(-2*s) =
      (gamma0CuspTrueWidth N r : ℂ)^(-s)*(c.val : ℂ)^(-2*s) := by
    simpa only [Complex.ofReal_natCast] using
      cuspEisenstein_width_power s (gamma0CuspTrueWidth N r : ℝ) (c.val : ℝ)
        (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) (Nat.cast_pos.mpr c.property)
  calc
    _ = ((gamma0CuspTrueWidth N r : ℂ)^s *
        (((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ) : ℝ) : ℂ)^(-2*s)) *
        spectralRealFourierPhase (n : ℝ)
          (-(d.val.val : ℝ)/((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ)))*
        eisensteinHorizontalFourier s (n : ℝ) y := by ring
    _ = _ := by rw [hp]

theorem spectralRealFourierPhase_neg_div (b d c : ℝ) :
    spectralRealFourierPhase b (-d/c) = atkinPhase (b*d/c) := by
  unfold spectralRealFourierPhase atkinPhase
  congr 1
  push_cast
  ring

theorem cuspEisensteinResidueFourierSum_eq_kloosterman (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (c : ℕ) [NeZero c] (n : ℤ) :
    (∑ d : CuspEisensteinRowResidues N r a c,
      spectralRealFourierPhase (n : ℝ)
        (-(d.val.val : ℝ)/((c : ℝ)*(gamma0CuspTrueWidth N r : ℝ)))) =
      gamma0TrueWidthKloostermanSum N r a c n 0 := by
  let e := cuspEisensteinReducedMatrixRowEquiv N r a c
  symm
  unfold gamma0TrueWidthKloostermanSum
  apply Fintype.sum_equiv e
  intro M
  have hd : ((e M).val.val : ℝ) = (M.val 1 1 : ℝ) := by
    exact_mod_cast cuspEisensteinReducedMatrixRow_int N r a c M
  rw [hd,spectralRealFourierPhase_neg_div]
  unfold cuspTrueWidthGeometricPhase
  simp only [Int.cast_zero,zero_mul,zero_div,add_zero]
  congr 1
  push_cast
  ring

end ArtinMatthews

