module

public import ArtinMatthews.SpectralCuspEisensteinFourierPositive
public import ArtinMatthews.SpectralCuspEisensteinFourierSigns


set_option backward.privateInPublic true
@[expose] public section

/-! The actual nonzero Fourier coefficient of the convergent all-cusp
Eisenstein series, with the genuine true-width Kloosterman Dirichlet
series and the evaluated K-Bessel kernel. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspEisenstein_nonzero_fourier_bessel (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (hn : n ≠ 0)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)*
        spectralRealFourierPhase (n : ℝ) x) =
      ((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
        ((Real.pi*|(n : ℝ)| : ℝ) : ℂ)^(s-1/2) *
          cuspBesselKernel (s-1/2) (2*Real.pi*|(n : ℝ)|) y *
            gamma0CuspFourierDirichlet N r a n s := by
  rw [gamma0CuspEisenstein_nonzero_fourier_positive_rows N r a s hs n hn y hy,
    cuspEisensteinPositiveFourier_dirichlet N r a s hs n y hy,
    eisensteinHorizontalFourier_bessel s (by linarith) (n : ℝ) y (by exact_mod_cast hn) hy,
    gamma0CuspFourierDirichlet_normalized]
  ring

end ArtinMatthews

