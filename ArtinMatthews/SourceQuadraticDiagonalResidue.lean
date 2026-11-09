module

public import ArtinMatthews.SourceQuadraticPrincipalResiduePositive
public import ArtinMatthews.SourceQuadraticDiagonalBlock


set_option backward.privateInPublic true
@[expose] public section

/-! The actual diagonal Full residue is nonnegative and may be removed
from the upper real-part bound in the signed B3 decomposition. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticFullResidueDiagonal_nonnegative {M : ℝ} (hM : 0 < M)
    (K : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) :
    0 ≤ (sourceQuadraticZeroResidualBlock F S₀
      (sourceQuadraticDualDivisorResidue F S₀ hζ M K g) cols u g).re ∧
      (sourceQuadraticZeroResidualBlock F S₀
        (sourceQuadraticDualDivisorResidue F S₀ hζ M K g) cols u g).im = 0 := by
  rw [sourceQuadraticZeroResidualBlock_eq]
  by_cases hg : g ∈ cols
  · rw [ite_eq_left hg]
    have hu : star (u g) * u g = ((‖u g‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      rfl
    rw [hu]
    obtain ⟨hr, hi⟩ := sourceQuadraticDualDivisorResidue_zero_nonnegative F S₀ hζ hM K g
    constructor
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (sq_nonneg _) hr
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hi, mul_zero, zero_mul, add_zero]
  · rw [ite_eq_right hg]
    exact ⟨le_rfl, rfl⟩

theorem sourceQuadratic_sub_fullResidueDiagonal_re_le {M : ℝ} (hM : 0 < M)
    (K : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) (z : ℂ) :
    (z - sourceQuadraticZeroResidualBlock F S₀
      (sourceQuadraticDualDivisorResidue F S₀ hζ M K g) cols u g).re ≤ z.re := by
  rw [Complex.sub_re]
  exact sub_le_self _ (sourceQuadraticFullResidueDiagonal_nonnegative F S₀ hζ hM K cols u g).1

end
end ArtinMatthews.SourceEulerAssembly
