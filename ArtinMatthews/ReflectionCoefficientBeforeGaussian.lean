module

public import ArtinMatthews.ReflectionCoefficientConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! The exact coefficient of the positive sheet, with its full directed
Gauss and angular factors. The Dedekind majorant applies before any
Gaussian smoothing. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : QuadraticWeil.standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

def reflectionCoefficientBeforeGaussian (c : ReflectionSquarefreeExponents F S₀)
    (n : SourcePrimeExponents F S₀) (m : sourceRing F S₀) : ℂ :=
  let A := c.val + 3 • n
  reflectionGammaTwo F hζ S₀ c.val /
      ((Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) : ℂ) *
        (sourcePrimeExponentNorm F S₀ n : ℂ)) *
    reflectionThetaValue F hζ S₀ hS η A * reflectionExponentResidueValue F hζ S₀ A m

theorem reflectionCoefficientTerm_eq_beforeGaussian_mul
    (c : ReflectionSquarefreeExponents F S₀) (n : SourcePrimeExponents F S₀)
    (m : sourceRing F S₀) (Z : ℝ) :
    reflectionCoefficientTerm F hζ S₀ hS η c n m Z =
      reflectionCoefficientBeforeGaussian F hζ S₀ hS η c n m *
        (reflectionGaussian ((sourcePrimeExponentNorm F S₀ (c.val + 3 • n) : ℝ) / Z) : ℂ) := rfl

theorem reflectionCoefficientBeforeGaussian_norm_le_one
    (c : ReflectionSquarefreeExponents F S₀) (n : SourcePrimeExponents F S₀)
    (m : sourceRing F S₀) :
    ‖reflectionCoefficientBeforeGaussian F hζ S₀ hS η c n m‖ ≤ 1 := by
  have hg := reflectionGaussian_pos ((sourcePrimeExponentNorm F S₀ (c.val + 3 • n) : ℝ) / 1)
  have h := reflectionCoefficientTerm_norm_le_gaussian F hζ S₀ hS η c n m 1
  rw [reflectionCoefficientTerm_eq_beforeGaussian_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hg.le] at h
  exact le_of_mul_le_mul_right (h.trans_eq (one_mul _).symm) hg

theorem reflectionCoefficientBeforeGaussian_dirichlet_summable
    (m : sourceRing F S₀) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : ReflectionSquarefreeExponents F S₀ × SourcePrimeExponents F S₀ =>
      ‖reflectionCoefficientBeforeGaussian F hζ S₀ hS η p.1 p.2 m‖ *
        (sourcePrimeExponentNorm F S₀ (p.1.val + 3 • p.2) : ℝ) ^ (-σ)) := by
  have hN := sourcePrimeExponentNorm_summable F S₀ hσ
  have hC : Summable (fun c : ReflectionSquarefreeExponents F S₀ =>
      (sourcePrimeExponentNorm F S₀ c.val : ℝ) ^ (-σ)) :=
    hN.subtype (fun c => ∀ P, c P ≤ 1)
  have hsum : Summable (fun p : ReflectionSquarefreeExponents F S₀ × SourcePrimeExponents F S₀ =>
      (sourcePrimeExponentNorm F S₀ p.1.val : ℝ) ^ (-σ) *
        (sourcePrimeExponentNorm F S₀ p.2 : ℝ) ^ (-σ)) :=
    summable_mul_of_summable_norm hC.norm hN.norm
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hsum
  intro p
  have hc : 0 < (sourcePrimeExponentNorm F S₀ p.1.val : ℝ) :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ _)
  have hn : 0 < (sourcePrimeExponentNorm F S₀ p.2 : ℝ) :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ _)
  have hA := Real.rpow_le_rpow_of_nonpos (mul_pos hc hn)
    (reflectionExponentNorm_cube_ge_product F S₀ p.1.val p.2) (show -σ ≤ 0 by linarith)
  rw [Real.mul_rpow hc.le hn.le] at hA
  exact (mul_le_of_le_one_left (by positivity)
    (reflectionCoefficientBeforeGaussian_norm_le_one F hζ S₀ hS η p.1 p.2 m)).trans hA

end
end ArtinMatthews.VaryingKummerAnalytic
