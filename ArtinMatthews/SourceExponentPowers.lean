module

public import ArtinMatthews.SourcePrimeExponentProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Literal powers of the fixed allowed prime-generator products. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourcePrimeExponentNorm_nsmul (e : SourcePrimeExponents F S₀) (k : ℕ) :
    sourcePrimeExponentNorm F S₀ (k • e) = sourcePrimeExponentNorm F S₀ e ^ k := by
  induction k with
  | zero => rw [zero_nsmul, sourcePrimeExponentNorm_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, sourcePrimeExponentNorm_add, ih, pow_succ]

theorem sourcePrimeExponentIdeal_nsmul (e : SourcePrimeExponents F S₀) (k : ℕ) :
    sourcePrimeExponentIdeal F S₀ (k • e) = sourcePrimeExponentIdeal F S₀ e ^ k := by
  induction k with
  | zero => rw [zero_nsmul, sourcePrimeExponentIdeal_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, sourcePrimeExponentIdeal_add, ih, pow_succ]

theorem sourcePrimeExponentGenerator_nsmul {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (e : SourcePrimeExponents F S₀) (k : ℕ) :
    sourcePrimeExponentGenerator F hζ S₀ (k • e) = sourcePrimeExponentGenerator F hζ S₀ e ^ k := by
  induction k with
  | zero => rw [zero_nsmul, sourcePrimeExponentGenerator_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, sourcePrimeExponentGenerator_add, ih, pow_succ]

theorem sourcePrimeExponentNorm_squarefree_cube (c n : SourcePrimeExponents F S₀) :
    sourcePrimeExponentNorm F S₀ (c + 3 • n) =
      sourcePrimeExponentNorm F S₀ c * sourcePrimeExponentNorm F S₀ n ^ 3 := by
  rw [sourcePrimeExponentNorm_add, sourcePrimeExponentNorm_nsmul]

end
end ArtinMatthews
