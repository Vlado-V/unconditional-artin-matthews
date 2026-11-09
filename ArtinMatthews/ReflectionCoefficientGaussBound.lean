module

public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceExponentFiniteFNorm
public import ArtinMatthews.SourcePrimeNormSummability


set_option backward.privateInPublic true
@[expose] public section

/-! A direct bound for the literal global Gauss sum. This uses the
actual quotient cardinality and actual standard phase, and needs no
primitive-character or CRT-factorization hypothesis. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SIntegerQuotient StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem reflectionSourceQuotientPhase_norm (e : SourcePrimeExponents F S₀)
    (x : (sourceRing F S₀) ⧸ Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e}) :
    ‖sIntegerQuotientPhase F (sourceHilbertSet F S₀)
      (sourcePrimeExponentGenerator F hζ S₀ e)
      (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e) x‖ = 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sIntegerQuotientPhase_mk]
  exact sourceStandardCharacter_norm F _ _

theorem reflectionGammaTwo_norm_le_sqrt (e : SourcePrimeExponents F S₀) :
    ‖reflectionGammaTwo F hζ S₀ e‖ ≤ Real.sqrt (sourcePrimeExponentNorm F S₀ e : ℝ) := by
  let A := sourcePrimeExponentGenerator F hζ S₀ e
  let hA := sourcePrimeExponentGenerator_ne_zero F hζ S₀ e
  let R := (sourceRing F S₀) ⧸ Ideal.span {A}
  let : Finite R := sourcePrimeExponentGenerator_quotient_finite F hζ S₀ e
  let := Fintype.ofFinite R
  have hq : 0 < (sourcePrimeExponentNorm F S₀ e : ℝ) :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ e)
  have hs : 0 < Real.sqrt (sourcePrimeExponentNorm F S₀ e : ℝ) := Real.sqrt_pos.mpr hq
  have ht (x : R) :
      ‖(reflectionExponentResidueValue F hζ S₀ e (Quotient.out x)) ^ 2 *
        sIntegerQuotientPhase F (sourceHilbertSet F S₀) A hA x‖ ≤ 1 := by
    rw [norm_mul, norm_pow, reflectionSourceQuotientPhase_norm, mul_one]
    exact pow_le_one₀ (norm_nonneg _) (reflectionExponentResidueValue_norm_le_one F hζ S₀ e _)
  have hsum :
      ‖∑' x : R, (reflectionExponentResidueValue F hζ S₀ e (Quotient.out x)) ^ 2 *
        sIntegerQuotientPhase F (sourceHilbertSet F S₀) A hA x‖ ≤
        (sourcePrimeExponentNorm F S₀ e : ℝ) := by
    rw [tsum_fintype]
    calc
      _ ≤ ∑ x : R, ‖(reflectionExponentResidueValue F hζ S₀ e (Quotient.out x)) ^ 2 *
          sIntegerQuotientPhase F (sourceHilbertSet F S₀) A hA x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : R, (1 : ℝ) := Finset.sum_le_sum (fun x _ => ht x)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        rw [← Nat.card_eq_fintype_card]
        exact congrArg Nat.cast (sourcePrimeExponentGenerator_quotient_card F hζ S₀ e)
  change ‖(∑' x : R, _) / (Real.sqrt (sourcePrimeExponentNorm F S₀ e : ℝ) : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ hs).mpr
  exact hsum.trans_eq (Real.mul_self_sqrt hq.le).symm

end
end ArtinMatthews.VaryingKummerAnalytic
