module

public import ArtinMatthews.SourceFrequencyOrbitSeparation
public import ArtinMatthews.SourcePrimeNormSummability


set_option backward.privateInPublic true
@[expose] public section

/-! The reduced rows inherit exterior ideal norm summability with
exactly a finite S-unit class fiber at each exponent vector. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def sourceFrequencyRepresentativeNorm (u : SourceFrequencyRepresentativeIndex F S₀) : ℕ :=
  sourcePrimeExponentNorm F S₀ u.1.val

theorem sourceFrequencyRepresentativeNorm_pos (u : SourceFrequencyRepresentativeIndex F S₀) :
    0 < sourceFrequencyRepresentativeNorm F S₀ u :=
  sourcePrimeExponentNorm_pos F S₀ u.1.val

theorem sourceFrequencyRepresentativeNorm_eq_element {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (u : SourceFrequencyRepresentativeIndex F S₀) :
    sourcePrimeExponentNorm F S₀
        (sourceElementExponents F S₀ (sourceFrequencyRepresentative F hζ S₀ u).val
          (sourceFrequencyRepresentative F hζ S₀ u).property) =
      sourceFrequencyRepresentativeNorm F S₀ u := by
  rw [sourceFrequencyRepresentative_exponents]
  rfl

theorem sourceFrequencyRepresentativeNorm_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun u : SourceFrequencyRepresentativeIndex F S₀ =>
      (sourceFrequencyRepresentativeNorm F S₀ u : ℝ) ^ (-σ)) := by
  let Q := ExteriorUnitSixthClasses (sourceHilbertSet F S₀)
  let : Fintype Q := Fintype.ofFinite _
  let f (e : SourceReducedFrequencyExponents F S₀) := (sourcePrimeExponentNorm F S₀ e.val : ℝ) ^ (-σ)
  have hf : Summable f := (sourcePrimeExponentNorm_summable F S₀ hσ).subtype (fun e => ∀ P, e P < 6)
  change Summable (fun u : SourceReducedFrequencyExponents F S₀ × Q => f u.1)
  refine (summable_prod_of_nonneg (fun u => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
    ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
  simp only [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  exact hf.mul_left _

theorem sourceFrequencyRepresentativeNorm_summable_neg_two :
    Summable (fun u : SourceFrequencyRepresentativeIndex F S₀ =>
      (sourceFrequencyRepresentativeNorm F S₀ u : ℝ) ^ (-(2 : ℝ))) :=
  sourceFrequencyRepresentativeNorm_summable F S₀ (by norm_num)

abbrev SourceBoundedFrequencyRows (N : ℕ) :=
  {u : SourceFrequencyRepresentativeIndex F S₀ // sourceFrequencyRepresentativeNorm F S₀ u ≤ N}

theorem sourceBoundedFrequencyRows_finite (N : ℕ) : Finite (SourceBoundedFrequencyRows F S₀ N) := by
  let B := {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ N}
  let : Fintype B := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N).fintype
  let Q := ExteriorUnitSixthClasses (sourceHilbertSet F S₀)
  let j : SourceBoundedFrequencyRows F S₀ N → B × Q := fun u =>
    (⟨sourcePrimeExponentIdeal F S₀ u.val.1.val, by
      rw [sourcePrimeExponentIdeal_norm]
      exact u.property⟩, u.val.2)
  apply Finite.of_injective j
  intro u v huv
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact sourcePrimeExponentIdeal_injective F S₀ (congrArg (fun b : B × Q => b.1.val) huv)
  · exact congrArg (fun b : B × Q => b.2) huv

end
end ArtinMatthews
