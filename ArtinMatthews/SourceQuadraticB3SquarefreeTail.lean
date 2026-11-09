module

public import ArtinMatthews.SourceQuadraticBlockSquarefreeTail
public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticClassPair


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticBlockSquarefreeTail_eq_divisorTail (M K : ℝ) (g e : E) :
    sourceQuadraticBlockSquarefreeTail F S₀ hζ M g e K =
      sourceQuadraticDualDivisorTail F S₀ hζ M K g e := rfl

/-- The literal off-diagonal pair sum of the Full squarefree-tail terms. -/
def sourceQuadraticB3SquarefreeTail (M K : ℝ) (cols : Finset E) (a : E → ℂ) (g : E) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g ∧ p.1 ≠ p.2),
    star (a p.1) * a p.2 *
      sourceQuadraticDualDivisorTail F S₀ hζ M K g ((p.1 - g) + (p.2 - g))

/-- The named tail is exactly the remainder of the original Full pair expression. -/
theorem sourceQuadraticB3SquarefreeTail_replacement {M σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσ₁ : σ < 1) (K : ℝ)
    (cols : Finset E) (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (a : E → ℂ) (g : E) :
    (∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g ∧ p.1 ≠ p.2),
      star (a p.1) * a p.2 * sourceQuadraticBlockIdealFull F S₀ hζ M g
        ((p.1 - g) + (p.2 - g))) -
    (∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g ∧ p.1 ≠ p.2),
      star (a p.1) * a p.2 *
        (sourceQuadraticDualDivisorError F S₀ hζ M K σ g ((p.1 - g) + (p.2 - g)) +
          sourceQuadraticDualDivisorResidue F S₀ hζ M K g ((p.1 - g) + (p.2 - g)))) =
      sourceQuadraticB3SquarefreeTail F S₀ hζ M K cols a g := by
  unfold sourceQuadraticB3SquarefreeTail
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpair, hg, hne⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hpair
  have he := (sourceQuadraticPair_residual_data F S₀ p.1 p.2 g
    (hcols p.1 hb) (hcols p.2 hc) hg).2.2.2
  have he0 : (p.1 - g) + (p.2 - g) ≠ 0 := by
    intro hz
    exact hne ((sourceQuadraticPair_residual_eq_zero_iff F S₀ p.1 p.2 g hg).mp hz)
  rw [sourceQuadraticBlockIdealFull_eq_error_residue_tail F S₀ hζ hM hσ hσ₁ K g _ he he0]
  ring

end
end ArtinMatthews.SourceEulerAssembly
