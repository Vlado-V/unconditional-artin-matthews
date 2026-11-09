module

public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.FiniteSupportSourceCoordinates
public import ArtinMatthews.AbsoluteFourProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine product of four Dedekind norm majorants on the source
index, with the squarefree coordinate and all shared prime factors retained. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SourceExponentCoordinates := SourceEuler.SourceCoordinates (SourceExteriorPrime F S₀)

def sourceCoordinateMajorant (α β γ δ : ℝ) (a : SourceExponentCoordinates F S₀) : ℝ :=
  (sourcePrimeExponentNorm F S₀ a.1.val : ℝ) ^ (-α) *
    ((sourcePrimeExponentNorm F S₀ a.2.1 : ℝ) ^ (-β) *
      ((sourcePrimeExponentNorm F S₀ a.2.2.1 : ℝ) ^ (-γ) *
        (sourcePrimeExponentNorm F S₀ a.2.2.2 : ℝ) ^ (-δ)))

theorem sourceCoordinateMajorant_summable {α β γ δ : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hγ : 1 < γ) (hδ : 1 < δ) :
    Summable (sourceCoordinateMajorant F S₀ α β γ δ) := by
  exact SourceEuler.fourProduct_summable
    (fun c : {c : SourcePrimeExponents F S₀ // ∀ P, c P ≤ 1} =>
      (sourcePrimeExponentNorm F S₀ c.val : ℝ) ^ (-α))
    (fun n : SourcePrimeExponents F S₀ => (sourcePrimeExponentNorm F S₀ n : ℝ) ^ (-β))
    (fun s : SourcePrimeExponents F S₀ => (sourcePrimeExponentNorm F S₀ s : ℝ) ^ (-γ))
    (fun r : SourcePrimeExponents F S₀ => (sourcePrimeExponentNorm F S₀ r : ℝ) ^ (-δ))
    ((sourcePrimeExponentNorm_summable F S₀ hα).subtype (fun c => ∀ P, c P ≤ 1))
    (sourcePrimeExponentNorm_summable F S₀ hβ)
    (sourcePrimeExponentNorm_summable F S₀ hγ)
    (sourcePrimeExponentNorm_summable F S₀ hδ)

theorem sourceCoordinate_summable_of_bound (f : SourceExponentCoordinates F S₀ → ℂ)
    {α β γ δ : ℝ} (hα : 1 < α) (hβ : 1 < β) (hγ : 1 < γ) (hδ : 1 < δ)
    (hf : ∀ a, ‖f a‖ ≤ sourceCoordinateMajorant F S₀ α β γ δ a) : Summable f :=
  Summable.of_norm_bounded (sourceCoordinateMajorant_summable F S₀ hα hβ hγ hδ) hf

theorem sourceInitialCoordinateMajorant_summable :
    Summable (sourceCoordinateMajorant F S₀ (7 / 2) 10 3 12) :=
  sourceCoordinateMajorant_summable F S₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
end ArtinMatthews
