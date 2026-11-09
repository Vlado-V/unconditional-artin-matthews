module

public import ArtinMatthews.StandardAdelicCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite approximation defining the standard character
at one completion, retaining the rational remainder and integrality
at every other place. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain StandardAdelic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sourceLocalRationalRemainder (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K) :
    ∃ q : K,
      x - algebraMap K (P.adicCompletion K) q ∈ P.adicCompletionIntegers K ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), Q ≠ P → Q.valuation K q ≤ 1) ∧
      localFiniteCharacter K P x = (rationalCharacter K q)⁻¹ := by
  let a := RestrictedProduct.single (fun Q : HeightOneSpectrum (𝓞 K) => Q.adicCompletionIntegers K) P x
  let q := finiteRationalPart K a
  have hq := finiteRationalPart_spec K a
  refine ⟨q, ?_, ?_, ?_⟩
  · have h := hq P
    change a P - algebraMap K (P.adicCompletion K) q ∈ P.adicCompletionIntegers K at h
    dsimp only [a] at h
    rwa [RestrictedProduct.single_eq_same] at h
  · intro Q hQP
    have h := hq Q
    change a Q - algebraMap K (Q.adicCompletion K) q ∈ Q.adicCompletionIntegers K at h
    dsimp only [a] at h
    rw [RestrictedProduct.single_eq_of_ne _ x hQP, zero_sub] at h
    have h' := (Q.adicCompletionIntegers K).toSubring.neg_mem h
    simp only [neg_neg] at h'
    change Valued.v (q : Q.adicCompletion K) ≤ 1 at h'
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h'
  · rw [localFiniteCharacter_single]
    exact finiteCharacter_eq K a q hq

end
end ArtinMatthews.SourcePhysical
