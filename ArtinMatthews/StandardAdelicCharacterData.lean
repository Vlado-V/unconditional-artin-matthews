module

public import ArtinMatthews.StandardAdelicLocalNontrivial
public import ArtinMatthews.StandardAdelicInfiniteNontrivial
public import ArtinMatthews.AdicConductorUniformizer
public import ArtinMatthews.AdelicCharacterData


set_option backward.privateInPublic true
@[expose] public section

/-! The actual constructed standard character satisfies every global and
local analytic input needed by the genuine adelic Gaussian product. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain
open ArtinMatthews.QuadraticWeil ArtinMatthews.VaryingKummerAnalytic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def localPrime (P : HeightOneSpectrum (𝓞 K)) : P.adicCompletion K :=
  algebraMap (𝓞 K) (P.adicCompletion K) (probeIdealUniformizer P)

theorem localPrime_ne_zero (P : HeightOneSpectrum (𝓞 K)) : localPrime K P ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (P.adicCompletion K))).mpr
    (probeIdealUniformizer_ne_zero P)

theorem localPrime_valuation (P : HeightOneSpectrum (𝓞 K)) :
    (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ))) (localPrime K P) =
      WithZero.exp (-1 : ℤ) := by
  change Valued.v ((algebraMap (𝓞 K) K (probeIdealUniformizer P) : K) : P.adicCompletion K) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', P.valuation_of_algebraMap,
    probeIdealUniformizer_valuation]

theorem localFiniteCharacter_conductorZero (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ traceBadPlaces K) :
    adicConductorZero K P (localFiniteCharacter K P) := by
  apply adicConductorZero_of_uniformizer K P (localFiniteCharacter K P)
    (localFiniteCharacter_integral K P) (localPrime K P) (localPrime_valuation K P)
  obtain ⟨x,hx⟩ := localFiniteCharacter_inverse_prime K P hP
  exact ⟨x,x.property,hx⟩

theorem character_data : AdelicCharacterData K (character K) where
  continuous := character_continuous K
  unitary := character_unitary K
  principal := character_principal K
  local_nontrivial := fun v => character_local_nontrivial K v (localFiniteCharacter_nontrivial K)
  conductor_zero := by
    have hgood : ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite, P ∉ traceBadPlaces K := by
      apply Filter.eventually_cofinite.mpr
      exact (traceBadPlaces K).finite_toSet.subset (fun _ h => not_not.mp h)
    filter_upwards [hgood] with P hP
    exact localFiniteCharacter_conductorZero K P hP

theorem character_nontrivial : ∃ a : ArchimedeanAdeles.Construction.Adeles K, character K a ≠ 1 := by
  let v : InfinitePlace K := Classical.arbitrary _
  obtain ⟨x,hx⟩ := localInfiniteCharacter_nontrivial K v
  exact ⟨ArchimedeanAdeles.Construction.localAdd K (.inl v) x, hx⟩

end
end ArtinMatthews.StandardAdelic
