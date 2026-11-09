module

public import ArtinMatthews.SourceExteriorValueEuler


set_option backward.privateInPublic true
@[expose] public section

/-! Full nonzero integral ideals in actual prime exponent coordinates.
The inverse is their normalized factorization. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]

def sourceFullPrimeEmbedding : ProbePrime F ↪ Ideal (𝓞 F) :=
  ⟨HeightOneSpectrum.asIdeal, HeightOneSpectrum.asIdeal_injective⟩

def sourceFullExponentIdeal (e : ProbePrime F →₀ ℕ) : Ideal (𝓞 F) :=
  e.prod (fun P n => P.asIdeal ^ n)

theorem sourceFullExponentIdeal_ne_bot (e : ProbePrime F →₀ ℕ) :
    sourceFullExponentIdeal F e ≠ ⊥ :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => pow_ne_zero _ P.ne_bot)

theorem sourceFullExponentIdeal_embDomain (e : ProbePrime F →₀ ℕ) :
    (e.embDomain (sourceFullPrimeEmbedding F)).prod (fun I n => I ^ n) =
      sourceFullExponentIdeal F e := Finsupp.prod_embDomain

theorem sourceFullExponentIdeal_factorization (e : ProbePrime F →₀ ℕ) :
    factorization (sourceFullExponentIdeal F e) = e.embDomain (sourceFullPrimeEmbedding F) := by
  rw [← sourceFullExponentIdeal_embDomain, ← Finsupp.prod_toMultiset]
  unfold factorization
  rw [normalizedFactors_prod_of_prime]
  · exact Finsupp.toMultiset_toFinsupp _
  · intro I hI
    rw [Finsupp.mem_toMultiset, Finsupp.support_embDomain] at hI
    obtain ⟨P, _, rfl⟩ := Finset.mem_map.mp hI
    exact P.prime

theorem sourceFullExponentIdeal_injective : Function.Injective (sourceFullExponentIdeal F) := by
  intro e f h
  apply Finsupp.embDomain_injective (sourceFullPrimeEmbedding F)
  simpa only [sourceFullExponentIdeal_factorization] using congrArg factorization h

def sourceFullIdealExponents (I : Ideal (𝓞 F)) : ProbePrime F →₀ ℕ :=
  Finsupp.comapDomain (sourceFullPrimeEmbedding F) (factorization I)
    (sourceFullPrimeEmbedding F).injective.injOn

theorem sourceFullIdealExponents_embDomain (I : Ideal (𝓞 F)) :
    (sourceFullIdealExponents F I).embDomain (sourceFullPrimeEmbedding F) = factorization I := by
  apply Finsupp.embDomain_comapDomain
  intro P hP
  have hp : P ∈ normalizedFactors I := by
    simpa only [support_factorization, Finset.mem_coe, Multiset.mem_toFinset] using hP
  have hprime := prime_of_normalized_factor P hp
  exact ⟨⟨P, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩, rfl⟩

theorem sourceFullIdealExponents_recover (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    sourceFullExponentIdeal F (sourceFullIdealExponents F I) = I := by
  rw [← sourceFullExponentIdeal_embDomain, sourceFullIdealExponents_embDomain,
    ← Finsupp.prod_toMultiset]
  unfold factorization
  rw [Multiset.toFinsupp_toMultiset]
  simpa only [normalize_eq] using prod_normalizedFactors_eq hI

def sourceFullExponentIdealEquiv : (ProbePrime F →₀ ℕ) ≃ {I : Ideal (𝓞 F) // I ≠ ⊥} where
  toFun e := ⟨sourceFullExponentIdeal F e, sourceFullExponentIdeal_ne_bot F e⟩
  invFun I := sourceFullIdealExponents F I.val
  left_inv e := (sourceFullExponentIdeal_injective F)
    (sourceFullIdealExponents_recover F (sourceFullExponentIdeal F e) (sourceFullExponentIdeal_ne_bot F e))
  right_inv I := Subtype.ext (sourceFullIdealExponents_recover F I.val I.property)

end
end ArtinMatthews.SourceEulerAssembly
