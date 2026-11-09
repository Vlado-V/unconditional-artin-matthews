module

public import ArtinMatthews.StandardAdelicCharacter
public import ArtinMatthews.StandardAdelicPoleIdeals


set_option backward.privateInPublic true
@[expose] public section

/-! Nontriviality of every actual finite local restriction, and conductor
zero outside the finite support of the actual codifferent. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain FractionalIdeal
open ArtinMatthews.VaryingKummerAnalytic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField nonZeroDivisors BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem rationalCharacter_eq_one_iff (q : K) :
    rationalCharacter K q = 1 ↔ Algebra.trace ℚ K q ∈ (algebraMap ℤ ℚ).range := by
  change archCharacter K (algebraMap K (InfiniteAdeleRing K) q) = 1 ↔ _
  rw [archCharacter_rational, Complex.exp_eq_one_iff]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    have h := mul_right_cancel₀ hc hn
    refine ⟨n, ?_⟩
    exact_mod_cast h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    congr 1
    exact_mod_cast hn.symm

theorem poleIdeal_completion_integral_outside (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (q : K) (hq : q ∈ poleIdeal K P n) (w : HeightOneSpectrum (𝓞 K)) (hw : w ≠ P) :
    algebraMap K (w.adicCompletion K) q ∈ w.adicCompletionIntegers K := by
  change Valued.v (q : w.adicCompletion K) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact poleIdeal_valuation_outside K P n q hq w hw

theorem localFiniteCharacter_pole (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (q : K) (hq : q ∈ poleIdeal K P n) :
    localFiniteCharacter K P (algebraMap K (P.adicCompletion K) q) = (rationalCharacter K q)⁻¹ :=
  localFiniteCharacter_rational K P q (poleIdeal_completion_integral_outside K P n q hq)

theorem localFiniteCharacter_nontrivial (P : HeightOneSpectrum (𝓞 K)) :
    ∃ x : P.adicCompletion K, localFiniteCharacter K P x ≠ 1 := by
  obtain ⟨n,q,hq,ht⟩ := exists_nonintegral_trace_one_prime K P
  refine ⟨algebraMap K (P.adicCompletion K) q, ?_⟩
  rw [localFiniteCharacter_pole K P n q hq]
  intro he
  apply ht
  apply (rationalCharacter_eq_one_iff K q).mp
  simpa only [inv_inv, inv_one] using congrArg Inv.inv he

def traceBadPlaces : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := K)
    (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)))).toFinset

theorem mem_traceBadPlaces (P : HeightOneSpectrum (𝓞 K)) :
    P ∈ traceBadPlaces K ↔ FractionalIdeal.count K P
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := Set.Finite.mem_toFinset _

theorem localFiniteCharacter_inverse_prime (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ traceBadPlaces K) :
    ∃ x : P.adicCompletionIntegers K,
      localFiniteCharacter K P
        ((algebraMap (𝓞 K) (P.adicCompletion K) (probeIdealUniformizer P))⁻¹ * (x : P.adicCompletion K)) ≠ 1 := by
  have hc : FractionalIdeal.count K P
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) = 0 := by
    simpa only [mem_traceBadPlaces, not_not] using hP
  obtain ⟨q,hq,ht⟩ := exists_nonintegral_trace_in_poleIdeal K P 1 (by rw [hc]; norm_num)
  let π := algebraMap (𝓞 K) (P.adicCompletion K) (probeIdealUniformizer P)
  let y := algebraMap K (P.adicCompletion K) (q * algebraMap (𝓞 K) K (probeIdealUniformizer P))
  have hy : y ∈ P.adicCompletionIntegers K := by
    change Valued.v ((q * algebraMap (𝓞 K) K (probeIdealUniformizer P) : K) : P.adicCompletion K) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [pow_one] using poleIdeal_uniformizer_integral K P 1 q hq
  have hπ : π ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (P.adicCompletion K))).mpr
    (probeIdealUniformizer_ne_zero P)
  have he : π⁻¹*y = algebraMap K (P.adicCompletion K) q := by
    dsimp only [y, π]
    rw [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) K (P.adicCompletion K),
      mul_comm (algebraMap K (P.adicCompletion K) q), inv_mul_cancel_left₀ hπ]
  refine ⟨⟨y,hy⟩, ?_⟩
  change localFiniteCharacter K P (π⁻¹*y) ≠ 1
  rw [he, localFiniteCharacter_pole K P 1 q hq]
  intro hz
  apply ht
  apply (rationalCharacter_eq_one_iff K q).mp
  simpa only [inv_inv, inv_one] using congrArg Inv.inv hz

theorem localFiniteCharacter_conductor_zero_ae :
    ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (∀ x : P.adicCompletionIntegers K, localFiniteCharacter K P (x : P.adicCompletion K) = 1) ∧
      ∃ x : P.adicCompletionIntegers K, localFiniteCharacter K P
        ((algebraMap (𝓞 K) (P.adicCompletion K) (probeIdealUniformizer P))⁻¹ * (x : P.adicCompletion K)) ≠ 1 := by
  have hgood : ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite, P ∉ traceBadPlaces K := by
    apply Filter.eventually_cofinite.mpr
    exact (traceBadPlaces K).finite_toSet.subset (fun _ h => not_not.mp h)
  filter_upwards [hgood] with P hP
  exact ⟨fun x => localFiniteCharacter_integral K P x x.property,
    localFiniteCharacter_inverse_prime K P hP⟩

end
end ArtinMatthews.StandardAdelic
