module

public import ArtinMatthews.StandardAdelicCharacterData
public import ArtinMatthews.ProbeIdealPrimeFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Literal standard local quotient phases psi_P(-x/pi^n), with pi an
actual integral local uniformizer. Periodicity, coherence, and (away from
the different) primitivity are proved from the constructed global character. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain
open ArtinMatthews.VaryingKummerAnalytic ArtinMatthews.QuadraticWeil
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem localInteger_valuation (P : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ)))
      (algebraMap (𝓞 K) (P.adicCompletion K) x) = P.intValuation x := by
  change Valued.v ((algebraMap (𝓞 K) K x : K) : P.adicCompletion K) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', P.valuation_of_algebraMap]

theorem localPrime_pow_valuation (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ)))
      (localPrime K P ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [localPrime, ← map_pow, localInteger_valuation, probeIdealUniformizer_pow_valuation]

def localIntegerPhase (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) : AddChar (𝓞 K) ℂ where
  toFun x := localFiniteCharacter K P (-(algebraMap (𝓞 K) (P.adicCompletion K) x) / localPrime K P ^ n)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, neg_add, add_div, AddChar.map_add_eq_mul]

theorem localIntegerPhase_period (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : 𝓞 K) (hx : x ∈ P.asIdeal ^ n) : localIntegerPhase K P n x = 1 := by
  apply localFiniteCharacter_integral
  change Valued.v (-(algebraMap (𝓞 K) (P.adicCompletion K) x) / localPrime K P ^ n) ≤ 1
  rw [map_div₀, Valuation.map_neg, localPrime_pow_valuation, localInteger_valuation]
  apply (div_le_one₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)).mpr
  exact (P.intValuation_le_pow_iff_mem x n).mpr hx

def localQuotientPhase (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift (P.asIdeal ^ n).toAddSubgroup
    (localIntegerPhase K P n).toAddMonoidHom (fun x hx => localIntegerPhase_period K P n x hx))

theorem localQuotientPhase_mk (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : 𝓞 K) :
    localQuotientPhase K P n (Ideal.Quotient.mk _ x) =
      localFiniteCharacter K P (-(algebraMap (𝓞 K) (P.adicCompletion K) x) / localPrime K P ^ n) := rfl

theorem localQuotientPhase_zero (P : HeightOneSpectrum (𝓞 K)) : localQuotientPhase K P 0 = 1 := by
  ext x
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact localIntegerPhase_period K P 0 x (by simp)

theorem localQuotientPhase_coherent (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ) (x : 𝓞 K) :
    localQuotientPhase K P (n+k) (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ k * x)) =
      localQuotientPhase K P n (Ideal.Quotient.mk _ x) := by
  rw [localQuotientPhase_mk, localQuotientPhase_mk]
  congr 1
  rw [map_mul, map_pow]
  change -(localPrime K P ^ k * algebraMap (𝓞 K) (P.adicCompletion K) x) / localPrime K P ^ (n+k) = _
  rw [pow_add]
  field_simp [localPrime_ne_zero K P]

theorem integer_dense_local (P : HeightOneSpectrum (𝓞 K)) :
    DenseRange (algebraMap (𝓞 K) (P.adicCompletionIntegers K)) := by
  exact (Function.surjective_eval P).denseRange.comp
    (StrongApproximation.Construction.denseRange_integer_finiteIntegerProduct K) (continuous_apply P)

theorem localFiniteCharacter_integer_dual (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ traceBadPlaces K) (c : P.adicCompletion K) :
    (∀ b : 𝓞 K, localFiniteCharacter K P (c * algebraMap (𝓞 K) (P.adicCompletion K) b) = 1) ↔
      c ∈ P.adicCompletionIntegers K := by
  constructor
  · intro hh
    have hcont : Continuous (fun b : P.adicCompletionIntegers K => localFiniteCharacter K P (c * (b : P.adicCompletion K))) :=
      (localFiniteCharacter_continuous K P).comp (continuous_const.mul continuous_subtype_val)
    have heq : (fun b : P.adicCompletionIntegers K => localFiniteCharacter K P (c * (b : P.adicCompletion K))) =
        fun _ => (1 : ℂ) := by
      apply (integer_dense_local K P).equalizer hcont continuous_const
      funext b
      exact hh b
    exact (adicConductorZero_dual K P (localFiniteCharacter K P) (localFiniteCharacter_conductorZero K P hP) c).mp
      (fun b hb => congrFun heq ⟨b,hb⟩)
  · intro hc b
    apply localFiniteCharacter_integral
    exact (P.adicCompletionIntegers K).toSubring.mul_mem hc
      (HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := K) P b)

theorem localQuotientPhase_primitive (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (hP : P ∉ traceBadPlaces K) : (localQuotientPhase K P n).IsPrimitive := by
  intro a ha hshift
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  apply ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  let c := -(algebraMap (𝓞 K) (P.adicCompletion K) a) / localPrime K P ^ n
  have hc : c ∈ P.adicCompletionIntegers K := (localFiniteCharacter_integer_dual K P hP c).mp (by
    intro b
    have h := congrArg (fun χ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ => χ (Ideal.Quotient.mk _ b)) hshift
    change localQuotientPhase K P n ((Ideal.Quotient.mk _ a) * (Ideal.Quotient.mk _ b)) = 1 at h
    rw [← map_mul (Ideal.Quotient.mk (P.asIdeal ^ n)) a b, localQuotientPhase_mk] at h
    change localFiniteCharacter K P (c * algebraMap (𝓞 K) (P.adicCompletion K) b) = 1
    convert h using 1
    congr 1
    dsimp only [c]
    rw [map_mul]
    ring)
  change Valued.v c ≤ 1 at hc
  dsimp only [c] at hc
  rw [map_div₀, Valuation.map_neg, localPrime_pow_valuation, localInteger_valuation] at hc
  exact (P.intValuation_le_pow_iff_mem a n).mp
    ((div_le_one₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)).mp hc)

theorem localQuotientPhase_comparison_exists (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (hP : P ∉ traceBadPlaces K) :
    ∃ u : ((𝓞 K) ⧸ P.asIdeal ^ n)ˣ,
      (probeIdealPhase K P n).mulShift (u : _) = localQuotientPhase K P n := by
  let : Finite ((𝓞 K) ⧸ P.asIdeal ^ n) := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero n P.ne_bot)
  let : Fintype ((𝓞 K) ⧸ P.asIdeal ^ n) := Fintype.ofFinite _
  exact probe_addChar_exists_unit_shift _ _ (probeIdealPhase_primitive K P n) (localQuotientPhase_primitive K P n hP)

end
end ArtinMatthews.StandardAdelic
