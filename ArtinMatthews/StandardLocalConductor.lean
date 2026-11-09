module

public import ArtinMatthews.StandardLocalDifferent
public import ArtinMatthews.StandardLocalRationalRemainder
public import ArtinMatthews.StandardLocalPoleValuation


set_option backward.privateInPublic true
@[expose] public section

/-! The exact conductor of the constructed standard finite character,
including ramified places: the annihilator of local integers is the
codifferent ball of radius exp(d_P). -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal StandardAdelic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

abbrev sourceLocalValuation (P : HeightOneSpectrum (𝓞 K)) :
    Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v

def sourceLocalBall (P : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Set (P.adicCompletion K) :=
  {x | sourceLocalValuation K P x ≤ WithZero.exp n}

theorem sourceLocalCharacter_codifferent (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K)
    (hx : x ∈ sourceLocalBall K P (sourceDifferentExponent K P : ℤ)) :
    localFiniteCharacter K P x = 1 := by
  obtain ⟨q, hrem, hout, hψ⟩ := sourceLocalRationalRemainder K P x
  let v := sourceLocalValuation K P
  let d := sourceDifferentExponent K P
  have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (d : ℤ) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (Int.natCast_nonneg d)
  have hr : v (x - algebraMap K (P.adicCompletion K) q) ≤ 1 := hrem
  have hQ : v (algebraMap K (P.adicCompletion K) q) ≤ WithZero.exp (d : ℤ) := by
    have H := v.map_sub_le (show v x ≤ WithZero.exp (d : ℤ) from hx) (hr.trans h1)
    simpa only [sub_sub_cancel] using H
  have hq : P.valuation K q ≤ WithZero.exp (d : ℤ) := by
    change Valued.v (q : P.adicCompletion K) ≤ WithZero.exp (d : ℤ) at hQ
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hQ
  have hc := sourcePoleIdeal_le_codifferent K P (sourcePoleIdeal_mem_of_valuation K P d q hq hout)
  rw [FractionalIdeal.mem_dual one_ne_zero] at hc
  have htrace : Algebra.trace ℚ K q ∈ (algebraMap ℤ ℚ).range := by
    have hm : (1 : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨1, map_one _⟩
    simpa only [Algebra.traceForm_apply, mul_one] using hc 1 hm
  rw [hψ, (rationalCharacter_eq_one_iff K q).mpr htrace, inv_one]

theorem sourceLocalCharacter_next_ball_nontrivial (P : HeightOneSpectrum (𝓞 K)) :
    ∃ x ∈ sourceLocalBall K P ((sourceDifferentExponent K P : ℤ) + 1),
      localFiniteCharacter K P x ≠ 1 := by
  let d := sourceDifferentExponent K P
  obtain ⟨q, hq, htr⟩ := exists_nonintegral_trace_in_poleIdeal K P (d + 1) (by
    rw [sourceCodifferent_count K P]
    change -((d + 1 : ℕ) : ℤ) < -(d : ℤ)
    omega)
  refine ⟨algebraMap K (P.adicCompletion K) q, ?_, ?_⟩
  · change Valued.v (q : P.adicCompletion K) ≤ WithZero.exp ((d : ℤ) + 1)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact_mod_cast sourcePoleIdeal_valuation K P (d + 1) q hq
  · rw [localFiniteCharacter_pole K P (d + 1) q hq]
    intro h
    apply htr
    apply (rationalCharacter_eq_one_iff K q).mp
    simpa only [inv_inv, inv_one] using congrArg Inv.inv h

theorem sourceLocalInteger_annihilator_iff (P : HeightOneSpectrum (𝓞 K)) (y : P.adicCompletion K) :
    (∀ x ∈ P.adicCompletionIntegers K, localFiniteCharacter K P (y * x) = 1) ↔
      y ∈ sourceLocalBall K P (sourceDifferentExponent K P : ℤ) := by
  let v := sourceLocalValuation K P
  let d := sourceDifferentExponent K P
  constructor
  · intro h
    change v y ≤ WithZero.exp (d : ℤ)
    by_contra hn
    have hy : WithZero.exp (d : ℤ) < v y := lt_of_not_ge hn
    have hv0 : 0 < v y := (pos_iff_ne_zero.mpr WithZero.exp_ne_zero).trans hy
    have hy0 : y ≠ 0 := by
      intro he
      rw [he, map_zero] at hv0
      exact (lt_irrefl 0) hv0
    have hlog : (d : ℤ) < WithZero.log (v y) := WithZero.exp_lt_exp.mp (by
      rw [WithZero.exp_log hv0.ne']
      exact hy)
    have hnext : WithZero.exp ((d : ℤ) + 1) ≤ v y := by
      rw [← WithZero.exp_log hv0.ne', WithZero.exp_le_exp]
      omega
    obtain ⟨z, hz, hψ⟩ := sourceLocalCharacter_next_ball_nontrivial K P
    have hzI : z / y ∈ P.adicCompletionIntegers K := by
      change v (z / y) ≤ 1
      rw [map_div₀, div_le_one₀ hv0]
      exact (show v z ≤ WithZero.exp ((d : ℤ) + 1) from hz).trans hnext
    apply hψ
    have hh := h (z / y) hzI
    rwa [show y * (z / y) = z by field_simp [hy0]] at hh
  · intro hy x hx
    apply sourceLocalCharacter_codifferent K P
    change v (y * x) ≤ WithZero.exp (d : ℤ)
    rw [map_mul]
    exact (mul_le_mul' (show v y ≤ WithZero.exp (d : ℤ) from hy) (show v x ≤ 1 from hx)).trans_eq
      (mul_one _)

end
end ArtinMatthews.SourcePhysical
