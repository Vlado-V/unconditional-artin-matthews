module

public import ArtinMatthews.StandardAdelicLocalQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! Exact membership in the actual one-prime pole ideal from the
finite-place valuations. These implications use the genuine integer
ring and ideal powers, not any global principal-prime generator. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sourcePoleIdeal_mem_of_valuation (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) (q : K)
    (hp : P.valuation K q ≤ WithZero.exp (n : ℤ))
    (hother : ∀ Q : HeightOneSpectrum (𝓞 K), Q ≠ P → Q.valuation K q ≤ 1) :
    q ∈ poleIdeal K P n := by
  rw [poleIdeal]
  apply (FractionalIdeal.mem_inv_iff (pow_ne_zero n (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot))).mpr
  intro y hy
  rw [← FractionalIdeal.coeIdeal_pow] at hy
  obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
  apply (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one K
  intro Q
  rw [map_mul]
  by_cases hQP : Q = P
  · subst Q
    rw [P.valuation_of_algebraMap]
    calc
      _ ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) :=
        mul_le_mul' hp ((P.intValuation_le_pow_iff_mem a n).mpr ha)
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · exact (mul_le_mul' (hother Q hQP) (Q.valuation_le_one a)).trans_eq (one_mul 1)

theorem sourcePoleIdeal_valuation (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (q : K) (hq : q ∈ poleIdeal K P n) : P.valuation K q ≤ WithZero.exp (n : ℤ) := by
  have h := poleIdeal_uniformizer_integral K P n q hq
  rw [map_mul, ← map_pow (algebraMap (𝓞 K) K), P.valuation_of_algebraMap,
    probeIdealUniformizer_pow_valuation] at h
  have hn : 0 < WithZero.exp (-(n : ℤ)) := pos_iff_ne_zero.mpr WithZero.exp_ne_zero
  have h' := (le_div_iff₀ hn).mpr h
  simpa only [one_div, ← WithZero.exp_neg, neg_neg] using h'

end
end ArtinMatthews.SourcePhysical
