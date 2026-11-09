module

public import ArtinMatthews.SourcePrimeExponents


set_option backward.privateInPublic true
@[expose] public section

/-! Exact exterior valuations of the fixed product generators. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourceAllowedPrimeGenerator_valuation
    (P Q : SourceExteriorPrime F S₀) :
    Q.val.valuation F (sourceAllowedPrimeGenerator F hζ S₀ P : F) =
      if P = Q then WithZero.exp (-1 : ℤ) else 1 := by
  classical
  by_cases h : P = Q
  · subst P
    rw [ite_eq_left rfl]
    exact exterior_generator_valuation (sourceHilbertSeed F S₀) Q.val Q.property _
      (sourceAllowedPrimeGenerator_ideal F hζ S₀ Q)
  · rw [ite_eq_right h]
    exact exterior_generator_other_valuation (sourceHilbertSeed F S₀) P.val _
      (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) Q.val Q.property
      (fun he => h (Subtype.ext he.symm))

theorem sourcePrimeExponentGenerator_valuation
    (e : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) :
    P.val.valuation F (sourcePrimeExponentGenerator F hζ S₀ e : F) =
      WithZero.exp (-(e P : ℤ)) := by
  classical
  unfold sourcePrimeExponentGenerator Finsupp.prod
  rw [SubmonoidClass.coe_finsetProd, map_prod]
  simp_rw [Subalgebra.coe_pow, map_pow, sourceAllowedPrimeGenerator_valuation]
  calc
    _ = ∏ Q ∈ e.support,
        if Q = P then WithZero.exp (-1 : ℤ) ^ e Q else 1 := by
      apply Finset.prod_congr rfl
      intro Q _
      split_ifs <;> simp only [one_pow]
    _ = WithZero.exp (-1 : ℤ) ^ e P := by
      by_cases hp : P ∈ e.support
      · simp only [Finset.prod_ite_eq', hp, ite_eq_left]
      · simp only [Finset.prod_ite_eq', hp,
          Finsupp.notMem_support_iff.mp hp, pow_zero, ite_self]
    _ = WithZero.exp (-(e P : ℤ)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp only [nsmul_eq_mul, mul_neg, mul_one]

theorem sourcePrimeExponentGenerator_mem_primePower_iff
    (e : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) (n : ℕ) :
    sourcePrimeExponentGenerator F hζ S₀ e ∈
      (P.val.asIdeal ^ n).map (algebraMap (𝓞 F) (sourceRing F S₀)) ↔ n ≤ e P := by
  calc
    _ ↔ P.val.valuation F (sourcePrimeExponentGenerator F hζ S₀ e : F) ≤
        WithZero.exp (-(n : ℤ)) :=
      principalInteger_power_mem_iff_valuation (sourceHilbertSeed F S₀)
        P.val P.property n (sourcePrimeExponentGenerator F hζ S₀ e)
    _ ↔ n ≤ e P := by
      rw [sourcePrimeExponentGenerator_valuation, WithZero.exp_le_exp]
      exact_mod_cast (neg_le_neg_iff (a := (e P : ℤ)) (b := (n : ℤ)))

theorem sourcePrimeExponentGenerator_exact_order
    (e : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) :
    sourcePrimeExponentGenerator F hζ S₀ e ∈
        (P.val.asIdeal ^ e P).map (algebraMap (𝓞 F) (sourceRing F S₀)) ∧
      sourcePrimeExponentGenerator F hζ S₀ e ∉
        (P.val.asIdeal ^ (e P + 1)).map (algebraMap (𝓞 F) (sourceRing F S₀)) := by
  rw [sourcePrimeExponentGenerator_mem_primePower_iff,
    sourcePrimeExponentGenerator_mem_primePower_iff]
  exact ⟨le_rfl, Nat.not_succ_le_self _⟩

end
end ArtinMatthews
