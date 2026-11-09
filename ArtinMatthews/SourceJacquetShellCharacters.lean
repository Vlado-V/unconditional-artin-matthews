module

public import ArtinMatthews.SourceJacquetShellIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The source shell character is the literal negative eighth power,
written as a natural power using its genuine sextic order. The principal
case remains masked on nonunits in both orthogonality sums. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient SIntegerFourier StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
variable (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)

def sourceJacquetShellCharacter (l : ℕ) : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ := χ ^ (4 * l)

omit [NumberField F] in
theorem sourceJacquetShellCharacter_eq_negative (hχ : orderOf χ = 6) (l : ℕ) :
    sourceJacquetShellCharacter F P χ l = χ ^ (-(8 * (l : ℤ))) := by
  have hp : χ ^ (6 : ℕ) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hχ])
  have hp' : χ ^ (6 : ℤ) = 1 := by exact_mod_cast hp
  calc
    _ = χ ^ (4 * (l : ℤ)) := by
      have hc : ((4 * l : ℕ) : ℤ) = 4 * (l : ℤ) := by push_cast; rfl
      rw [← hc, zpow_natCast]
      rfl
    _ = χ ^ (-(8 * (l : ℤ)) + 6 * (2 * (l : ℤ))) := by congr 1; ring
    _ = χ ^ (-(8 * (l : ℤ))) * χ ^ (6 * (2 * (l : ℤ))) := zpow_add _ _ _
    _ = _ := by rw [zpow_mul χ 6 (2 * (l : ℤ)), hp', one_zpow, mul_one]

omit [NumberField F] in
theorem sourceJacquetShellCharacter_principal_iff (hχ : orderOf χ = 6) (l : ℕ) :
    sourceJacquetShellCharacter F P χ l = 1 ↔ 3 ∣ l := by
  rw [sourceJacquetShellCharacter, ← orderOf_dvd_iff_pow_eq_one, hχ]
  omega

theorem sourceJacquetShellCharacter_sum (hχ : orderOf χ = 6) (l : ℕ) :
    (∑' z : (𝓞 F) ⧸ P.asIdeal, sourceJacquetShellCharacter F P χ l z) =
      if 3 ∣ l then (Ideal.absNorm P.asIdeal : ℂ) - 1 else 0 := by
  let : Field ((𝓞 F) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 F) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 F) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card ((𝓞 F) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  by_cases hl : 3 ∣ l
  · rw [ite_eq_left hl, (sourceJacquetShellCharacter_principal_iff F P χ hχ l).mpr hl,
      tsum_fintype, MulChar.sum_one_eq_card_units, ← hcard,
      Fintype.card_eq_card_units_add_one ((𝓞 F) ⧸ P.asIdeal)]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  · rw [ite_eq_right hl, tsum_fintype]
    exact MulChar.sum_eq_zero_of_ne_one (mt (sourceJacquetShellCharacter_principal_iff F P χ hχ l).mp hl)

theorem sourceJacquetShellCharacter_tau_principal (hχ : orderOf χ = 6) (l : ℕ) (hl : 3 ∣ l)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces F) :
    residueSourceTau S₀ P hP a ha (sourceJacquetShellCharacter F P χ l) = -1 := by
  rw [(sourceJacquetShellCharacter_principal_iff F P χ hχ l).mpr hl]
  exact residueSourceTau_principal S₀ P hP a ha hbad

end
end ArtinMatthews
