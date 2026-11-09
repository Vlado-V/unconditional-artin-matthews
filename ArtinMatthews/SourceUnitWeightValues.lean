module

public import ArtinMatthews.SourcePowerWeightMultiplication
public import ArtinMatthews.SourceProductUnits
public import ArtinMatthews.SIntegerPowerResidueSymbol


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine source weight restricted to quotient units. This also
covers degree zero, where it is the constant-one homomorphism. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerResidueSymbol
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourcePowerWeightHom (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) :
    ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P n) →* ℂ where
  toFun := sourceLocalPowerWeight S₀ P hP a ha χ n
  map_one' := sourceLocalPowerWeight_one S₀ P hP a ha χ n
  map_mul' := sourceLocalPowerWeight_mul S₀ P hP a ha χ n

def sourceCharacterUnit (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) : ℂˣ :=
  χ.toUnitHom (sIntegerResidueUnit K S₀ P hP a ha x hx)

theorem sourceCharacterUnit_val (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    (sourceCharacterUnit S₀ P hP a ha χ x hx : ℂ) =
      generatorResidueCharacter S₀ P hP a ha χ (Ideal.Quotient.mk _ x) := rfl

theorem sourcePowerWeight_unitValue (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    sourceLocalPowerWeight S₀ P hP a ha χ n (Ideal.Quotient.mk _ x) =
      (sourceCharacterUnit S₀ P hP a ha χ x hx : ℂ) ^ n := by
  cases n with
  | zero => simp only [sourceLocalPowerWeight_zero, pow_zero]
  | succ n =>
    unfold sourceLocalPowerWeight
    erw [Ideal.quotEquivOfEq_mk]
    rw [generatorPowerWeight, dite_eq_left (Nat.succ_pos n), generatorResidueReduction_mk,
      MulChar.pow_apply' _ (Nat.succ_ne_zero n), sourceCharacterUnit_val]

theorem sourceUnitFactor_zpow {G : Type*} [CommGroup G] (s b c : G) (k t : ℤ) :
    (c * b⁻¹) ^ k * (s * b * c⁻¹) ^ t = c ^ (k - t) * s ^ t * b ^ (t - k) := by
  rw [mul_zpow, mul_zpow, mul_zpow, inv_zpow, inv_zpow, zpow_sub, zpow_sub]
  ac_rfl

end
end ArtinMatthews.SourceCRTNormalization
