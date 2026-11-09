module

public import ArtinMatthews.SourceUnitWeightValues


set_option backward.privateInPublic true
@[expose] public section

/-! The two actual source weights as homomorphisms on the common
product-quotient unit group. Their values on local elements are proved. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceProductWeightLeft (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) :
    ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ →* ℂˣ :=
  (Units.map (sourcePowerWeightHom S₀ P hP a ha χ k)).comp
    (Units.map (Ideal.Quotient.factor
      (Ideal.mul_le_left : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)).toMonoidHom)

def sourceProductWeightRight (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) :
    ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ →* ℂˣ :=
  (Units.map (sourcePowerWeightHom S₀ P hP a ha χ t)).comp
    (Units.map (Ideal.Quotient.factor
      (Ideal.mul_le_right : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)).toMonoidHom)

theorem sourceProductWeightLeft_val (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ)
    (u : ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ) :
    (sourceProductWeightLeft S₀ P hP a ha χ k t u : ℂ) =
      sourceLocalPowerWeight S₀ P hP a ha χ k
        (quotientUnitProjection (Ideal.mul_le_left : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _) u) := rfl

theorem sourceProductWeightRight_val (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ)
    (u : ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ) :
    (sourceProductWeightRight S₀ P hP a ha χ k t u : ℂ) =
      sourceLocalPowerWeight S₀ P hP a ha χ t
        (quotientUnitProjection (Ideal.mul_le_right : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _) u) := rfl

theorem sourceProductWeightLeft_element (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    sourceProductWeightLeft S₀ P hP a ha χ k t (sourceProductUnit S₀ P hP a ha k t x hx) =
      sourceCharacterUnit S₀ P hP a ha χ x hx ^ k := by
  apply Units.ext
  rw [sourceProductWeightLeft_val, sourceProductUnit_left, sourcePowerWeight_unitValue,
    Units.val_pow_eq_pow_val]

theorem sourceProductWeightRight_element (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    sourceProductWeightRight S₀ P hP a ha χ k t (sourceProductUnit S₀ P hP a ha k t x hx) =
      sourceCharacterUnit S₀ P hP a ha χ x hx ^ t := by
  apply Units.ext
  rw [sourceProductWeightRight_val, sourceProductUnit_right, sourcePowerWeight_unitValue,
    Units.val_pow_eq_pow_val]

end
end ArtinMatthews.SourceCRTNormalization
