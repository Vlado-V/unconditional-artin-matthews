module

public import ArtinMatthews.SourceLocalUnitChange
public import ArtinMatthews.SourceKernelTableBridge


set_option backward.privateInPublic true
@[expose] public section

/-! Actual source unit changes land on the proved literal C coefficient.
All multiplier factors are kept as evaluations of the genuine source
weights on explicitly constructed quotient units. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerFourier
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceLocalUnitFactor (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) (sp ap hp : PrincipalIntegerRing S₀)
    (hsp : sp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hap : ap ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hhp : hp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) : ℂ :=
  let s := sourceProductUnit S₀ P hP a ha k t sp hsp
  let b := sourceProductUnit S₀ P hP a ha k t ap hap
  let c := sourceProductUnit S₀ P hP a ha k t hp hhp
  sourceLocalPowerWeight S₀ P hP a ha χ k
      (quotientUnitProjection (Ideal.mul_le_left : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)
        (c * b⁻¹)) *
    sourceLocalPowerWeight S₀ P hP a ha χ t
      (quotientUnitProjection (Ideal.mul_le_right : primePowerIdeal S₀ P k * primePowerIdeal S₀ P t ≤ _)
        (s * b * c⁻¹))

theorem sourceLocalKernel_eq_coefficient (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t J : ℕ) (sp ap hp : PrincipalIntegerRing S₀)
    (hsp : sp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hap : ap ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hhp : hp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    let s := sourceProductUnit S₀ P hP a ha k t sp hsp
    let b := sourceProductUnit S₀ P hP a ha k t ap hap
    let φ := sourceLocalProductPhase S₀ P a ha k t
    quotientCongruenceKernel (primePowerIdeal S₀ P k) (primePowerIdeal S₀ P t)
        (a ^ t * ap) (a ^ J * hp)
        (φ.mulShift (((s * b)⁻¹ :
          ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t))ˣ) :
            (PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ P k * primePowerIdeal S₀ P t)))
        (sourceLocalPowerWeight S₀ P hP a ha χ k) (sourceLocalPowerWeight S₀ P hP a ha χ t) =
      sourceLocalUnitFactor S₀ P hP a ha χ k t sp ap hp hsp hap hhp *
        standardLocalCoefficient S₀ P hP a ha χ t k J := by
  have h := sourceLocalKernel_unit_change S₀ P hP a ha χ k t J sp ap hp hsp hap hhp
  dsimp only at h
  rw [normalizedKernel_eq_coefficient S₀ P hP a ha χ k t J] at h
  exact h

end
end ArtinMatthews.SourceCRTNormalization
