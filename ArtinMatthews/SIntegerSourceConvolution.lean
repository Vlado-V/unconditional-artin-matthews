module

public import ArtinMatthews.SIntegerSourceGaussAt


set_option backward.privateInPublic true
@[expose] public section

/-! The actual one-step source convolution, with its finite Gauss
constant and sign retained. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic OAI.SevenEighths
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem residueSource_convolution (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (h : PrincipalIntegerRing S₀) :
    (∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
      generatorResidueCharacter S₀ P hP a ha χ d *
        residueTransformOnSource S₀ P hP a ha ξ 1 (h - Quotient.out d)) =
      χ⁻¹ (-1) * residueSourceTau S₀ P hP a ha χ *
        residueTransformOnSource S₀ P hP a ha (ξ * χ⁻¹) 1 h := by
  let e := generatorResidueEquiv S₀ P hP a ha
  let ψ := residueSourcePhase S₀ P hP a ha
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hf (d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :
      residueTransformOnSource S₀ P hP a ha ξ 1 (h - Quotient.out d) =
        ProbeGauss.frequencyGauss ξ ψ (e (Ideal.Quotient.mk _ h) - e d) := by
    rw [residueTransformOnSource_transport]
    have hm : e (Ideal.Quotient.mk (Ideal.span {a}) (h - Quotient.out d)) =
        e (Ideal.Quotient.mk (Ideal.span {a}) h) - e d := by
      rw [map_sub (Ideal.Quotient.mk (Ideal.span {a})), Ideal.Quotient.mk_out]
      exact e.map_sub _ _
    change (∑' z : (𝓞 K) ⧸ P.asIdeal,
      (ξ ^ 1) z * ψ (e (Ideal.Quotient.mk (Ideal.span {a}) (h - Quotient.out d)) * z)) = _
    rw [hm]
    simp only [pow_one, tsum_fintype]
    rfl
  calc
    _ = ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
        χ (e d) * ProbeGauss.frequencyGauss ξ ψ (e (Ideal.Quotient.mk _ h) - e d) := by
      apply tsum_congr
      intro d
      rw [hf]
      rfl
    _ = ∑' d : (𝓞 K) ⧸ P.asIdeal,
        χ d * ProbeGauss.frequencyGauss ξ ψ (e (Ideal.Quotient.mk _ h) - d) :=
      e.toEquiv.tsum_eq (fun d : (𝓞 K) ⧸ P.asIdeal =>
        χ d * ProbeGauss.frequencyGauss ξ ψ (e (Ideal.Quotient.mk _ h) - d))
    _ = χ⁻¹ (-1) * residueSourceTau S₀ P hP a ha χ *
        residueTransformOnSource S₀ P hP a ha (ξ * χ⁻¹) 1 h := by
      rw [tsum_fintype, ProbeGauss.finite_gauss_convolution,
        residueTransformOnSource_transport]
      simp only [pow_one, residueSourceTau, tsum_fintype, gaussSum,
        ProbeGauss.frequencyGauss]
      rfl

def sourceScalarOne (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : PrincipalIntegerRing S₀) : ℂ :=
  ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
    generatorResidueCharacter S₀ P hP a ha χ d *
      sourceGaussAt S₀ P hP a ha ξ n (h - a ^ n * Quotient.out d)

theorem sourceScalarOne_eq (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K)
    (χ ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : PrincipalIntegerRing S₀) :
    sourceScalarOne S₀ P hP a ha χ ξ n h =
      χ⁻¹ (-1) * residueSourceTau S₀ P hP a ha χ *
        sourceGaussAt S₀ P hP a ha (ξ * χ⁻¹) n h := by
  by_cases hd : a ^ n ∣ h
  · obtain ⟨b, rfl⟩ := hd
    have he (d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :
        a ^ n * b - a ^ n * Quotient.out d = a ^ n * (b - Quotient.out d) := by ring
    unfold sourceScalarOne
    simp_rw [he, sourceGaussAt_lift]
    calc
      _ = (Ideal.absNorm P.asIdeal : ℂ) ^ n *
          ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
            generatorResidueCharacter S₀ P hP a ha χ d *
              residueTransformOnSource S₀ P hP a ha ξ 1 (b - Quotient.out d) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro d
        ring
      _ = _ := by
        rw [residueSource_convolution]
        ring
  · have hz (d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :
        ¬ a ^ n ∣ h - a ^ n * Quotient.out d := by
      intro hh
      apply hd
      have hs := dvd_add hh (dvd_mul_right (a ^ n) (Quotient.out d))
      simpa only [sub_add_cancel] using hs
    rw [sourceGaussAt_zero_off_support S₀ P hP a ha hbad _ n h hd, mul_zero]
    unfold sourceScalarOne
    apply Eq.trans (b := ∑' _d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a}, (0 : ℂ)) _ tsum_zero
    apply tsum_congr
    intro d
    rw [sourceGaussAt_zero_off_support S₀ P hP a ha hbad _ n _ (hz d), mul_zero]

end
end ArtinMatthews.SIntegerFourier
