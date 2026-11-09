module

public import ArtinMatthews.SIntegerPrincipalQuotient
public import ArtinMatthews.SIntegerCharacterTransport
public import ArtinMatthews.ProbeStandardSexticCRT


set_option backward.privateInPublic true
@[expose] public section

/-! Exact power-residue weights on actual S-integer quotients. A missing
modulus has weight one; every positive modulus retains the nonunit mask,
including positive exponents divisible by six. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def generatorResidueEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ≃+* ((𝓞 K) ⧸ P.asIdeal) :=
  ((principalQuotientEquiv S₀ P.asIdeal
    (by simpa only [pow_one] using principalPrimePower_coprime S₀ P hP 1)).toRingEquiv.trans
      (Ideal.quotEquivOfEq ha)).symm

theorem generatorResidueEquiv_mk (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (x : 𝓞 K) :
    generatorResidueEquiv S₀ P hP a ha
      (Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x)) = Ideal.Quotient.mk _ x := by
  let e := (principalQuotientEquiv S₀ P.asIdeal
    (by simpa only [pow_one] using principalPrimePower_coprime S₀ P hP 1)).toRingEquiv.trans
      (Ideal.quotEquivOfEq ha)
  have hp : principalQuotientEquiv S₀ P.asIdeal
      (by simpa only [pow_one] using principalPrimePower_coprime S₀ P hP 1)
      (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) :=
    principalQuotientEquiv_mk S₀ _ _ x
  have he : e (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) := by
    rw [RingEquiv.trans_apply]
    erw [hp, Ideal.quotEquivOfEq_mk]
  change e.symm _ = _
  rw [← he, e.symm_apply_apply]

def generatorResidueCharacter (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) :
    MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ℂ :=
  pullCharacter (generatorResidueEquiv S₀ P hP a ha) χ

theorem generatorResidueCharacter_orderOf (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) :
    orderOf (generatorResidueCharacter S₀ P hP a ha χ) = orderOf χ :=
  pullCharacter_orderOf _ _

def generatorResidueReduction (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (a : PrincipalIntegerRing S₀) (n : ℕ) (hn : 0 < n) :
    ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) →+*
      ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :=
  Ideal.Quotient.factor (by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_le_self (Nat.ne_of_gt hn))

theorem generatorResidueReduction_mk (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (a : PrincipalIntegerRing S₀) (n : ℕ) (hn : 0 < n) (x : PrincipalIntegerRing S₀) :
    generatorResidueReduction S₀ a n hn (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

def generatorPowerWeight (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ)
    (x : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) : ℂ :=
  if hn : 0 < n then
    (generatorResidueCharacter S₀ P hP a ha χ ^ n) (generatorResidueReduction S₀ a n hn x) else 1

theorem generatorPowerWeight_zero (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (x : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ 0}) :
    generatorPowerWeight S₀ P hP a ha χ 0 x = 1 := rfl

theorem generatorPowerWeight_nonunit (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (hn : 0 < n)
    (x : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n})
    (hx : ¬ IsUnit (generatorResidueReduction S₀ a n hn x)) :
    generatorPowerWeight S₀ P hP a ha χ n x = 0 := by
  rw [generatorPowerWeight, dite_eq_left hn]
  exact MulChar.map_nonunit _ hx

theorem generatorPowerWeight_eq_transport
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ)
    (z : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) :
    generatorPowerWeight S₀ P hP a ha χ n z =
      probePowerResidueWeight K P χ n (generatorQuotientEquiv S₀ P hP a ha n z) := by
  let e := generatorQuotientEquiv S₀ P hP a ha n
  obtain ⟨y, rfl⟩ := e.symm.surjective z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hm : e.symm (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) :=
    generatorQuotientEquiv_symm_mk S₀ P hP a ha n x
  rw [hm, generatorQuotientEquiv_mk]
  by_cases hn : 0 < n
  · rw [generatorPowerWeight, probePowerResidueWeight, dite_eq_left hn, dite_eq_left hn,
      generatorResidueReduction_mk, probeIdealResidueReduction_mk,
      MulChar.pow_apply' _ (Nat.ne_of_gt hn), MulChar.pow_apply' _ (Nat.ne_of_gt hn)]
    rw [generatorResidueCharacter, pullCharacter_apply, generatorResidueEquiv_mk]
  · rw [generatorPowerWeight, probePowerResidueWeight, dite_eq_right hn, dite_eq_right hn]

end
end ArtinMatthews.SIntegerQuotient
