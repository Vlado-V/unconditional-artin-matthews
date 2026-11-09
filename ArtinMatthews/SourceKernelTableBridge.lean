module

public import ArtinMatthews.SourceLocalKernelCoefficient
public import ArtinMatthews.SourceProductUnits
public import ArtinMatthews.SourcePowerWeightMultiplication


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized finite kernel on actual prime-power ideals equals
the checked literal local coefficient. Modulus, phase and weight
transport are all proved, including degree zero. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerFourier
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceDegreeIdealEq (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n : ℕ) :
    primePowerIdeal S₀ P n = Ideal.span {sourceDegreeGenerator S₀ a n} := by
  rw [primePowerIdeal, generator_power_ideal S₀ P a ha n, sourceDegreeGenerator_eq_pow]

theorem sourcePowerWeight_mk (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (x : PrincipalIntegerRing S₀) :
    sourceLocalPowerWeight S₀ P hP a ha χ n (Ideal.Quotient.mk _ x) =
      if 0 < n then (generatorResidueCharacter S₀ P hP a ha χ ^ n) (Ideal.Quotient.mk _ x) else 1 := by
  unfold sourceLocalPowerWeight
  erw [Ideal.quotEquivOfEq_mk]
  by_cases hn : 0 < n
  · rw [generatorPowerWeight, dite_eq_left hn, ite_eq_left hn, generatorResidueReduction_mk]
  · rw [generatorPowerWeight, dite_eq_right hn, ite_eq_right hn]

theorem sourcePowerWeight_degree (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ)
    (z : (PrincipalIntegerRing S₀) ⧸ Ideal.span {sourceDegreeGenerator S₀ a n}) :
    sourceLocalPowerWeight S₀ P hP a ha χ n
        ((Ideal.quotEquivOfEq (sourceDegreeIdealEq S₀ P a ha n)).symm z) =
      sourceDegreeWeight S₀ P hP a ha χ n z := by
  cases n with
  | zero => rfl
  | succ n =>
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk, sourcePowerWeight_mk,
      ite_eq_left (Nat.succ_pos n), generatorResidueCharacter_pow]
    rfl

theorem sourceDegreePhase (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (k t : ℕ) :
    pullAddChar (Ideal.quotEquivOfEq
        (congrArg₂ (fun X Y : Ideal (PrincipalIntegerRing S₀) => X * Y)
          (sourceDegreeIdealEq S₀ P a ha k) (sourceDegreeIdealEq S₀ P a ha t)).symm)
      (sourceLocalProductPhase S₀ P a ha k t) =
      sourceProductPhase S₀ (sourceDegreeGenerator S₀ a k) (sourceDegreeGenerator S₀ a t)
        (sourceDegreeGenerator_ne_zero S₀ a (exterior_generator_ne_zero S₀ P a ha) k)
        (sourceDegreeGenerator_ne_zero S₀ a (exterior_generator_ne_zero S₀ P a ha) t) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pullAddChar_apply, Ideal.quotEquivOfEq_mk, sourceLocalProductPhase_mk, sourceProductPhase_mk]
  rw [sourceDegreeGenerator_eq_pow, sourceDegreeGenerator_eq_pow]
  congr 1
  change (x : K) / (a : K) ^ (k + t) = (x : K) / ((a : K) ^ k * (a : K) ^ t)
  rw [pow_add]

theorem normalizedKernel_eq_coefficient (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t J : ℕ) :
    quotientCongruenceKernel (primePowerIdeal S₀ P k) (primePowerIdeal S₀ P t)
      (a ^ t) (a ^ J) (sourceLocalProductPhase S₀ P a ha k t)
      (sourceLocalPowerWeight S₀ P hP a ha χ k) (sourceLocalPowerWeight S₀ P hP a ha χ t) =
      standardLocalCoefficient S₀ P hP a ha χ t k J := by
  rw [quotientCongruenceKernel_transport (sourceDegreeIdealEq S₀ P a ha k)
    (sourceDegreeIdealEq S₀ P a ha t), sourceDegreePhase]
  have hW : (fun d => sourceLocalPowerWeight S₀ P hP a ha χ k
      ((Ideal.quotEquivOfEq (sourceDegreeIdealEq S₀ P a ha k)).symm d)) =
      sourceDegreeWeight S₀ P hP a ha χ k := by
    funext d
    exact sourcePowerWeight_degree S₀ P hP a ha χ k d
  have hZ : (fun v => sourceLocalPowerWeight S₀ P hP a ha χ t
      ((Ideal.quotEquivOfEq (sourceDegreeIdealEq S₀ P a ha t)).symm v)) =
      sourceDegreeWeight S₀ P hP a ha χ t := by
    funext v
    exact sourcePowerWeight_degree S₀ P hP a ha χ t v
  rw [hW, hZ, ← sourceDegreeGenerator_eq_pow S₀ a t]
  exact principalLocalCoefficient_eq_standard S₀ P hP a ha χ t k J

end
end ArtinMatthews.SourceCRTNormalization
