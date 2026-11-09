module

public import ArtinMatthews.ProbeIdealCyclotomicSource
public import ArtinMatthews.ProbeBadPrimeFiniteProduct
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity


set_option backward.privateInPublic true
@[expose] public section

/-! The actual principal angular correction on (s,1,1/6). Its finite
cutoff contains the modulus and the primes over six. The sixth power of
the finite ray value is retained in the third local parameter. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain Set Filter AngularLambda
open OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcreteTraceCRT
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}

def principalAngularCutoffBound (K : Type*) [Field K] [NumberField K] (M : Ideal (𝓞 K)) : ℕ :=
  max ArtinMatthews.probeEulerCutoff
    (max (Ideal.absNorm M) (Ideal.absNorm (Ideal.span {(6 : 𝓞 K)})))

theorem principalAngularCutoff_finite :
    {P : ArtinMatthews.ProbePrime K | Ideal.absNorm P.asIdeal ≤ principalAngularCutoffBound K M}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le _).preimage HeightOneSpectrum.asIdeal_injective.injOn

def principalAngularCutoff (K : Type*) [Field K] [NumberField K] (M : Ideal (𝓞 K)) :
    Finset (ArtinMatthews.ProbePrime K) := (principalAngularCutoff_finite (K := K) (M := M)).toFinset

theorem mem_principalAngularCutoff (P : ArtinMatthews.ProbePrime K) :
    P ∈ principalAngularCutoff K M ↔ Ideal.absNorm P.asIdeal ≤ principalAngularCutoffBound K M :=
  Set.Finite.mem_toFinset _

theorem probePrimeCutoff_subset_principalAngularCutoff :
    ArtinMatthews.probePrimeCutoff K ⊆ principalAngularCutoff K M := by
  intro P hP
  exact (mem_principalAngularCutoff P).mpr
    (((ArtinMatthews.mem_probePrimeCutoff K P).mp hP).trans (le_max_left _ _))

theorem principalAngular_prime_coprime_of_not_le (P : ArtinMatthews.ProbePrime K)
    (J : Ideal (𝓞 K)) (hJ : ¬ J ≤ P.asIdeal) : IsCoprime P.asIdeal J := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra h
  have he := P.isMaximal.eq_of_le h le_sup_left
  exact hJ (le_sup_right.trans_eq he.symm)

theorem principalAngularCutoff_coprime (hM : M ≠ ⊥) (P : ArtinMatthews.ProbePrime K)
    (hP : P ∉ principalAngularCutoff K M) : IsCoprime P.asIdeal M := by
  apply principalAngular_prime_coprime_of_not_le P M
  intro hMP
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hM))
    (Ideal.absNorm_dvd_absNorm_of_le hMP)
  apply hP
  exact (mem_principalAngularCutoff P).mpr
    (hn.trans ((le_max_left _ _).trans (le_max_right _ _)))

theorem principalAngularCutoff_six_not_mem (P : ArtinMatthews.ProbePrime K)
    (hP : P ∉ principalAngularCutoff K M) : (6 : 𝓞 K) ∉ P.asIdeal := by
  intro h6
  have h60 : (Ideal.span {(6 : 𝓞 K)} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h60))
    (Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr h6))
  exact hP ((mem_principalAngularCutoff P).mpr
    (hn.trans ((le_max_right _ _).trans (le_max_right _ _))))

theorem principalAngularCutoff_coprime_three (P : ArtinMatthews.ProbePrime K)
    (hP : P ∉ principalAngularCutoff K M) : IsCoprime P.asIdeal (Ideal.span {(3 : 𝓞 K)}) := by
  apply principalAngular_prime_coprime_of_not_le P _
  intro h3
  have hm : (3 : 𝓞 K) ∈ P.asIdeal := h3 (Ideal.subset_span (by simp))
  exact principalAngularCutoff_six_not_mem P hP (by
    simpa only [show (2 : 𝓞 K) * 3 = 6 by norm_num] using P.asIdeal.mul_mem_left 2 hm)

theorem cyclotomicAngularIdeal_norm_le_one (hζ : IsPrimitiveRoot ζ 12) (I : Ideal (𝓞 K)) :
    ‖cyclotomicAngularIdeal hζ I‖ ≤ 1 := by
  let : Algebra BaseField K := baseAlgebraOfTwelve hζ
  change ‖angularNormIdeal K I‖ ≤ 1
  rw [angularNormIdeal_apply, eisensteinAngularIdeal_apply]
  by_cases h : eisEmbedding (primaryGenerator (Ideal.relNorm BaseIntegers I)) = 0
  · simp only [h, complexAngular, norm_zero, Complex.ofReal_zero, div_zero, zero_le_one]
  · exact (complexAngular_norm h).le

def principalAngularThirdPhase (hζ : IsPrimitiveRoot ζ 12) (η : EvenIdealRayCharacter K M)
    (P : ArtinMatthews.ProbePrime K) : ℂ :=
  star (cyclotomicAngularIdeal hζ P.asIdeal) ^ 6 * η.allCoefficient P.asIdeal ^ 6

theorem principalAngularThirdPhase_norm_le_one (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (P : ArtinMatthews.ProbePrime K) :
    ‖principalAngularThirdPhase hζ η P‖ ≤ 1 := by
  rw [principalAngularThirdPhase, norm_mul, norm_pow, norm_star, norm_pow]
  calc
    _ ≤ (1 : ℝ) ^ 6 * 1 ^ 6 := by
      gcongr
      · exact cyclotomicAngularIdeal_norm_le_one hζ P.asIdeal
      · exact η.allCoefficient_norm_le_one P.asIdeal
    _ = 1 := by norm_num

theorem principalAngular_value_norm (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    (S : Finset (ArtinMatthews.ProbePrime K)) (hS : principalAngularCutoff K M ⊆ S)
    (P : ArtinMatthews.ProbeGoodPrime K S) : ‖η.allCoefficient P.val.asIdeal‖ = 1 := by
  have hp : P.val ∉ principalAngularCutoff K M := fun h => P.property (hS h)
  have hc := principalAngularCutoff_coprime hM P.val hp
  simp only [EvenIdealRayCharacter.allCoefficient, dite_eq_left P.val.ne_bot, ite_eq_left hc]
  exact η.idealHom_norm _

theorem principalAngularThirdPhase_norm (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    (S : Finset (ArtinMatthews.ProbePrime K)) (hS : principalAngularCutoff K M ⊆ S)
    (P : ArtinMatthews.ProbeGoodPrime K S) : ‖principalAngularThirdPhase hζ η P.val‖ = 1 := by
  rw [principalAngularThirdPhase, norm_mul, norm_pow, norm_star, norm_pow,
    cyclotomicAngularIdeal_norm hζ P.val.asIdeal P.val.ne_bot
      (principalAngularCutoff_coprime_three P.val (fun h => P.property (hS h))),
    principalAngular_value_norm η hM S hS P, one_pow, mul_one]

def principalAngularCorrection (hζ : IsPrimitiveRoot ζ 12) (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) (s : ℂ) : ℂ :=
  ArtinMatthews.probeEulerProduct K S (fun _ => 1) (fun P => η.allCoefficient P.asIdeal)
    (principalAngularThirdPhase hζ η) (s, 1, 1 / 6)

theorem principalAngular_point_region {s : ℂ} (hs : 99799 / 100000 ≤ s.re) :
    (s, (1 : ℂ), (1 / 6 : ℂ)) ∈ ArtinMatthews.probeEulerDomain := by
  exact Or.inr ⟨hs, by norm_num, by norm_num⟩

theorem principalAngularCorrection_differentiableOn (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) :
    DifferentiableOn ℂ (principalAngularCorrection hζ η S)
      {s : ℂ | 99799 / 100000 < s.re} := by
  apply ArtinMatthews.probeEulerProduct_differentiableOn_path K S
    (probePrimeCutoff_subset_principalAngularCutoff.trans hS)
    (fun _ => 1) (fun P => η.allCoefficient P.asIdeal) (principalAngularThirdPhase hζ η)
    (by simp) (fun P => η.allCoefficient_norm_le_one P.asIdeal)
    (fun P => principalAngularThirdPhase_norm_le_one hζ η P)
    (isOpen_lt continuous_const Complex.continuous_re)
    differentiableOn_id (differentiableOn_const (c := (1 : ℂ)))
    (differentiableOn_const (c := (1 / 6 : ℂ)))
  intro s hs
  exact principalAngular_point_region hs.le

theorem principalAngularCorrection_analyticOnNhd (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) :
    AnalyticOnNhd ℂ (principalAngularCorrection hζ η S) {s : ℂ | 99799 / 100000 < s.re} :=
  (principalAngularCorrection_differentiableOn hζ η S hS).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem principalAngularCorrection_ne_zero (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 99799 / 100000 ≤ s.re) :
    principalAngularCorrection hζ η S s ≠ 0 :=
  ArtinMatthews.probeEulerProduct_ne_zero K S
    (probePrimeCutoff_subset_principalAngularCutoff.trans hS) _ _ _ (by simp)
    (fun P => η.allCoefficient_norm_le_one P.asIdeal)
    (fun P => principalAngularThirdPhase_norm_le_one hζ η P) (principalAngular_point_region hs)

theorem principalAngularCorrection_norm_le (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 99799 / 100000 ≤ s.re) :
    ‖principalAngularCorrection hζ η S s‖ ≤ probeGoodProductUniformBound K :=
  probeEulerProduct_norm_le_uniform K S (probePrimeCutoff_subset_principalAngularCutoff.trans hS)
    _ _ _ (by simp) (fun P => η.allCoefficient_norm_le_one P.asIdeal)
    (fun P => principalAngularThirdPhase_norm_le_one hζ η P) (principalAngular_point_region hs)

end
end ArtinMatthews.VaryingKummerAnalytic
