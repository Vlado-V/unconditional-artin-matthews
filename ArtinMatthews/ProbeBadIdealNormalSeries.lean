module

public import ArtinMatthews.ProbeIdealSourceWeight
public import ArtinMatthews.ProbeIdealCoefficientBounds
public import ArtinMatthews.ProbeBadPrimeHolomorphy


set_option backward.privateInPublic true
@[expose] public section

/-! The bad-prime geometric majorant for every actual ideal prime.
This uses the quotient/uniformizer finite Gauss sums and requires no
principal-generator presentation of the prime ideal. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probeBadIdealWeight_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ) (e k : Fin 2) (l m : ℕ) :
    ‖probeIdealSourceWeight K P χ j a b W V e l k.val m‖ ≤
      ((Ideal.absNorm P.asIdeal : ℝ) * ‖a‖) ^ e.val *
      ((Ideal.absNorm P.asIdeal : ℝ) ^ 3 * ‖b‖) ^ l *
      (Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) * ‖W‖) ^ k.val * ‖V‖ ^ m := by
  have hC : ‖probeIdealLocalCoefficient K P χ (e.val + 3 * l) k.val (j + 6 * m)‖ ≤
      (Ideal.absNorm P.asIdeal : ℝ) ^ (e.val + 3 * l) *
        Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) ^ k.val := by
    fin_cases k
    · simpa using probeIdealLocalCoefficient_zero_norm_le K P χ hχ _ (j + 6 * m)
    · simpa [mul_comm] using probeIdealLocalCoefficient_one_norm_le K P χ hχ hminus _ (j + 6 * m)
  simp only [probeIdealSourceWeight, norm_mul, norm_pow]
  calc
    _ ≤ ((Ideal.absNorm P.asIdeal : ℝ) ^ (e.val + 3 * l) *
        Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) ^ k.val) *
        ‖a‖ ^ e.val * ‖b‖ ^ l * ‖W‖ ^ k.val * ‖V‖ ^ m := by gcongr
    _ = _ := by simp only [pow_add, pow_mul, mul_pow]; ring

theorem probeBadIdealWeight_higher_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (hj : 0 < j)
    (a b W V : ℂ) (e : Fin 2) (l k m : ℕ) :
    probeIdealSourceWeight K P χ j a b W V e l (k + 2) m = 0 := by
  unfold probeIdealSourceWeight
  rw [probeIdealLocalCoefficient_bad_higher K P χ _ k _ (by omega)]
  simp

theorem probeBadIdealSourceTerm_norm_le_majorant (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ ξ w z : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re)
    (e : Fin 2) (i : ℕ × (ℕ × ℕ)) :
    ‖probeIdealSourceTerm K P χ j γ ν θ ξ w z e i.2.1 i.1 i.2.2‖ ≤
      probeBadPrimeMajorant (Ideal.absNorm P.asIdeal) i := by
  let Q : ℝ := Ideal.absNorm P.asIdeal
  let a := probeBadFirstParameter Q γ ν θ ξ
  let b := probeBadThetaParameter Q ν θ ξ
  let W := ArtinMatthews.probeLocalW Q θ w
  let V := ArtinMatthews.probeLocalV Q z
  have heq := probeIdealSourceWeight_eq_source K P χ j γ ν θ ξ w z e i.2.1 i.1 i.2.2
  change probeIdealSourceWeight K P χ j a b W V e i.2.1 i.1 i.2.2 = _ at heq
  rw [← heq]
  by_cases hk : i.1 < 2
  · let k : Fin 2 := ⟨i.1, hk⟩
    obtain ⟨hQ, _, _⟩ := ArtinMatthews.probeEulerCutoff_spec hcut
    have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
    obtain ⟨hw, hx, _, _, _⟩ := probeBadRegion_exponents hregion
    obtain ⟨hE, _, hT, _⟩ := probeBadParameters_real Q hQ0 γ ν θ ξ w z hγ hν hθ
    obtain ⟨hA, hV⟩ := probeBadParameters_small Q γ ν θ ξ w z hγ hν hθ hcut hregion
    have hE1 : probeBadE Q a ≤ 1 := by
      rw [hE]
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hQ hx
    have hTs : probeBadT Q W ≤ Real.sqrt Q := by
      rw [hT, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
    have hTk : (Real.sqrt Q) ^ k.val ≤ Q + 1 := by
      have hs := Real.sq_sqrt hQ0.le
      have hn := Real.sqrt_nonneg Q
      have hk01 : k.val = 0 ∨ k.val = 1 := by omega
      rcases hk01 with hk0 | hk1
      · rw [hk0, pow_zero]
        linarith
      · rw [hk1, pow_one]
        nlinarith
    have hE0 : 0 ≤ probeBadE Q a := by unfold probeBadE; positivity
    have hA0 : 0 ≤ probeBadA Q b := by unfold probeBadA; positivity
    have hT0 : 0 ≤ probeBadT Q W := by unfold probeBadT; positivity
    have H := probeBadIdealWeight_norm_le K P χ hχ hminus j a b W V e k i.2.1 i.2.2
    change _ ≤ probeBadE Q a ^ e.val * probeBadA Q b ^ i.2.1 *
      probeBadT Q W ^ k.val * ‖V‖ ^ i.2.2 at H
    calc
      _ ≤ probeBadE Q a ^ e.val * probeBadA Q b ^ i.2.1 *
          probeBadT Q W ^ k.val * ‖V‖ ^ i.2.2 := H
      _ ≤ 1 ^ e.val * (1 / 2 : ℝ) ^ i.2.1 * (Real.sqrt Q) ^ k.val *
          (1 / 2 : ℝ) ^ i.2.2 := by gcongr
      _ ≤ 1 ^ e.val * (1 / 2 : ℝ) ^ i.2.1 * (Q + 1) *
          (1 / 2 : ℝ) ^ i.2.2 := by gcongr
      _ = probeBadPrimeMajorant Q i := by
        simp only [probeBadPrimeMajorant, hk, ite_true, one_pow]
        ring
  · have hk2 : 2 ≤ i.1 := by omega
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk2
    have hz : probeIdealSourceWeight K P χ j a b W V e i.2.1 i.1 i.2.2 = 0 := by
      rw [hr, Nat.add_comm 2 r]
      exact probeBadIdealWeight_higher_zero K P χ j hj a b W V e i.2.1 r i.2.2
    rw [hz, norm_zero, probeBadPrimeMajorant, ite_eq_right hk]

theorem probeBadIdealSourceTerm_differentiable (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (γ ν θ : ℂ)
    (e : Fin 2) (i : ℕ × (ℕ × ℕ)) :
    Differentiable ℂ (fun q : ArtinMatthews.ProbeCoordinates =>
      probeIdealSourceTerm K P χ j γ ν θ q.1 q.2.1 q.2.2 e i.2.1 i.1 i.2.2) := by
  intro q
  have hQ : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  unfold probeIdealSourceTerm
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.const_cpow _ (Or.inl hQ)
  fun_prop

end
end ArtinMatthews.VaryingKummerAnalytic
