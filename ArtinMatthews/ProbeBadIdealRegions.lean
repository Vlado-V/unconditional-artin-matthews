module

public import ArtinMatthews.ProbeBadIdealSeries
public import ArtinMatthews.ProbeBadIdealGaussHolomorphy


set_option backward.privateInPublic true
@[expose] public section

/-! The source-exact bad correction at every prime ideal satisfies
the same 1+O(Norm(P)^(-1/4000)) estimate as the prime-element model. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probeBadIdealOriginalSeries (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (a b W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' i : ℕ × (ℕ × ℕ),
    probeIdealSourceWeight K P χ j a b W V e i.2.1 i.1 i.2.2

theorem probeBadIdealOriginal_norm_summable (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm P.asIdeal) b < 1) (hV : ‖V‖ < 1)
    (e : Fin 2) :
    Summable (fun i : ℕ × (ℕ × ℕ) =>
      ‖probeIdealSourceWeight K P χ j a b W V e i.2.1 i.1 i.2.2‖) := by
  have hz (k : ℕ) (hk : k ∉ ({0, 1} : Finset ℕ)) (v : ℕ × ℕ) :
      probeIdealSourceWeight K P χ j a b W V e v.1 k v.2 = 0 := by
    have hk2 : 2 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk2
    simpa only [Nat.add_comm] using probeBadIdealWeight_higher_zero K P χ j hj a b W V e v.1 r v.2
  have hi (k : ℕ) : Summable (fun v : ℕ × ℕ =>
      ‖probeIdealSourceWeight K P χ j a b W V e v.1 k v.2‖) := by
    by_cases h0 : k = 0
    · subst k
      simpa only [probeBadIdealPair, Fin.val_zero, add_zero] using
        (probeBadIdealPair_summable K P χ hχ hminus j a b W V hA hV e 0 0).norm
    by_cases h1 : k = 1
    · subst k
      simpa only [probeBadIdealPair, Fin.val_one, add_zero] using
        (probeBadIdealPair_summable K P χ hχ hminus j a b W V hA hV e 1 0).norm
    · have hk : k ∉ ({0, 1} : Finset ℕ) := by simp [h0, h1]
      simpa only [hz k hk, norm_zero] using (summable_zero : Summable (fun _ : ℕ × ℕ => (0 : ℝ)))
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨hi, ?_⟩
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro k hk
  simp only [hz k hk, norm_zero, tsum_zero]

theorem probeBadIdealOriginalSeries_eq (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm P.asIdeal) b < 1) (hV : ‖V‖ < 1) :
    probeBadIdealOriginalSeries K P χ j a b W V =
      probeBadIdealLocalSeries K P χ j a b W V := by
  unfold probeBadIdealOriginalSeries probeBadIdealLocalSeries
  apply Finset.sum_congr rfl
  intro e _
  rw [(probeBadIdealOriginal_norm_summable K P χ hχ hminus j hj a b W V hA hV e).of_norm.tsum_prod]
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ)) (fun k hk => by
    have hk2 : 2 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk2
    simp only [show ∀ v : ℕ × ℕ,
      probeIdealSourceWeight K P χ j a b W V e v.1 (2 + r) v.2 = 0 from
      fun v => by simpa only [Nat.add_comm] using
        probeBadIdealWeight_higher_zero K P χ j hj a b W V e v.1 r v.2, tsum_zero])]
  simp only [Fin.sum_univ_two, Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, Nat.zero_ne_one, not_false_eq_true, Fin.val_zero, Fin.val_one,
    probeBadIdealPair, add_zero]
theorem probeBadIdealCorrection_regions (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ ξ w z : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    ‖probeBadIdealCorrection K P χ j
      (probeBadFirstParameter (Ideal.absNorm P.asIdeal) γ ν θ ξ)
      (probeBadThetaParameter (Ideal.absNorm P.asIdeal) ν θ ξ)
      (ArtinMatthews.probeLocalW (Ideal.absNorm P.asIdeal) θ w)
      (ArtinMatthews.probeLocalV (Ideal.absNorm P.asIdeal) z) - 1‖ ≤
        36 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-(1 / 4000 : ℝ)) := by
  let Q : ℝ := Ideal.absNorm P.asIdeal
  obtain ⟨hQ, hsmall, _⟩ := ArtinMatthews.probeEulerCutoff_spec hcut
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  obtain ⟨hw, hx, hAexp, hETexp, hz⟩ := probeBadRegion_exponents hregion
  obtain ⟨hE, hA, hT, hV⟩ := probeBadParameters_real Q hQ0 γ ν θ ξ w z hγ hν hθ
  have hAA : Q ^ (2 - 3 * ξ.re) ≤ Q ^ (-(99 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ hAexp
  have hAh : Q ^ (2 - 3 * ξ.re) ≤ 1 / 2 := hAA.trans
    ((Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)).trans hsmall)
  have hVh : Q ^ (-(6 * z.re)) ≤ 1 / 2 :=
    (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)).trans hsmall
  have hEE : Q ^ (1 / 2 - ξ.re) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hQ hx
  have hTT : Q ^ (1 / 2 - w.re) ≤ Q ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  have hET : Q ^ (1 / 2 - ξ.re) * Q ^ (1 / 2 - w.re) ≤ Q ^ (-(1 / 4000 : ℝ)) := by
    rw [← Real.rpow_add hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ
    linarith
  have hhalf : 1 ≤ Q ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hprod : (1 + Q ^ (1 / 2 - ξ.re)) * (1 + Q ^ (1 / 2 - w.re)) *
      Q ^ (2 - 3 * ξ.re) ≤ 4 * Q ^ (-(49 / 100 : ℝ)) := by
    calc
      _ ≤ (1 + 1) * (2 * Q ^ (1 / 2 : ℝ)) * Q ^ (-(99 / 100 : ℝ)) := by
        gcongr
        linarith
      _ = _ := by
        rw [mul_assoc, mul_assoc, ← Real.rpow_add hQ0]
        norm_num
        ring
  have hlast : Q ^ (-(49 / 100 : ℝ)) ≤ Q ^ (-(1 / 4000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
  have H := probeBadIdealCorrection_norm_sub_one_le K P χ hχ hminus j hj
    (probeBadFirstParameter Q γ ν θ ξ) (probeBadThetaParameter Q ν θ ξ)
    (ArtinMatthews.probeLocalW Q θ w) (ArtinMatthews.probeLocalV Q z)
    (by rwa [hA]) (by rwa [hV])
  rw [hE, hA, hT] at H
  change _ ≤ 36 * Q ^ (-(1 / 4000 : ℝ))
  nlinarith

theorem probeBadIdealSourceSeries_eq_original (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (γ ν θ ξ w z : ℂ) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    probeIdealSourceSeries K P χ j γ ν θ ξ w z =
      probeBadIdealOriginalSeries K P χ j (probeBadFirstParameter Q γ ν θ ξ)
        (probeBadThetaParameter Q ν θ ξ) (ArtinMatthews.probeLocalW Q θ w)
        (ArtinMatthews.probeLocalV Q z) := by
  simp only [probeIdealSourceSeries, probeBadIdealOriginalSeries, probeIdealSourceWeight_eq_source]

theorem probeBadIdealSourceCorrection_regions (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal)
    (q : ArtinMatthews.ProbeCoordinates) (hregion : q ∈ ArtinMatthews.probeEulerDomain) :
    ‖probeBadIdealSourceCorrection K P χ j γ ν θ q - 1‖ ≤
      36 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-(1 / 4000 : ℝ)) := by
  obtain ⟨hA, hV⟩ := probeBadParameters_small (Ideal.absNorm P.asIdeal)
    γ ν θ q.1 q.2.1 q.2.2 hγ hν hθ hcut hregion
  unfold probeBadIdealSourceCorrection
  rw [probeBadIdealSourceSeries_eq_original,
    probeBadIdealOriginalSeries_eq K P χ hχ hminus j hj _ _ _ _ (by linarith) (by linarith)]
  exact probeBadIdealCorrection_regions K P χ hχ hminus j hj γ ν θ q.1 q.2.1 q.2.2
    hγ hν hθ hcut hregion

end
end ArtinMatthews.VaryingKummerAnalytic
