module

public import ArtinMatthews.ShiftedDyadicEnergyScale
public import ArtinMatthews.ShiftedBilinearMajorant
public import ArtinMatthews.ShiftedThetaWeightedEnergy
public import ArtinMatthews.ShiftedABLCorrelationTarget


set_option backward.privateInPublic true
@[expose] public section

/-! Apply the literal correlation estimate to each fixed smooth bump. -/
namespace ArtinMatthews
open Set OAI.SevenEighths
open scoped BigOperators ContDiff
noncomputable section

theorem shiftedDyadic_scaledBump_energy_bound (N : ℕ) (η : HeckeFamily.Character)
    (hreal : ∀ n, star (idealThetaCoeff η n) = idealThetaCoeff η n)
    (hsource : ShiftedABLCorrelationSource N η)
    (ε : ℝ) (hε : 0 < ε) (hsmall : ε < 1 / 2) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (M : ℕ), 0 < M → ∀ (T S : ℝ), 1 ≤ T → 1 ≤ S → S ≤ 2 * T →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc M (2 * M) →
      (∀ m ∈ A, Squarefree m) → (∀ m ∈ A, N.Coprime m) →
      ∀ α : ℕ → ℂ, (∀ m ∈ A, ‖α m‖ ≤ 1) →
      (∑ n ∈ Finset.Icc 1 ⌈2 * S⌉₊, (shiftedBilinearScaledBump S n).re *
        ‖∑ m ∈ A, α m * idealThetaCoeff η (m * n + 1)‖ ^ 2) ≤
        C0 * ((M : ℝ) * T) ^ (2 * ε) *
          ((M : ℝ) * T + (M : ℝ) ^ 3 * T ^ (1 / 2 : ℝ) +
            (M : ℝ) ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) := by
  obtain ⟨Cg, hCg, hbump⟩ := shiftedBilinearScaledBump_source_data
  obtain ⟨C, hC, hcorr⟩ := hsource ε hε Cg hCg
  obtain ⟨K, hK, henergy⟩ := shiftedTheta_weighted_energy_bound ε hε hsmall
  refine ⟨169 * K + 64 * C * K, by positivity, ?_⟩
  intro M hM T S hT hS hST A hA hSF hN α hα
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M from hM)
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  obtain ⟨hsm, hsupport, hderiv⟩ := hbump S hSp
  have hcast : (fun x : ℝ => ((shiftedBilinearScaledBump S x).re : ℂ)) =
      shiftedBilinearScaledBump S := by
    funext x
    exact shiftedBilinearScaledBump_ofReal_re S x
  have hc (m1 : ℕ) (hm1 : m1 ∈ A) (m2 : ℕ) (hm2 : m2 ∈ A) (hne : m1 ≠ m2) :
      ‖thetaShiftedCorrelation η m1 m2 (fun x => ((shiftedBilinearScaledBump S x).re : ℂ))‖ ≤
        C * ((M : ℝ) * S) ^ ε *
          (Real.sqrt ((M : ℝ) * S + 1) * Real.sqrt M * (shiftedCommonPrimePart m1 m2 : ℝ) /
              Real.sqrt (m1.gcd m2) +
            ((M : ℝ) * S + 1) ^ (3 / 4 : ℝ) * (shiftedCommonPrimePart m1 m2 : ℝ) ^ (1 / 4 : ℝ) /
              (M : ℝ) ^ (1 / 4 : ℝ)) := by
    rw [hcast]
    have hm1' := Finset.mem_Icc.mp (hA hm1)
    have hm2' := Finset.mem_Icc.mp (hA hm2)
    exact hcorr m1 m2 hne (hSF m1 hm1) (hSF m2 hm2) ((hN m1 hm1).mul_right (hN m2 hm2))
      M S hMreal hS (by exact_mod_cast hm1'.1) (by exact_mod_cast hm1'.2)
      (by exact_mod_cast hm2'.1) (by exact_mod_cast hm2'.2) _ hsm hsupport hderiv
  have hG (x : ℝ) : |(shiftedBilinearScaledBump S x).re| ≤ 1 := by
    rw [abs_of_nonneg (shiftedBilinearScaledBump_re_bounds S x).1]
    exact (shiftedBilinearScaledBump_re_bounds S x).2
  have he := henergy η M S A hM hS hA α hα (fun x => (shiftedBilinearScaledBump S x).re)
    (fun x => (shiftedBilinearScaledBump_re_bounds S x).1)
    (shiftedBilinearScaledBump_re_support S hSp) 1 hG ε C hC.le hreal hc
  simp only [one_mul] at he
  exact he.trans (shiftedDyadic_energyScale M T S ε C K hMreal hT hS hST hε.le hsmall.le hC.le hK.le)

end
end ArtinMatthews
