module

public import ArtinMatthews.ShiftedBilinearGlobal
public import ArtinMatthews.ShiftedRawDyadicEstimate


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set OAI.SevenEighths
open scoped ContDiff
noncomputable section

theorem giantSamplingCoprimeShiftedBilinearBound_of_correlation
    (N : ℕ) (η : HeckeFamily.Character)
    (hreal : ∀ n, star (idealThetaCoeff η n) = idealThetaCoeff η n)
    (hsource : ShiftedABLCorrelationSource N η)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingCoprimeShiftedBilinearBound N η Φ x ν Cν :=
  giantSamplingCoprimeShiftedBilinearBound_of_dyadic N η Φ hΦ hsupp
    (shiftedRawDyadicBound_of_correlation N η hreal hsource)

theorem giantSamplingShiftedBilinearBound_of_correlation
    (N : ℕ) (hN : N ≠ 0) (η : HeckeFamily.Character)
    (hreal : ∀ n, star (idealThetaCoeff η n) = idealThetaCoeff η n)
    (hsource : ShiftedABLCorrelationSource N η)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingShiftedBilinearBound η Φ x ν Cν := by
  intro ν hν
  obtain ⟨C, hC, hbound⟩ := giantSamplingCoprimeShiftedBilinearBound_of_correlation
    N η hreal hsource Φ hΦ hsupp ν hν
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine ⟨(N : ℝ) ^ 2 * C, mul_pos (sq_pos_of_pos hN0) hC, ?_⟩
  intro x hx
  exact giantSamplingShiftedBilinearBound_of_coprime N hN η Φ
    (zero_le_one.trans hx) hC.le (hbound x hx)

theorem cubicNumerator_shiftedBilinearBound_of_correlation
    (a : ℤ) (ha : a ≠ 0)
    (hsource : ShiftedABLCorrelationSource (cubicNumeratorThetaLevel a)
      (cubicNumeratorHeckeCharacter a ha))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter a ha) Φ x ν Cν :=
  giantSamplingShiftedBilinearBound_of_correlation (cubicNumeratorThetaLevel a)
    (cubicNumeratorThetaLevel_ne_zero ha) (cubicNumeratorHeckeCharacter a ha)
    (cubicNumeratorThetaCoeff_conjugate a ha) hsource Φ hΦ hsupp

end
end ArtinMatthews
