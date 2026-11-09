module

public import ArtinMatthews.ShiftedABLLevelBudget
public import ArtinMatthews.CubicThetaActualCuspFormConstructed


set_option backward.privateInPublic true
@[expose] public section

/-! Exact removal of the first-variable level-coprimality restriction in
Proposition 5.1. The only analytic input is its coprime coefficient test. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews
open OAI OAI.SevenEighths

def GiantSamplingCoprimeShiftedBilinearBound (N : ℕ) (η : HeckeFamily.Character)
    (Φ : ℝ → ℝ) (x ν Cν : ℝ) : Prop :=
  ∀ lo hi : ℝ, 1 ≤ lo → lo ≤ hi → ∀ (A B : Finset ℕ) (α β : ℕ → ℂ),
    (∀ a ∈ A, Squarefree a ∧ lo ≤ (a : ℝ) ∧ (a : ℝ) ≤ hi) →
    (∀ a ∈ A, a.Coprime N) →
    (∀ n ∈ B, 0 < n) →
    (∀ a ∈ A, ‖α a‖ ≤ 1) → (∀ n ∈ B, ‖β n‖ ≤ 1) →
    ‖giantCubicSamplingBilinear η Φ x A B α β‖ ≤
      Cν*x^ν*(x*lo^(-(1/2) : ℝ)+x^(7/8 : ℝ)*hi^(3/8 : ℝ))

theorem giantSamplingShiftedBilinearBound_of_coprime
    (N : ℕ) (hN : N ≠ 0) (η : HeckeFamily.Character) (Φ : ℝ → ℝ)
    {x ν C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hcoprime : GiantSamplingCoprimeShiftedBilinearBound N η Φ x ν C) :
    GiantSamplingShiftedBilinearBound η Φ x ν ((N : ℝ)^2*C) := by
  classical
  intro lo hi hlo hhi A B α β hA hB hα hβ
  have hlo0 : 0 ≤ lo := zero_le_one.trans hlo
  have hhi0 : 0 ≤ hi := hlo0.trans hhi
  let M := x*lo^(-(1/2) : ℝ)+x^(7/8 : ℝ)*hi^(3/8 : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hscale : 0 ≤ C*x^ν := mul_nonneg hC (Real.rpow_nonneg hx _)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hbound (d : ℕ) (hdN : d ∈ N.divisors) :
      ‖giantCubicSamplingBilinear η Φ x (shiftedABLLevelRow N A d)
        (shiftedABLLevelColumn B d) (shiftedABLLevelLeft α d) (shiftedABLLevelRight β d)‖ ≤
          (N : ℝ)*(C*x^ν*M) := by
    have hd := Nat.pos_of_mem_divisors hdN
    by_cases he : (shiftedABLLevelRow N A d).Nonempty
    · have hrow := fun (a : ℕ) (ha : a ∈ shiftedABLLevelRow N A d) =>
        shiftedABLLevelRow_interval hN hlo hA hd ha
      obtain ⟨a,ha⟩ := he
      have hlohi := (hrow a ha).2.2.1.trans (hrow a ha).2.2.2
      have hb := hcoprime (max 1 (lo/(d : ℝ))) (hi/(d : ℝ))
        (le_max_left _ _) hlohi (shiftedABLLevelRow N A d) (shiftedABLLevelColumn B d)
        (shiftedABLLevelLeft α d) (shiftedABLLevelRight β d)
        (fun a ha => ⟨(hrow a ha).1,(hrow a ha).2.2⟩)
        (fun a ha => (hrow a ha).2.1)
        (fun n hn => shiftedABLLevelColumn_source hd hB hn)
        (fun a ha => shiftedABLLevelRow_alpha_bound hα ha)
        (fun n hn => shiftedABLLevelColumn_beta_bound hd hβ hn)
      have hmain := shiftedABLLevel_main_bound hx hlo hhi hd (Nat.divisor_le hdN)
      calc
        _ ≤ C*x^ν*(x*(max 1 (lo/(d : ℝ)))^(-(1/2) : ℝ)+
          x^(7/8 : ℝ)*(hi/(d : ℝ))^(3/8 : ℝ)) := hb
        _ ≤ C*x^ν*((N : ℝ)*M) := mul_le_mul_of_nonneg_left hmain hscale
        _ = _ := by ring
    · have hempty : shiftedABLLevelRow N A d = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simp only [hempty,giantCubicSamplingBilinear,Finset.sum_empty,norm_zero]
      positivity
  rw [giantCubicSamplingBilinear_level_partition η Φ x N hN A B α β]
  calc
    _ ≤ ∑ d ∈ N.divisors, ‖giantCubicSamplingBilinear η Φ x (shiftedABLLevelRow N A d)
        (shiftedABLLevelColumn B d) (shiftedABLLevelLeft α d) (shiftedABLLevelRight β d)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ N.divisors, (N : ℝ)*(C*x^ν*M) := Finset.sum_le_sum hbound
    _ = (N.divisors.card : ℝ)*((N : ℝ)*(C*x^ν*M)) := by simp
    _ ≤ (N : ℝ)*((N : ℝ)*(C*x^ν*M)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.card_divisors_le_self N)) (by positivity)
    _ = ((N : ℝ)^2*C)*x^ν*M := by ring

theorem giantSamplingCubicShiftedBilinearBound_of_coprime
    (a : ℤ) (ha : a ≠ 0) (Φ : ℝ → ℝ) {x ν C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hcoprime : GiantSamplingCoprimeShiftedBilinearBound (cubicNumeratorThetaLevel a)
      (cubicNumeratorHeckeCharacter a ha) Φ x ν C) :
    GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter a ha) Φ x ν
      ((1944 : ℝ)^2*(a.natAbs : ℝ)^4*C) := by
  have h := giantSamplingShiftedBilinearBound_of_coprime (cubicNumeratorThetaLevel a)
    (cubicNumeratorThetaLevel_ne_zero ha) (cubicNumeratorHeckeCharacter a ha) Φ hx hC hcoprime
  have he : ((cubicNumeratorThetaLevel a : ℕ) : ℝ)^2*C =
      (1944 : ℝ)^2*(a.natAbs : ℝ)^4*C := by
    rw [cubicNumeratorThetaLevel_eq]
    push_cast
    ring
  rwa [he] at h

end ArtinMatthews
