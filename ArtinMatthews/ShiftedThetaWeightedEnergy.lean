module

public import ArtinMatthews.ShiftedThetaFiniteEnergy
public import ArtinMatthews.ShiftedThetaEnergyArithmetic


set_option backward.privateInPublic true
@[expose] public section

/-! The weighted finite energy estimate uses the actual off-diagonal
correlation bound and the established arithmetic sums. -/
namespace ArtinMatthews
open Set Complex
open scoped BigOperators ComplexConjugate
noncomputable section

theorem shiftedTheta_weighted_energy_bound (δ : ℝ) (hδ : 0 < δ) (hsmall : δ < 1/2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (M : ℕ) (T : ℝ) (A : Finset ℕ),
        0 < M → 1 ≤ T → A ⊆ Finset.Icc M (2*M) →
        ∀ (α : ℕ → ℂ), (∀ m ∈ A, ‖α m‖ ≤ 1) →
        ∀ (g : ℝ → ℝ), (∀ x, 0 ≤ g x) → Function.support g ⊆ Icc T (2*T) →
        ∀ G : ℝ, (∀ x, |g x| ≤ G) → ∀ ν C : ℝ, 0 ≤ C →
        (∀ n, star (idealThetaCoeff χ n) = idealThetaCoeff χ n) →
        (∀ m1 ∈ A, ∀ m2 ∈ A, m1 ≠ m2 →
          ‖thetaShiftedCorrelation χ m1 m2 (fun x => (g x : ℂ))‖ ≤
            C * ((M : ℝ)*T)^ν *
              (Real.sqrt ((M : ℝ)*T+1) * Real.sqrt M * (shiftedCommonPrimePart m1 m2 : ℝ) /
                  Real.sqrt (m1.gcd m2) +
                ((M : ℝ)*T+1)^(3/4 : ℝ) * (shiftedCommonPrimePart m1 m2 : ℝ)^(1/4 : ℝ) /
                  (M : ℝ)^(1/4 : ℝ))) →
        (∑ n ∈ Finset.Icc 1 ⌈2*T⌉₊,
          g n * ‖∑ m ∈ A, α m * idealThetaCoeff χ (m*n+1)‖^2) ≤
          G*K*(6*(M : ℝ)*T+1)^(1+δ) +
            C*K*((M : ℝ)*T)^ν*(2*(M : ℝ))^(2+δ) *
              (Real.sqrt ((M : ℝ)*T+1)*Real.sqrt M +
                ((M : ℝ)*T+1)^(3/4 : ℝ)/(M : ℝ)^(1/4 : ℝ)) := by
  obtain ⟨K,hK,hdiag,hfirst,hsecond⟩ := shiftedTheta_energy_arithmetic δ hδ hsmall
  refine ⟨K,hK,?_⟩
  intro χ M T A hM hT hA α hα g hg hs G hG ν C hC hreal hcorr
  have hG0 : 0 ≤ G := (abs_nonneg (g 0)).trans (hG 0)
  have hT0 : 0 ≤ T := (by norm_num : (0 : ℝ) ≤ 1).trans hT
  have hdiagW :
      (∑ m ∈ A, ∑ n ∈ Finset.Icc 1 ⌈2*T⌉₊,
        g n * ‖idealThetaCoeff χ (m*n+1)‖^2) ≤ G*K*(6*(M : ℝ)*T+1)^(1+δ) := by
    calc
      _ ≤ G * ∑ m ∈ A, ∑ n ∈ Finset.Icc 1 ⌈2*T⌉₊,
          ‖idealThetaCoeff χ (m*n+1)‖^2 := by
        simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro m _
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_right ((le_abs_self (g n)).trans (hG n)) (sq_nonneg _)
      _ ≤ G * (K*(6*(M : ℝ)*T+1)^(1+δ)) :=
        mul_le_mul_of_nonneg_left (hdiag χ M T A hM hT hA) hG0
      _ = _ := by ring
  let a := Real.sqrt ((M : ℝ)*T+1)*Real.sqrt M
  let b := ((M : ℝ)*T+1)^(3/4 : ℝ)/(M : ℝ)^(1/4 : ℝ)
  let P := C*((M : ℝ)*T)^ν
  have ha : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb : 0 ≤ b := div_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have hP : 0 ≤ P := mul_nonneg hC (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg M) hT0) _)
  have hcorr' (p : ℕ × ℕ) (hp : p ∈ A.offDiag) :
      ‖thetaShiftedCorrelation χ p.1 p.2 (fun x => (g x : ℂ))‖ ≤
        P * (a * ((shiftedCommonPrimePart p.1 p.2 : ℝ) / Real.sqrt (p.1.gcd p.2)) +
          b * (shiftedCommonPrimePart p.1 p.2 : ℝ)^(1/4 : ℝ)) := by
    rcases Finset.mem_offDiag.mp hp with ⟨h1,h2,hne⟩
    exact (hcorr p.1 h1 p.2 h2 hne).trans_eq (by dsimp only [P,a,b]; ring)
  have hoff :
      (∑ p ∈ A.offDiag, ‖thetaShiftedCorrelation χ p.1 p.2 (fun x => (g x : ℂ))‖) ≤
        C*K*((M : ℝ)*T)^ν*(2*(M : ℝ))^(2+δ)*(a+b) := by
    calc
      _ ≤ ∑ p ∈ A.offDiag, P *
          (a * ((shiftedCommonPrimePart p.1 p.2 : ℝ) / Real.sqrt (p.1.gcd p.2)) +
            b * (shiftedCommonPrimePart p.1 p.2 : ℝ)^(1/4 : ℝ)) :=
        Finset.sum_le_sum hcorr'
      _ = P *
          (a * (∑ p ∈ A.offDiag, (shiftedCommonPrimePart p.1 p.2 : ℝ) / Real.sqrt (p.1.gcd p.2)) +
            b * (∑ p ∈ A.offDiag, (shiftedCommonPrimePart p.1 p.2 : ℝ)^(1/4 : ℝ))) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
      _ ≤ P * (a * (K*(2*(M : ℝ))^(2+δ)) + b * (K*(2*(M : ℝ))^(2+δ))) := by
        apply mul_le_mul_of_nonneg_left _ hP
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hfirst M A hM hA) ha)
          (mul_le_mul_of_nonneg_left (hsecond M A hM hA) hb)
      _ = _ := by dsimp only [P]; ring
  exact (shiftedTheta_weighted_energy_split χ hreal A α hα hT g hg hs).trans
    (add_le_add hdiagW hoff)

end
end ArtinMatthews
