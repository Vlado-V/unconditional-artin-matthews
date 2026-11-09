module

public import ArtinMatthews.IdealFiniteFrame


set_option backward.privateInPublic true
@[expose] public section

/-! Finite weighted Cauchy--Schwarz on numeric fibers, retaining arbitrary
functions of the complete ordered tuple. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

def idealFiberMass (μ : Ω → ℝ) (p : Ω → ℕ) (n : ℕ) : ℝ :=
  ∑ a, if p a = n then μ a else 0

def idealFiberCoefficient (μ : Ω → ℝ) (p : Ω → ℕ) (f : Ω → ℂ) (n : ℕ) : ℂ :=
  ∑ a, if p a = n then (μ a : ℂ) * f a else 0

theorem idealFiberCoefficient_sq_le (μ : Ω → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (p : Ω → ℕ) (f : Ω → ℂ) (n : ℕ) :
    ‖idealFiberCoefficient μ p f n‖^2 ≤ idealFiberMass μ p n *
      ∑ a, if p a = n then μ a * ‖f a‖^2 else 0 := by
  let w : Ω → ℝ := fun a => if p a = n then μ a else 0
  have hw (a : Ω) : 0 ≤ w a := by
    dsimp [w]
    split_ifs
    · exact hμ a
    · exact le_rfl
  have hc := idealFrame_weighted_cauchy w hw (fun _ => 1) f
  simp only [star_one, mul_one, idealFrameEnergy, norm_one, one_pow] at hc
  have hwcast (a : Ω) : (w a : ℂ) * f a = if p a = n then (μ a : ℂ)*f a else 0 := by
    dsimp [w]
    split_ifs
    · rfl
    · rw [Complex.ofReal_zero, zero_mul]
  simp_rw [hwcast] at hc
  simpa only [idealFiberCoefficient, idealFiberMass, w, ite_mul, zero_mul] using hc

theorem idealFiberCoefficient_energy_le (μ : Ω → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (p : Ω → ℕ) (f : Ω → ℂ) (S : Finset ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hatom : ∀ n ∈ S, idealFiberMass μ p n ≤ R) :
    (∑ n ∈ S, ‖idealFiberCoefficient μ p f n‖^2) ≤ R * idealFrameEnergy μ f := by
  calc
    _ ≤ ∑ n ∈ S, R * ∑ a, if p a = n then μ a * ‖f a‖^2 else 0 := by
      apply sum_le_sum
      intro n hn
      exact (idealFiberCoefficient_sq_le μ hμ p f n).trans
        (mul_le_mul_of_nonneg_right (hatom n hn) (sum_nonneg fun a _ => by
          split_ifs
          · exact mul_nonneg (hμ a) (sq_nonneg _)
          · exact le_rfl))
    _ = R * ∑ a, ∑ n ∈ S, if p a = n then μ a * ‖f a‖^2 else 0 := by
      rw [← mul_sum, sum_comm]
    _ ≤ R * idealFrameEnergy μ f := by
      apply mul_le_mul_of_nonneg_left _ hR
      unfold idealFrameEnergy
      apply sum_le_sum
      intro a _
      simp only [sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hμ a) (sq_nonneg _)

end
end ArtinMatthews
