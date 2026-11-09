module

public import ArtinMatthews.GaussianCoordinateRows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Finset VaryingKummerAnalytic
noncomputable section
variable {β ι : Type*} [Fintype β]

def coordinateAdditiveSieveBound (β : Type*) [Fintype β] (Q a R : ℝ) : ℝ :=
  Real.exp (Real.pi*a*R)*((1/Real.sqrt a)^(Fintype.card β)*
    (coordinateGaussianConstant β*(1+Q/Real.sqrt (Real.pi/a))^(Fintype.card β)))

theorem coordinate_gaussian_majorant {a R : ℝ} (ha : 0 < a) (n : β → ℤ)
    (hn : (∑ i, (n i:ℝ)^2) ≤ R) :
    1 ≤ Real.exp (Real.pi*a*R)*coordinateGaussianWeight a n := by
  unfold coordinateGaussianWeight
  rw [← Real.exp_add]
  apply Real.one_le_exp_iff.mpr
  have h := mul_le_mul_of_nonneg_left hn (mul_pos Real.pi_pos ha).le
  linarith

theorem coordinateAdditiveSieveBound_nonneg {Q a R : ℝ} (hQ : 0 < Q) (ha : 0 < a) :
    0 ≤ coordinateAdditiveSieveBound β Q a R := by
  have hC := coordinateGaussianConstant_pos (β := β)
  unfold coordinateAdditiveSieveBound
  positivity

/-- Dual finite additive large sieve with actual coordinate Gaussian and
actual separated lifts. No row or operator estimate is supplied as a hypothesis. -/
theorem coordinate_finite_dual_sieve {Q a R : ℝ} (hQ : 0 < Q) (ha : 0 < a)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ u v : {i // i ∈ P} × (β → ℤ), u ≠ v →
      1/Q ≤ ‖coordinateGaussianLift x (u.1.val,u.2)-coordinateGaussianLift x (v.1.val,v.2)‖)
    (N : Finset (β → ℤ)) (hN : ∀ n ∈ N, (∑ b, (n b:ℝ)^2) ≤ R) (v : ι → ℂ) :
    (∑ n ∈ N, ‖∑ p ∈ P, v p*coordinatePhase (x p) n‖^2) ≤
      coordinateAdditiveSieveBound β Q a R*∑ p ∈ P, ‖v p‖^2 := by
  have hs := coordinateGaussianEnergy_summable ha P x v
  have hweight : (∑ n ∈ N, ‖coordinateDualPolynomial P x v n‖^2) ≤
      Real.exp (Real.pi*a*R)*∑ n ∈ N, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have h := mul_le_mul_of_nonneg_right (coordinate_gaussian_majorant ha n (hN n hn))
      (sq_nonneg ‖coordinateDualPolynomial P x v n‖)
    simpa only [one_mul,mul_assoc] using h
  have hfinite : (∑ n ∈ N, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2) ≤
      ∑' n, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2 :=
    hs.sum_le_tsum N (fun n _ => mul_nonneg (coordinateGaussianWeight_nonneg _ _) (sq_nonneg _))
  calc
    _ ≤ Real.exp (Real.pi*a*R)*(∑' n, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2) :=
      hweight.trans (mul_le_mul_of_nonneg_left hfinite (Real.exp_pos _).le)
    _ ≤ Real.exp (Real.pi*a*R)*(((1/Real.sqrt a)^(Fintype.card β)*
        (coordinateGaussianConstant β*(1+Q/Real.sqrt (Real.pi/a))^(Fintype.card β)))*∑ p ∈ P, ‖v p‖^2) :=
      mul_le_mul_of_nonneg_left (coordinateGaussianEnergy_bound hQ ha P x hsep v) (Real.exp_pos _).le
    _ = _ := by unfold coordinateAdditiveSieveBound; ring

/-- The primal finite additive large sieve, retaining the exact coordinate phase. -/
theorem coordinate_finite_primal_sieve {Q a R : ℝ} (hQ : 0 < Q) (ha : 0 < a)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ u v : {i // i ∈ P} × (β → ℤ), u ≠ v →
      1/Q ≤ ‖coordinateGaussianLift x (u.1.val,u.2)-coordinateGaussianLift x (v.1.val,v.2)‖)
    (N : Finset (β → ℤ)) (hN : ∀ n ∈ N, (∑ b, (n b:ℝ)^2) ≤ R) (v : (β → ℤ) → ℂ) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n*coordinatePhase (x p) n‖^2) ≤
      coordinateAdditiveSieveBound β Q a R*∑ n ∈ N, ‖v n‖^2 :=
  coordinate_finite_sieve_duality P N (fun p n => coordinatePhase (x p) n)
    (coordinateAdditiveSieveBound_nonneg hQ ha)
    (coordinate_finite_dual_sieve hQ ha P x hsep N hN) v

end
end ArtinMatthews
