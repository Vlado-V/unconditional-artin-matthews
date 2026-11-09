module

public import ArtinMatthews.GaussianCoordinateKernel
public import ArtinMatthews.GaussianCoordinateSchur


set_option backward.privateInPublic true
@[expose] public section

/-! Exact arbitrary-dimensional Gaussian energy identity. The finite Schur
argument is the generic part of the OpenAI HuxleyGaussianEnergy proof. -/
namespace ArtinMatthews
noncomputable section
open Finset
variable {β ι : Type*} [Fintype β]

def coordinateDualPolynomial (P : Finset ι) (x : ι → β → ℝ) (v : ι → ℂ) (n : β → ℤ) : ℂ :=
  ∑ p ∈ P, v p*coordinatePhase (x p) n

theorem coordinateGaussianEnergy_expansion (a : ℝ) (P : Finset ι)
    (x : ι → β → ℝ) (v : ι → ℂ) (n : β → ℤ) :
    ((coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2:ℝ):ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, (v p*star (v q))*
        ((coordinateGaussianWeight a n:ℂ)*coordinatePhase (x p-x q) n) := by
  rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
  unfold coordinateDualPolynomial
  simp only [map_sum,map_mul,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [coordinatePhase_sub]
  simp only [starRingEnd_apply]
  ring

theorem coordinateGaussianEnergy_summable {a : ℝ} (ha : 0 < a) (P : Finset ι)
    (x : ι → β → ℝ) (v : ι → ℂ) :
    Summable (fun n : β → ℤ => coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2) := by
  have hs : Summable (fun n : β → ℤ => ∑ p ∈ P, ∑ q ∈ P,
      (v p*star (v q))*((coordinateGaussianWeight a n:ℂ)*coordinatePhase (x p-x q) n)) :=
    summable_sum (fun p _ => summable_sum (fun q _ =>
      (coordinate_weighted_phase_summable ha _).mul_left _))
  convert (Complex.hasSum_re hs.hasSum).summable using 1
  ext n
  rw [← coordinateGaussianEnergy_expansion]
  rfl

theorem coordinateGaussianEnergy_sum {a : ℝ} (ha : 0 < a) (P : Finset ι)
    (x : ι → β → ℝ) (v : ι → ℂ) :
    Complex.ofReal (∑' n : β → ℤ, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2) =
      ∑ p ∈ P, ∑ q ∈ P, (v p*star (v q))*coordinateGaussianKernel a (x p-x q) := by
  rw [Complex.ofReal_tsum]
  simp_rw [coordinateGaussianEnergy_expansion]
  rw [Summable.tsum_finsetSum (fun p _ => summable_sum (fun q _ =>
    (coordinate_weighted_phase_summable ha _).mul_left _))]
  apply sum_congr rfl
  intro p _
  rw [Summable.tsum_finsetSum (fun q _ => (coordinate_weighted_phase_summable ha _).mul_left _)]
  apply sum_congr rfl
  intro q _
  rw [tsum_mul_left]
  rfl

/-- The actual Gaussian energy inherits a genuine symmetric kernel-row bound. -/
theorem coordinateGaussianEnergy_schur {a : ℝ} (ha : 0 < a) (P : Finset ι)
    (x : ι → β → ℝ) (K : ι → ι → ℝ) {B : ℝ}
    (hK : ∀ i ∈ P, ∀ j ∈ P, 0 ≤ K i j)
    (hsym : ∀ i ∈ P, ∀ j ∈ P, K i j=K j i)
    (hkernel : ∀ i ∈ P, ∀ j ∈ P, ‖coordinateGaussianKernel a (x i-x j)‖ ≤ K i j)
    (hrow : ∀ i ∈ P, ∑ j ∈ P, K i j ≤ B) (v : ι → ℂ) :
    (∑' n : β → ℤ, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2) ≤
      B*∑ p ∈ P, ‖v p‖^2 := by
  have hnonneg : 0 ≤ ∑' n : β → ℤ, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2 :=
    tsum_nonneg (fun n => mul_nonneg (coordinateGaussianWeight_nonneg _ _) (sq_nonneg _))
  calc
    _ = ‖Complex.ofReal (∑' n : β → ℤ, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ‖v p‖*‖v q‖*‖coordinateGaussianKernel a (x p-x q)‖ := by
      rw [coordinateGaussianEnergy_sum ha]
      apply (norm_sum_le P _).trans
      apply sum_le_sum
      intro p _
      simpa only [norm_mul,norm_star] using norm_sum_le P
        (fun q => (v p*star (v q))*coordinateGaussianKernel a (x p-x q))
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ‖v p‖*‖v q‖*K p q := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hkernel p hp q hq) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := coordinate_finite_schur P K hK hsym hrow v

end
end ArtinMatthews
