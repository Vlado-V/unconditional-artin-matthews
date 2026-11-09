module

public import ArtinMatthews.GaussianCoordinateOneDim


set_option backward.privateInPublic true
@[expose] public section

/-! Generic finite Hilbert duality and Schur bounds, reused from the OpenAI
math snapshot OAI/NumberTheory/CubicMoment/Estimates/HuxleyDuality.lean
and HuxleySchur.lean. These statements have arbitrary finite index sets. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

lemma coordinate_finite_sieve_duality {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (A : ι → κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdual : ∀ b : ι → ℂ,
      (∑ n ∈ N, ‖∑ p ∈ P, b p*A p n‖^2) ≤ B*∑ p ∈ P, ‖b p‖^2)
    (v : κ → ℂ) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n*A p n‖^2) ≤ B*∑ n ∈ N, ‖v n‖^2 := by
  let F := fun p => ∑ n ∈ N, v n*A p n
  let S : ℝ := ∑ p ∈ P, ‖F p‖^2
  let T := fun n => ∑ p ∈ P, star (F p)*A p n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 ≤ ∑ n ∈ N, ‖v n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (S:ℂ) = ∑ n ∈ N, v n*T n := by
    calc
      (S:ℂ) = ∑ p ∈ P, F p*star (F p) := by
        simp only [S,Complex.ofReal_sum,Complex.ofReal_pow]
        apply Finset.sum_congr rfl
        intro p hp
        exact (Complex.mul_conj' (F p)).symm
      _ = ∑ p ∈ P, ∑ n ∈ N, v n*A p n*star (F p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_mul N (fun n => v n*A p n) (star (F p))
      _ = ∑ n ∈ N, v n*T n := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp only [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hnorm : S ≤ ∑ n ∈ N, ‖v n‖*‖T n‖ := by
    calc
      S = ‖(S:ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hS]
      _ ≤ _ := by
        rw [he]
        simpa only [norm_mul] using norm_sum_le N (fun n => v n*T n)
  have hc : S^2 ≤ (∑ n ∈ N, ‖v n‖^2)*(∑ n ∈ N, ‖T n‖^2) := by
    exact ((sq_le_sq₀ hS (Finset.sum_nonneg (fun _ _ => mul_nonneg
      (_root_.norm_nonneg _) (_root_.norm_nonneg _)))).mpr hnorm).trans
      (Finset.sum_mul_sq_le_sq_mul_sq N (fun n => ‖v n‖) (fun n => ‖T n‖))
  have hd : (∑ n ∈ N, ‖T n‖^2) ≤ B*S := by
    simpa only [T,S,norm_star] using hdual (fun p => star (F p))
  have hsquare : S*S ≤ (B*(∑ n ∈ N, ‖v n‖^2))*S := by
    calc
      S*S = S^2 := (pow_two _).symm
      _ ≤ _ := hc.trans (mul_le_mul_of_nonneg_left hd hE)
      _ = _ := by ring
  change S ≤ _
  by_cases hzero : S = 0
  · rw [hzero]
    exact mul_nonneg hB hE
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hS (Ne.symm hzero))).mp hsquare


lemma coordinate_finite_schur {ι : Type*} (P : Finset ι) (K : ι → ι → ℝ)
    (hK : ∀ i ∈ P, ∀ j ∈ P, 0 ≤ K i j)
    (hsym : ∀ i ∈ P, ∀ j ∈ P, K i j = K j i)
    {B : ℝ} (hrow : ∀ i ∈ P, ∑ j ∈ P, K i j ≤ B) (v : ι → ℂ) :
    (∑ i ∈ P, ∑ j ∈ P, ‖v i‖*‖v j‖*K i j) ≤ B*∑ i ∈ P, ‖v i‖^2 := by
  have hcol : (∑ i ∈ P, ∑ j ∈ P, ‖v j‖^2*K i j) =
      ∑ i ∈ P, ∑ j ∈ P, ‖v i‖^2*K i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have he : (∑ i ∈ P, ∑ j ∈ P, (‖v i‖^2+‖v j‖^2)*K i j) =
      2*∑ i ∈ P, ‖v i‖^2*(∑ j ∈ P, K i j) := by
    simp_rw [add_mul,Finset.sum_add_distrib]
    rw [hcol]
    simp_rw [← Finset.mul_sum]
    ring
  have hpair : 2*(∑ i ∈ P, ∑ j ∈ P, ‖v i‖*‖v j‖*K i j) ≤
      ∑ i ∈ P, ∑ j ∈ P, (‖v i‖^2+‖v j‖^2)*K i j := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hp : 2*‖v i‖*‖v j‖ ≤ ‖v i‖^2+‖v j‖^2 := by
      nlinarith [sq_nonneg (‖v i‖-‖v j‖)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (hK i hi j hj)
  have htotal : (∑ i ∈ P, ‖v i‖^2*(∑ j ∈ P, K i j)) ≤ B*∑ i ∈ P, ‖v i‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg ‖v i‖)
  rw [he] at hpair
  linarith

end
end ArtinMatthews
