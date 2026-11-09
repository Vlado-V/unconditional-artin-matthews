module

public import ArtinMatthews.VaryingKummerAnalyticCoordinatePacking
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Real.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Gaussian mass of a separated family in arbitrary finite-dimensional
coordinate space. The actual grid count is proved in CoordinatePacking.
This generalizes the Gaussian-bin argument of the pinned Huxley source. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped BigOperators
noncomputable section
variable {β ι : Type*} [Fintype β]

theorem coordinate_gaussian_weight_summable (n : ℕ) :
    Summable (fun k : ℕ => ((k:ℝ)+1)^n * Real.exp (-(k:ℝ))) := by
  have h := (Real.summable_pow_mul_exp_neg_nat_mul n (show (0:ℝ)<1 by norm_num)).comp_injective
    Nat.succ_injective
  have hm := h.mul_left (Real.exp 1)
  convert hm using 1
  ext k
  simp only [Function.comp_apply,Nat.cast_succ,neg_one_mul]
  rw [← mul_assoc,mul_comm (Real.exp 1),mul_assoc,← Real.exp_add]
  congr 2
  ring

def coordinateGaussianConstant (β : Type*) [Fintype β] : ℝ :=
  7^(Fintype.card β) * ∑' k : ℕ,
    ((k:ℝ)+1)^(Fintype.card β) * Real.exp (-(k:ℝ))

theorem coordinateGaussianConstant_pos : 0 < coordinateGaussianConstant β := by
  unfold coordinateGaussianConstant
  apply mul_pos (by positivity)
  have h := (coordinate_gaussian_weight_summable (Fintype.card β)).le_tsum 0
    (fun _ _ => by positivity)
  norm_num at h
  linarith

theorem coordinate_gaussian_bin_bound {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (z : β → ℝ) (S : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1/Q ≤ ‖x i-x j‖) (k : ℕ) :
    (∑ i ∈ S with ⌊t*‖x i-z‖^2⌋₊ = k,
      Real.exp (-t*‖x i-z‖^2)) ≤
      (7*(1+Q/Real.sqrt t))^(Fintype.card β) *
        (((k:ℝ)+1)^(Fintype.card β) * Real.exp (-(k:ℝ))) := by
  classical
  let U := S.filter (fun i => ⌊t*‖x i-z‖^2⌋₊ = k)
  let R := Real.sqrt (((k:ℝ)+1)/t)
  have hnum : 0 ≤ ((k:ℝ)+1)/t := by positivity
  have hball : ∀ i ∈ U, ‖x i-z‖ ≤ R := by
    intro i hi
    have hk := (Finset.mem_filter.mp hi).2
    have hlt := Nat.lt_floor_add_one (t*‖x i-z‖^2)
    rw [hk] at hlt
    apply (Real.le_sqrt (norm_nonneg _) hnum).mpr
    exact (le_div_iff₀ ht).mpr (by nlinarith)
  have hcard := coordinate_separated_ball_count hQ z R (Real.sqrt_nonneg _) U x
    (fun i hi j hj hne => hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne) hball
  have hpoint : ∀ i ∈ U, Real.exp (-t*‖x i-z‖^2) ≤ Real.exp (-(k:ℝ)) := by
    intro i hi
    have hk := (Finset.mem_filter.mp hi).2
    have hlo := Nat.floor_le (show 0 ≤ t*‖x i-z‖^2 by positivity)
    rw [hk] at hlo
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsqrt : Real.sqrt ((k:ℝ)+1) ≤ (k:ℝ)+1 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k]))
  have hR : R ≤ ((k:ℝ)+1)/Real.sqrt t := by
    dsimp [R]
    rw [Real.sqrt_div (by positivity)]
    exact div_le_div_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
  have hbase : 2*Q*R+5 ≤ 7*(1+Q/Real.sqrt t)*((k:ℝ)+1) := by
    have hmul := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2*Q by positivity)
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hq : 0 ≤ Q/Real.sqrt t := by positivity
    rw [show 2*Q*(((k:ℝ)+1)/Real.sqrt t) = 2*(Q/Real.sqrt t)*((k:ℝ)+1) by ring] at hmul
    nlinarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ 2*Q*R+5 by dsimp [R]; positivity) hbase (Fintype.card β)
  change (∑ i ∈ U, Real.exp (-t*‖x i-z‖^2)) ≤ _
  calc
    _ ≤ (U.card:ℝ)*Real.exp (-(k:ℝ)) := by
      simpa using Finset.sum_le_sum hpoint
    _ ≤ (2*Q*R+5)^(Fintype.card β)*Real.exp (-(k:ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-(k:ℝ))).le
      simpa only [mul_pow,mul_assoc] using hh

theorem coordinate_gaussian_sum_bound {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (z : β → ℝ) (S : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1/Q ≤ ‖x i-x j‖) :
    (∑ i ∈ S, Real.exp (-t*‖x i-z‖^2)) ≤
      coordinateGaussianConstant β * (1+Q/Real.sqrt t)^(Fintype.card β) := by
  classical
  let bin := fun i : ι => ⌊t*‖x i-z‖^2⌋₊
  let B := S.image bin
  have he : (∑ i ∈ S, Real.exp (-t*‖x i-z‖^2)) =
      ∑ k ∈ B, ∑ i ∈ S with bin i = k, Real.exp (-t*‖x i-z‖^2) := by
    exact (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩) _).symm
  calc
    _ = _ := he
    _ ≤ ∑ k ∈ B, (7*(1+Q/Real.sqrt t))^(Fintype.card β) *
        (((k:ℝ)+1)^(Fintype.card β)*Real.exp (-(k:ℝ))) :=
      Finset.sum_le_sum (fun k _ => coordinate_gaussian_bin_bound hQ ht z S x hsep k)
    _ = (7*(1+Q/Real.sqrt t))^(Fintype.card β) *
        ∑ k ∈ B, ((k:ℝ)+1)^(Fintype.card β)*Real.exp (-(k:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (7*(1+Q/Real.sqrt t))^(Fintype.card β) *
        ∑' k : ℕ, ((k:ℝ)+1)^(Fintype.card β)*Real.exp (-(k:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (coordinate_gaussian_weight_summable (Fintype.card β)).sum_le_tsum B
        (fun k _ => by positivity)
    _ = _ := by rw [mul_pow,coordinateGaussianConstant]; ring

theorem coordinate_gaussian_summable {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (z : β → ℝ) (x : ι → β → ℝ)
    (hsep : ∀ i j, i ≠ j → 1/Q ≤ ‖x i-x j‖) :
    Summable (fun i => Real.exp (-t*‖x i-z‖^2)) := by
  apply summable_of_sum_le (c := coordinateGaussianConstant β*(1+Q/Real.sqrt t)^(Fintype.card β))
  · intro i
    exact (Real.exp_pos _).le
  · intro S
    exact coordinate_gaussian_sum_bound hQ ht z S x (fun i _ j _ => hsep i j)

theorem coordinate_gaussian_tsum_bound {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (z : β → ℝ) (x : ι → β → ℝ)
    (hsep : ∀ i j, i ≠ j → 1/Q ≤ ‖x i-x j‖) :
    (∑' i, Real.exp (-t*‖x i-z‖^2)) ≤
      coordinateGaussianConstant β*(1+Q/Real.sqrt t)^(Fintype.card β) := by
  apply Real.tsum_le_of_sum_le
  · intro i
    exact (Real.exp_pos _).le
  · intro S
    exact coordinate_gaussian_sum_bound hQ ht z S x (fun i _ j _ => hsep i j)


theorem coordinate_norm_sq_le_sum_sq (x : β → ℝ) :
    ‖x‖^2 ≤ ∑ b, (x b)^2 := by
  have hsum : 0 ≤ ∑ b, (x b)^2 := Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hnorm : ‖x‖ ≤ Real.sqrt (∑ b, (x b)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro b
    apply (Real.le_sqrt (norm_nonneg _) hsum).mpr
    simpa only [Real.norm_eq_abs,sq_abs] using
      (Finset.single_le_sum (fun c _ => sq_nonneg (x c)) (Finset.mem_univ b))
  have hh := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hnorm
  simpa only [Real.sq_sqrt hsum] using hh

theorem coordinate_euclidean_gaussian_summable {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (z : β → ℝ) (x : ι → β → ℝ)
    (hsep : ∀ i j, i ≠ j → 1/Q ≤ ‖x i-x j‖) :
    Summable (fun i => Real.exp (-t*∑ b, (x i b-z b)^2)) := by
  apply (coordinate_gaussian_summable hQ ht z x hsep).of_nonneg_of_le
  · intro i
    exact (Real.exp_pos _).le
  · intro i
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (coordinate_norm_sq_le_sum_sq (x i-z)) (by linarith)

theorem coordinate_euclidean_gaussian_tsum_bound {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (z : β → ℝ) (x : ι → β → ℝ)
    (hsep : ∀ i j, i ≠ j → 1/Q ≤ ‖x i-x j‖) :
    (∑' i, Real.exp (-t*∑ b, (x i b-z b)^2)) ≤
      coordinateGaussianConstant β*(1+Q/Real.sqrt t)^(Fintype.card β) := by
  apply (Summable.tsum_le_tsum ?_
    (coordinate_euclidean_gaussian_summable hQ ht z x hsep)
    (coordinate_gaussian_summable hQ ht z x hsep)).trans
      (coordinate_gaussian_tsum_bound hQ ht z x hsep)
  intro i
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (coordinate_norm_sq_le_sum_sq (x i-z)) (by linarith)

end
end ArtinMatthews.VaryingKummerAnalytic
