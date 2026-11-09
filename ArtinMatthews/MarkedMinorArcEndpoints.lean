module

public import ArtinMatthews.MarkedMinorArcCleanKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Actual endpoint diagonal tests preserve clean-edge decay. Fixed bounded
square-root mass factors are absorbed with a fixed exponent margin. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The periodic major arcs are exactly the real rational arcs, without
enlarging either the reduced denominator cutoff or the source radius. -/
theorem markedMinorCircleMajor_coe_iff (θ Q Y : ℝ) :
    (θ : AddCircle (1:ℝ)) ∈ markedMinorCircleMajor Q Y ↔ MarkedInMajorArcs θ Q Y := by
  constructor
  · intro h
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp h
    split_ifs at hr with hden
    · have hp : θ ∈ ((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹'
          Metric.closedBall (((r : ℝ) : AddCircle (1:ℝ))) (2*Q/Y) := hr
      rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hp
      obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hp
      refine ⟨r+z,?_,?_⟩
      · simpa only [Rat.add_intCast_den] using hden
      · simpa only [Metric.mem_closedBall,Real.dist_eq,Rat.cast_add,Rat.cast_intCast,
          zsmul_eq_mul,mul_one] using hz
    · exact False.elim hr
  · intro h
    by_contra hn
    exact markedMinorCircleMajor_real hn h

/-- Literal endpoint multiplication of a finite matrix kernel. -/
noncomputable def markedMinorEndpointMatrix {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (u v : ι → ℂ) : Matrix ι ι ℂ :=
  fun h l => u h * A h l * v l

theorem markedMinorEndpointMatrix_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    markedMinorEndpointMatrix A u v = Matrix.diagonal u * A * Matrix.diagonal v := by
  ext h l
  simp only [markedMinorEndpointMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem markedMinorEndpointMatrix_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (u v : ι → ℂ) {Bu Bv : ℝ} (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv)
    (hu : ∀ h, ‖u h‖ ≤ Bu) (hv : ∀ l, ‖v l‖ ≤ Bv) :
    ‖markedMinorEndpointMatrix A u v‖ ≤ (Bu*Bv)*‖A‖ := by
  have hdu : ‖(Matrix.diagonal u : Matrix ι ι ℂ)‖ ≤ Bu := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hBu).mpr hu
  have hdv : ‖(Matrix.diagonal v : Matrix ι ι ℂ)‖ ≤ Bv := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hBv).mpr hv
  rw [markedMinorEndpointMatrix_eq_diagonal]
  calc
    _ ≤ (‖(Matrix.diagonal u : Matrix ι ι ℂ)‖*‖A‖)*‖(Matrix.diagonal v : Matrix ι ι ℂ)‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
        (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (Bu*‖A‖)*Bv := mul_le_mul
      (mul_le_mul_of_nonneg_right hdu (norm_nonneg _)) hdv (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Actual arbitrary endpoint tests, support restrictions, goodness tests,
and bounded mass factors preserve arbitrary logarithmic decay. The chosen
major-arc exponent G+4 remains independent of the band exponents. -/
theorem marked_minor_tested_clean_product_opNorm (ψ : SchwartzMap ℝ ℂ) {G C H Bu Bv : ℝ}
    (hG : 0 < G) (hC : 1 ≤ C) (hH : 1 ≤ H) (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) :
    ∀ᶠ Λ : ℝ in Filter.atTop, ∀ (Y : ℝ) (L T : ℤ) (M N : ℕ) (S : Finset ℤ)
      (u v : MarkedMinorBoxIndex L T M N × S → ℂ),
      Real.exp (Λ^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*Λ^(1/5 : ℝ)) →
      1 ≤ M → 1 ≤ N → (M : ℝ)*(N : ℝ) ≤ C*Y →
      (M : ℝ) ≤ C*Y^(9/10 : ℝ) → (N : ℝ) ≤ C*Y^(9/10 : ℝ) →
      (∀ h, ‖u h‖ ≤ Bu) → (∀ l, ‖v l‖ ≤ Bv) →
      ‖markedMinorEndpointMatrix
        (markedMinorCleanProductMatrix ψ L T M N Y (Λ^(G+4)) S) u v‖ ≤ Λ^(-G) := by
  classical
  have hminor := marked_minor_clean_product_opNorm ψ (show 0<G+1 by linarith) hC hH
  simp only [show (G+1)+3=G+4 by ring] at hminor
  filter_upwards [hminor,Filter.eventually_ge_atTop (max 1 (Bu*Bv))] with Λ hΛ hlarge
  intro Y L T M N S u v hYlo hYhi hMpos hNpos hMN hM hN hu hv
  have hΛp : 0 < Λ := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hlarge)
  have hb : Bu*Bv ≤ Λ := (le_max_right _ _).trans hlarge
  have hr : Λ^(-(G+1)) = Λ^(-G)*Λ⁻¹ := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hΛp]
    congr 1
    ring
  calc
    _ ≤ (Bu*Bv)*‖markedMinorCleanProductMatrix ψ L T M N Y (Λ^(G+4)) S‖ :=
      markedMinorEndpointMatrix_norm_le _ u v hBu hBv hu hv
    _ ≤ (Bu*Bv)*Λ^(-(G+1)) := mul_le_mul_of_nonneg_left
      (hΛ Y L T M N S hYlo hYhi hMpos hNpos hMN hM hN) (mul_nonneg hBu hBv)
    _ ≤ Λ*Λ^(-(G+1)) := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hΛp.le _)
    _ = Λ^(-G) := by rw [hr]; field_simp

end ArtinMatthews
