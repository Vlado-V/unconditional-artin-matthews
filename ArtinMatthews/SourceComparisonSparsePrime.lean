module

public import ArtinMatthews.MarkedMajorArcExceptionalCover


set_option backward.privateInPublic true
@[expose] public section

/-! Sparse large values for the actual prime polynomial on the comparison
scales. -/

namespace ArtinMatthews

open Filter ReusedMoments
open scoped Topology

noncomputable section

private theorem sparse_cost_linear_log_scale (c C₁ C₂ A : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ Y T : ℝ, 1 < Y →
      c * L^(1/(10:ℝ)) ≤ Real.log Y →
      Real.log Y ≤ C₁ * L → 1 < T → Real.log T ≤ C₂ * L →
      mrtShortPrimeSampleCost Y (L^(-A)) T (mrtAmplificationOrder Y T) ≤
        Real.exp (L^(91/(100:ℝ))) := by
  let R := C₂/c + 1
  let D := C₁ + 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  filter_upwards [marked_sparse_cost_envelopes R D A hR hD hA,
    eventually_ge_atTop (1:ℝ)] with L hcost hL
  intro Y T hY hlo hhi hT hTU
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow1 : 1 ≤ L^(9/(10:ℝ)) := Real.one_le_rpow hL (by norm_num)
  have hratio : C₂ * L / (c * L^(1/(10:ℝ))) = (C₂/c) * L^(9/(10:ℝ)) := by
    apply (div_eq_iff (mul_pos hc (Real.rpow_pos_of_pos hL0 _)).ne').mpr
    rw [mul_assoc, mul_left_comm (L^(9/(10:ℝ))) c, ← mul_assoc,
      mul_assoc (C₂/c) c, ← Real.rpow_add hL0]
    norm_num
    field_simp
  have hr : (mrtAmplificationOrder Y T : ℝ) ≤ R * L^(9/(10:ℝ)) := by
    have hceil := (mrt_amplification_order_bounds hY hT.le).2.2.le
    calc
      _ ≤ Real.log T/Real.log Y+1 := hceil
      _ ≤ C₂ * L/(c * L^(1/(10:ℝ)))+1 := by
        have hd := (div_le_div_of_nonneg_right hTU (Real.log_pos hY).le).trans
          (div_le_div_of_nonneg_left (mul_nonneg hC₂.le hL0.le)
            (mul_pos hc (Real.rpow_pos_of_pos hL0 _)) hlo)
        linarith
      _ ≤ _ := by rw [hratio]; dsimp [R]; nlinarith
  have hlog4 : Real.log (4*Y) ≤ D * L := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by linarith : Y ≠ 0)]
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    dsimp [D]
    nlinarith
  exact hcost Y T hY hT hr hlog4

/-- The actual exceptional cover is sparse throughout the larger prime-scale
range of the ordinary centered endpoint. -/
theorem sourceComparisonPrime_exceptionalIntervals_card (c C₁ C₂ A : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ P T : ℝ, 1 < P →
      c*X^(1/(10:ℝ)) ≤ Real.log P → Real.log P ≤ C₁*X →
      1 < T → T ≤ Real.exp (C₂*X) →
      ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (S : Finset ℕ),
        (∀ p ∈ S, p.Prime) → (∀ p ∈ S, (p:ℝ) ≤ 2*P) →
        ((markedExceptionalUnitIntervals (markedPrimePolynomial S P χ ξ) T (X^(-A))).card:ℝ)
          ≤ 3*Real.exp (X^(91/(100:ℝ))) := by
  filter_upwards [sparse_cost_linear_log_scale c C₁ C₂ A hc hC₁ hC₂ hA,
    eventually_gt_atTop (0:ℝ)] with X hcost hX
  intro P T hP hlo hhi hT hTU k χ ξ S hS hcap
  let F := markedPrimePolynomial S P χ ξ
  let I := markedExceptionalUnitIntervals F T (X^(-A))
  apply unitInterval_count_of_separated_samples I (fun t => |t| ≤ T ∧ X^(-A) ≤ ‖F t‖)
    (markedExceptionalUnitIntervals_witness F T (X^(-A)))
  intro J hJ hsep
  have hTlog : Real.log T ≤ C₂*X := by
    have h := Real.log_le_log (by linarith : 0 < T) hTU
    rwa [Real.log_exp] at h
  exact (markedPrimePolynomial_sample_cost S P (by linarith) χ ξ
    (mrtAmplificationOrder P T) hS hcap J (by linarith) (Real.rpow_pos_of_pos hX _)
    (fun t ht => (hJ t ht).1) hsep (fun t ht => (hJ t ht).2)).trans
    (hcost P T hP hlo hhi hT hTlog)

end
end ArtinMatthews
