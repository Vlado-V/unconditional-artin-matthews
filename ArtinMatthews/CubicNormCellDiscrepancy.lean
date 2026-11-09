module

public import ArtinMatthews.CubicNormCellVariation


set_option backward.privateInPublic true
@[expose] public section

/-! A complete period cell has zero arithmetic mean. Subtracting its value
at the cell origin gives the full smooth lattice discrepancy, with the
large-period range controlled by the actual finite coordinate support. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def cubicNormSmoothLatticeSum {M : ℕ} [NeZero M] (w : Fin M × Fin M → ℂ)
    (Φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑' z : ℤ × ℤ, HeckeTheta.periodicCoeff w z * (cubicNormRadial Φ x z : ℂ)

theorem cubicNormSmoothLatticeSum_eq_cells {M : ℕ} [NeZero M] (w : Fin M × Fin M → ℂ)
    (Φ : ℝ → ℝ) (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x) :
    cubicNormSmoothLatticeSum w Φ x =
      ∑ k ∈ cubicNormCoordinateBox (cubicNormCellRadius M x), ∑ r,
        w r * (cubicNormRadial Φ x (cubicNormCellPoint M k r) : ℂ) := by
  let B := cubicNormCoordinateBox (cubicNormCellRadius M x)
  let S : Finset ((Fin M × Fin M) × (ℤ × ℤ)) := Finset.univ ×ˢ B
  unfold cubicNormSmoothLatticeSum
  rw [← (HeckeTheta.residueEquiv M).symm.tsum_eq]
  change (∑' p : (Fin M × Fin M) × (ℤ × ℤ),
    HeckeTheta.periodicCoeff w (cubicNormCellPoint M p.2 p.1) *
      (cubicNormRadial Φ x (cubicNormCellPoint M p.2 p.1) : ℂ)) = _
  have hp (k : ℤ × ℤ) (r : Fin M × Fin M) :
      HeckeTheta.periodicCoeff w (cubicNormCellPoint M k r) = w r := by
    simp only [HeckeTheta.periodicCoeff, cubicNormCellPoint, Equiv.apply_symm_apply]
  simp_rw [hp]
  rw [tsum_eq_sum (s := S) ?_]
  · dsimp only [S]
    rw [Finset.sum_product, Finset.sum_comm]
  · intro p hp
    have hzero : cubicNormRadial Φ x (cubicNormCellPoint M p.2 p.1) = 0 := by
      by_contra hn
      exact hp (Finset.mem_product.mpr ⟨Finset.mem_univ _,
        cubicNormRadial_mem_cellBox Φ hs hx M hn⟩)
    rw [hzero, Complex.ofReal_zero, mul_zero]

private theorem cubicNormCell_card_bound {M : ℕ} [NeZero M] {x : ℝ} (hx : 0 ≤ x)
    (hM : (M : ℝ) ≤ Real.sqrt x) :
    ((cubicNormCoordinateBox (cubicNormCellRadius M x)).card : ℝ) * (M : ℝ) ^ 2 ≤
      81 * x := by
  have hM₀ : 0 < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hfloor : (cubicNormCellRadius M x : ℝ) ≤ 3 * Real.sqrt x / (M : ℝ) + 1 :=
    Nat.floor_le (by positivity)
  have hsize : (2 * (cubicNormCellRadius M x : ℝ) + 1) * (M : ℝ) ≤
      9 * Real.sqrt x := by
    calc
      _ ≤ (2 * (3 * Real.sqrt x / (M : ℝ) + 1) + 1) * (M : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hM₀.le
      _ = 6 * Real.sqrt x + 3 * (M : ℝ) := by field_simp [hM₀.ne']; ring
      _ ≤ _ := by linarith
  rw [cubicNormCoordinateBox_card]
  push_cast
  rw [← mul_pow]
  calc
    _ ≤ (9 * Real.sqrt x) ^ 2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hsize
    _ = _ := by rw [mul_pow, Real.sq_sqrt hx]; norm_num

private theorem cubicNormCoordinate_card_bound {x : ℝ} (hx : 1 ≤ x) :
    ((cubicNormCoordinateBox ⌊3 * Real.sqrt x⌋₊).card : ℝ) ≤ 49 * x := by
  have hx₀ := zero_le_one.trans hx
  have hs : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have hf : (⌊3 * Real.sqrt x⌋₊ : ℝ) ≤ 3 * Real.sqrt x := Nat.floor_le (by positivity)
  rw [cubicNormCoordinateBox_card]
  push_cast
  calc
    _ ≤ (7 * Real.sqrt x) ^ 2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    _ = _ := by rw [mul_pow, Real.sq_sqrt hx₀]; norm_num

theorem cubicNormSmoothLatticeSum_norm_le {M : ℕ} [NeZero M] (w : Fin M × Fin M → ℂ)
    (hw : ∀ r, ‖w r‖ ≤ 1) (hzero : ∑ r, w r = 0)
    (Φ : ℝ → ℝ) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    {L : NNReal} (hL : LipschitzWith L Φ) {x : ℝ} (hx : 1 ≤ x) :
    ‖cubicNormSmoothLatticeSum w Φ x‖ ≤
      2187 * (L : ℝ) * (M : ℝ) * Real.sqrt x + 49 * (L : ℝ) * (M : ℝ) ^ 2 := by
  have hx₀ := zero_lt_one.trans_le hx
  have hsqrt := Real.sqrt_pos.2 hx₀
  by_cases hM : (M : ℝ) ≤ Real.sqrt x
  · rw [cubicNormSmoothLatticeSum_eq_cells w Φ hs hx]
    let B := cubicNormCoordinateBox (cubicNormCellRadius M x)
    let V := 27 * (L : ℝ) * (M : ℝ) / Real.sqrt x
    have hV : 0 ≤ V := by dsimp only [V]; positivity
    have hcell (k : ℤ × ℤ) (hk : k ∈ B) :
        ‖∑ r, w r * (cubicNormRadial Φ x (cubicNormCellPoint M k r) : ℂ)‖ ≤
          (M : ℝ) ^ 2 * V := by
      let g (r : Fin M × Fin M) := cubicNormRadial Φ x (cubicNormCellPoint M k r)
      let c := cubicNormRadial Φ x (k.1 * (M : ℤ), k.2 * (M : ℤ))
      have heq : (∑ r, w r * (g r : ℂ)) = ∑ r, w r * ((g r - c : ℝ) : ℂ) := by
        simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          hzero, zero_mul, sub_zero]
      change ‖∑ r, w r * (g r : ℂ)‖ ≤ _
      rw [heq]
      calc
        _ ≤ ∑ r, ‖w r * ((g r - c : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _r : Fin M × Fin M, V := by
          apply Finset.sum_le_sum
          intro r _hr
          rw [norm_mul, Complex.norm_real]
          exact (mul_le_mul (hw r) (cubicNormRadial_cell_variation Φ hL hx hM hk r)
            (norm_nonneg _) zero_le_one).trans_eq (one_mul V)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul, pow_two]
    change ‖∑ k ∈ B, ∑ r, w r * (cubicNormRadial Φ x (cubicNormCellPoint M k r) : ℂ)‖ ≤ _
    calc
      _ ≤ ∑ k ∈ B, ‖∑ r, w r * (cubicNormRadial Φ x (cubicNormCellPoint M k r) : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k ∈ B, (M : ℝ) ^ 2 * V := Finset.sum_le_sum hcell
      _ = ((B.card : ℝ) * (M : ℝ) ^ 2) * V := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ (81 * x) * V := mul_le_mul_of_nonneg_right (cubicNormCell_card_bound hx₀.le hM) hV
      _ = 2187 * (L : ℝ) * (M : ℝ) * Real.sqrt x := by
        have hdiv : x / Real.sqrt x = Real.sqrt x :=
          (div_eq_iff hsqrt.ne').mpr (by rw [← pow_two, Real.sq_sqrt hx₀.le])
        calc
          _ = 2187 * (L : ℝ) * (M : ℝ) * (x / Real.sqrt x) := by dsimp only [V]; ring
          _ = _ := by rw [hdiv]
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · let B := cubicNormCoordinateBox ⌊3 * Real.sqrt x⌋₊
    have hΦ (t : ℝ) : ‖Φ t‖ ≤ (L : ℝ) := by
      have hΦ₁ : Φ 1 = 0 := not_not.mp (fun h => lt_irrefl _ (hs h).1)
      by_cases ht : Φ t = 0
      · rw [ht, norm_zero]
        exact L.coe_nonneg
      · obtain ⟨h₁, h₂⟩ := hs ht
        have hb := hL.norm_sub_le t 1
        rw [hΦ₁, sub_zero, Real.norm_eq_abs (t - 1),
          abs_of_nonneg (sub_nonneg.mpr h₁.le)] at hb
        exact hb.trans (mul_le_of_le_one_right L.coe_nonneg (by linarith))
    unfold cubicNormSmoothLatticeSum
    rw [tsum_eq_sum (s := B) ?_]
    · calc
        _ ≤ ∑ z ∈ B, ‖HeckeTheta.periodicCoeff w z * (cubicNormRadial Φ x z : ℂ)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _z ∈ B, (L : ℝ) := by
          apply Finset.sum_le_sum
          intro z _hz
          rw [norm_mul, Complex.norm_real]
          have hwp := hw (HeckeTheta.residueEquiv M z).1
          have hΦp := hΦ (((eisensteinIntegerNorm z : ℝ) - 1) / x)
          exact (mul_le_mul hwp hΦp (norm_nonneg _) zero_le_one).trans_eq (one_mul (L : ℝ))
        _ = (B.card : ℝ) * (L : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (49 * x) * (L : ℝ) :=
          mul_le_mul_of_nonneg_right (cubicNormCoordinate_card_bound hx) L.coe_nonneg
        _ ≤ (49 * (M : ℝ) ^ 2) * (L : ℝ) := by
          have hsq := (sq_le_sq₀ hsqrt.le (by positivity : 0 ≤ (M : ℝ))).mpr (le_of_not_ge hM)
          rw [Real.sq_sqrt hx₀.le] at hsq
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) L.coe_nonneg
        _ = 49 * (L : ℝ) * (M : ℝ) ^ 2 := by ring
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
    · intro z hz
      have hzero : cubicNormRadial Φ x z = 0 := by
        by_contra hn
        exact hz (cubicNormRadial_mem_coordinateBox Φ hs hx hn)
      rw [hzero, Complex.ofReal_zero, mul_zero]

end ArtinMatthews
