module

public import ArtinMatthews.CubicNormCellGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! The actual shifted radial weight varies by O(M/√x) on a period-M
Eisenstein coordinate cell in the small-period range. -/

noncomputable section
namespace ArtinMatthews

private theorem cubicNormForm_change_le {s M a b u v : ℝ}
    (hM : 0 ≤ M) (hMs : M ≤ s) (ha : |a| ≤ 4 * s) (hb : |b| ≤ 4 * s)
    (hu : |u| ≤ M) (hv : |v| ≤ M) :
    |((a + u) ^ 2 - (a + u) * (b + v) + (b + v) ^ 2) -
      (a ^ 2 - a * b + b ^ 2)| ≤ 27 * M * s := by
  have hlin (a b : ℝ) (ha : |a| ≤ 4 * s) (hb : |b| ≤ 4 * s) :
      |2 * a - b| ≤ 12 * s := by
    calc
      _ ≤ |2 * a| + |b| := abs_sub _ _
      _ = 2 * |a| + |b| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := by linarith
  have hprod (u v : ℝ) (hu : |u| ≤ M) (hv : |v| ≤ M) : |u * v| ≤ M * M := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) hM
  have hrem : |u ^ 2 - u * v + v ^ 2| ≤ 3 * M * M := by
    calc
      _ ≤ |u ^ 2 - u * v| + |v ^ 2| := abs_add_le _ _
      _ ≤ |u ^ 2| + |u * v| + |v ^ 2| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ M * M + M * M + M * M := by
        simp only [pow_two]
        exact add_le_add (add_le_add (hprod u u hu hu) (hprod u v hu hv)) (hprod v v hv hv)
      _ = _ := by ring
  have hlinmul (a b u : ℝ) (ha : |a| ≤ 4 * s) (hb : |b| ≤ 4 * s)
      (hu : |u| ≤ M) : |(2 * a - b) * u| ≤ 12 * s * M := by
    rw [abs_mul]
    exact mul_le_mul (hlin a b ha hb) hu (abs_nonneg _) (by linarith)
  have heq : ((a + u) ^ 2 - (a + u) * (b + v) + (b + v) ^ 2) -
      (a ^ 2 - a * b + b ^ 2) =
      (2 * a - b) * u + (2 * b - a) * v + (u ^ 2 - u * v + v ^ 2) := by ring
  rw [heq]
  calc
    _ ≤ |(2 * a - b) * u + (2 * b - a) * v| + |u ^ 2 - u * v + v ^ 2| := abs_add_le _ _
    _ ≤ |(2 * a - b) * u| + |(2 * b - a) * v| + |u ^ 2 - u * v + v ^ 2| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 12 * s * M + 12 * s * M + 3 * M * M :=
      add_le_add (add_le_add (hlinmul a b u ha hb hu) (hlinmul b a v hb ha hv)) hrem
    _ ≤ 27 * M * s := by nlinarith [mul_le_mul_of_nonneg_left hMs hM]

theorem cubicNormRadial_cell_variation (Φ : ℝ → ℝ) {L : NNReal} (hL : LipschitzWith L Φ)
    {x : ℝ} (hx : 1 ≤ x) {M : ℕ} [NeZero M] (hM : (M : ℝ) ≤ Real.sqrt x)
    {k : ℤ × ℤ} (hk : k ∈ cubicNormCoordinateBox (cubicNormCellRadius M x))
    (r : Fin M × Fin M) :
    ‖cubicNormRadial Φ x (cubicNormCellPoint M k r) -
      cubicNormRadial Φ x (k.1 * (M : ℤ), k.2 * (M : ℤ))‖ ≤
        27 * (L : ℝ) * (M : ℝ) / Real.sqrt x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hM₀ : 0 < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hsqrt := Real.sqrt_pos.2 hx₀
  have hk' := mem_cubicNormCoordinateBox.mp hk
  have hfloor : (cubicNormCellRadius M x : ℝ) ≤ 3 * Real.sqrt x / (M : ℝ) + 1 :=
    Nat.floor_le (by positivity)
  have hbase (v : ℤ) (hv : |(v : ℝ)| ≤ (cubicNormCellRadius M x : ℝ)) :
      |(v : ℝ) * (M : ℝ)| ≤ 4 * Real.sqrt x := by
    calc
      _ = |(v : ℝ)| * (M : ℝ) := by rw [abs_mul, abs_of_pos hM₀]
      _ ≤ (3 * Real.sqrt x / (M : ℝ) + 1) * (M : ℝ) :=
        mul_le_mul_of_nonneg_right (hv.trans hfloor) hM₀.le
      _ = 3 * Real.sqrt x + (M : ℝ) := by rw [add_mul, div_mul_cancel₀ _ hM₀.ne', one_mul]
      _ ≤ _ := by linarith
  have hrem (v : Fin M) : |(v : ℝ)| ≤ (M : ℝ) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast v.isLt.le
  have hnorm : |(eisensteinIntegerNorm (cubicNormCellPoint M k r) : ℝ) -
      (eisensteinIntegerNorm (k.1 * (M : ℤ), k.2 * (M : ℤ)) : ℝ)| ≤
        27 * (M : ℝ) * Real.sqrt x := by
    rw [cubicNormCellPoint_eq]
    simp only [eisensteinIntegerNorm, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_mul,
      Int.cast_natCast]
    exact cubicNormForm_change_le hM₀.le hM (hbase k.1 hk'.1) (hbase k.2 hk'.2)
      (hrem r.1) (hrem r.2)
  unfold cubicNormRadial
  refine (hL.norm_sub_le _ _).trans ?_
  rw [← sub_div, sub_sub_sub_cancel_right, Real.norm_eq_abs, abs_div, abs_of_pos hx₀]
  calc
    _ ≤ (L : ℝ) * (27 * (M : ℝ) * Real.sqrt x / x) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnorm hx₀.le) L.coe_nonneg
    _ = _ := by
      have heq : Real.sqrt x / x = 1 / Real.sqrt x := by
        apply (div_eq_div_iff hx₀.ne' hsqrt.ne').mpr
        rw [← pow_two, Real.sq_sqrt hx₀.le, one_mul]
      calc
        _ = (L : ℝ) * (27 * (M : ℝ)) * (Real.sqrt x / x) := by ring
        _ = _ := by rw [heq]; ring

end ArtinMatthews
