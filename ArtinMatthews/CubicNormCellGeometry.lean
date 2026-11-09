module

public import ArtinMatthews.CubicThetaRationalTwist


set_option backward.privateInPublic true
@[expose] public section

/-! Actual coordinate cells and the support of the shifted Eisenstein radial
test in Section 6.2. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths

def cubicNormCoordinateBox (B : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B

theorem mem_cubicNormCoordinateBox {B : ℕ} {z : ℤ × ℤ} :
    z ∈ cubicNormCoordinateBox B ↔
      |(z.1 : ℝ)| ≤ (B : ℝ) ∧ |(z.2 : ℝ)| ≤ (B : ℝ) := by
  obtain ⟨a, b⟩ := z
  simp only [cubicNormCoordinateBox, Finset.mem_product, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩,
      ⟨by exact_mod_cast h₃, by exact_mod_cast h₄⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩,
      ⟨by exact_mod_cast h₃, by exact_mod_cast h₄⟩⟩

theorem cubicNormCoordinateBox_card (B : ℕ) :
    (cubicNormCoordinateBox B).card = (2 * B + 1) ^ 2 := by
  have h : (B : ℤ) + 1 - -(B : ℤ) = ((2 * B + 1 : ℕ) : ℤ) := by push_cast; ring
  simp only [cubicNormCoordinateBox, Finset.card_product, Int.card_Icc, h,
    Int.toNat_natCast, pow_two]

def cubicNormRadial (Φ : ℝ → ℝ) (x : ℝ) (z : ℤ × ℤ) : ℝ :=
  Φ (((eisensteinIntegerNorm z : ℝ) - 1) / x)

theorem cubicNormRadial_coordinates_le (Φ : ℝ → ℝ)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x) {z : ℤ × ℤ}
    (hz : cubicNormRadial Φ x z ≠ 0) :
    |(z.1 : ℝ)| ≤ 3 * Real.sqrt x ∧ |(z.2 : ℝ)| ≤ 3 * Real.sqrt x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hq := (div_lt_iff₀ hx₀).mp (hs hz).2
  simp only [eisensteinIntegerNorm, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_pow] at hq
  have hsqrt := Real.sq_sqrt hx₀.le
  have hsum : (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤
      2 * ((z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2) := by
    nlinarith [sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ))]
  have h₁ : |(z.1 : ℝ)| ^ 2 ≤ (3 * Real.sqrt x) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (z.2 : ℝ)]
  have h₂ : |(z.2 : ℝ)| ^ 2 ≤ (3 * Real.sqrt x) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (z.1 : ℝ)]
  exact ⟨(sq_le_sq₀ (abs_nonneg _) (by positivity)).mp h₁,
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp h₂⟩

theorem cubicNormRadial_mem_coordinateBox (Φ : ℝ → ℝ)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x) {z : ℤ × ℤ}
    (hz : cubicNormRadial Φ x z ≠ 0) :
    z ∈ cubicNormCoordinateBox ⌊3 * Real.sqrt x⌋₊ := by
  obtain ⟨h₁, h₂⟩ := cubicNormRadial_coordinates_le Φ hs hx hz
  refine mem_cubicNormCoordinateBox.mpr ⟨?_, ?_⟩
  · rw [← Int.cast_abs, ← Nat.cast_natAbs] at h₁ ⊢
    exact Nat.cast_le.mpr (Nat.le_floor h₁)
  · rw [← Int.cast_abs, ← Nat.cast_natAbs] at h₂ ⊢
    exact Nat.cast_le.mpr (Nat.le_floor h₂)

def cubicNormCellPoint (M : ℕ) [NeZero M] (k : ℤ × ℤ) (r : Fin M × Fin M) :
    ℤ × ℤ :=
  (HeckeTheta.residueEquiv M).symm (r, k)

theorem cubicNormCellPoint_eq (M : ℕ) [NeZero M] (k : ℤ × ℤ) (r : Fin M × Fin M) :
    cubicNormCellPoint M k r =
      (k.1 * (M : ℤ) + (r.1 : ℤ), k.2 * (M : ℤ) + (r.2 : ℤ)) :=
  rfl

def cubicNormCellRadius (M : ℕ) (x : ℝ) : ℕ := ⌊3 * Real.sqrt x / (M : ℝ) + 1⌋₊

private theorem cubicNormCell_index_bound {M : ℕ} [NeZero M] {x : ℝ}
    (k : ℤ) (r : Fin M) (h : |((k * (M : ℤ) + (r : ℤ) : ℤ) : ℝ)| ≤ 3 * Real.sqrt x) :
    |(k : ℝ)| ≤ (cubicNormCellRadius M x : ℝ) := by
  have hM : 0 < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hr : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast r.isLt.le
  push_cast at h
  have hmul : |(k : ℝ)| * (M : ℝ) ≤ 3 * Real.sqrt x + (M : ℝ) := by
    calc
      _ = |(k : ℝ) * (M : ℝ)| := by rw [abs_mul, abs_of_pos hM]
      _ = |((k : ℝ) * (M : ℝ) + (r : ℝ)) - (r : ℝ)| := by rw [add_sub_cancel_right]
      _ ≤ |(k : ℝ) * (M : ℝ) + (r : ℝ)| + |(r : ℝ)| := abs_sub _ _
      _ ≤ _ := add_le_add h (by rwa [abs_of_nonneg (by positivity)])
  have hb := (le_div_iff₀ hM).mpr hmul
  rw [add_div, div_self hM.ne', ← Int.cast_abs, ← Nat.cast_natAbs] at hb
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact Nat.cast_le.mpr (Nat.le_floor hb)

theorem cubicNormRadial_mem_cellBox (Φ : ℝ → ℝ)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x)
    (M : ℕ) [NeZero M] {k : ℤ × ℤ} {r : Fin M × Fin M}
    (hr : cubicNormRadial Φ x (cubicNormCellPoint M k r) ≠ 0) :
    k ∈ cubicNormCoordinateBox (cubicNormCellRadius M x) := by
  obtain ⟨h₁, h₂⟩ := cubicNormRadial_coordinates_le Φ hs hx hr
  rw [cubicNormCellPoint_eq] at h₁ h₂
  exact mem_cubicNormCoordinateBox.mpr
    ⟨cubicNormCell_index_bound k.1 r.1 h₁, cubicNormCell_index_bound k.2 r.2 h₂⟩

end ArtinMatthews
