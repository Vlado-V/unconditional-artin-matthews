module

public import ArtinMatthews.MarkedMinorArcCellGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Literal source cells have uniformly bounded adjacency under the actual
bounded determinant cutoff. The bound is independent of Y and all bands. -/
namespace ArtinMatthews

/-- The actual integer cell at source width d₀*Y. -/
noncomputable def markedMinorPositionCell (r d₀ Y : ℝ) (z : ℤ × ℤ) : ℤ :=
  ⌊((z.2 : ℝ)/markedMinorIntegerTau r z)/(d₀*Y)⌋

private theorem minor_floor_difference (x y : ℝ) :
    |((⌊x⌋ : ℤ) : ℝ)-((⌊y⌋ : ℤ) : ℝ)| ≤ |x-y|+1 := by
  have hx₁ := Int.floor_le x
  have hx₂ := Int.lt_floor_add_one x
  have hy₁ := Int.floor_le y
  have hy₂ := Int.lt_floor_add_one y
  rw [abs_le]
  constructor <;> linarith [le_abs_self (x-y),neg_le_abs (x-y)]

/-- Source determinant cutoff and the actual dyadic shared-product range
force a bounded number of literal cell shifts. -/
theorem markedMinorPositionCell_bandwidth (r : ℝ) {Y d₀ c K D : ℝ}
    (hY : 0 < Y) (hd₀ : 0 < d₀) (hc : 0 < c) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hDhi : D ≤ 2*d₀) (z v : ℤ × ℤ)
    (hz : c ≤ |markedMinorIntegerTau r z|) (hv : c ≤ |markedMinorIntegerTau r v|)
    (hdet : |(markedMinorIntegerDet z v : ℝ)| ≤ K*D*Y) :
    |((markedMinorPositionCell r d₀ Y v : ℤ) : ℝ)-
      ((markedMinorPositionCell r d₀ Y z : ℤ) : ℝ)| ≤ 2*K/c^2+1 := by
  have hz₀ : markedMinorIntegerTau r z ≠ 0 := abs_pos.mp (hc.trans_le hz)
  have hv₀ : markedMinorIntegerTau r v ≠ 0 := abs_pos.mp (hc.trans_le hv)
  have hden : c^2 ≤ |markedMinorIntegerTau r z| * |markedMinorIntegerTau r v| := by
    nlinarith [mul_le_mul hz hv hc.le (abs_nonneg _)]
  have hr : |(v.2 : ℝ)/markedMinorIntegerTau r v-(z.2 : ℝ)/markedMinorIntegerTau r z| ≤
      (2*K/c^2)*(d₀*Y) := by
    rw [markedMinorIntegerTau_difference r z v hz₀ hv₀,abs_div,abs_mul]
    calc
      _ ≤ (K*D*Y)/(|markedMinorIntegerTau r z| * |markedMinorIntegerTau r v|) :=
        div_le_div_of_nonneg_right hdet (by positivity)
      _ ≤ (K*D*Y)/c^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ (K*(2*d₀)*Y)/c^2 := by gcongr
      _ = _ := by field_simp
  have hs : |((v.2 : ℝ)/markedMinorIntegerTau r v)/(d₀*Y)-
      ((z.2 : ℝ)/markedMinorIntegerTau r z)/(d₀*Y)| ≤ 2*K/c^2 := by
    rw [← sub_div,abs_div,abs_of_pos (mul_pos hd₀ hY)]
    exact (div_le_iff₀ (mul_pos hd₀ hY)).mpr hr
  exact (minor_floor_difference _ _).trans (add_le_add hs le_rfl)

/-- A literal finite set of possible shifts, with no Y- or band-dependent
cardinality, contains every edge allowed by the source determinant cutoff. -/
theorem markedMinorPositionCell_shift_mem (r : ℝ) {Y d₀ c K D : ℝ}
    (hY : 0 < Y) (hd₀ : 0 < d₀) (hc : 0 < c) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hDhi : D ≤ 2*d₀) (z v : ℤ × ℤ)
    (hz : c ≤ |markedMinorIntegerTau r z|) (hv : c ≤ |markedMinorIntegerTau r v|)
    (hdet : |(markedMinorIntegerDet z v : ℝ)| ≤ K*D*Y) :
    markedMinorPositionCell r d₀ Y v-markedMinorPositionCell r d₀ Y z ∈
      Finset.Icc (-(⌈2*K/c^2+1⌉₊ : ℤ)) (⌈2*K/c^2+1⌉₊ : ℤ) := by
  have hh := markedMinorPositionCell_bandwidth r hY hd₀ hc hK hD hDhi z v hz hv hdet
  have hn : 2*K/c^2+1 ≤ (⌈2*K/c^2+1⌉₊ : ℝ) := Nat.le_ceil _
  have hb := abs_le.mp (hh.trans hn)
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2⟩

end ArtinMatthews
