module

public import ArtinMatthews.SourceHyperbolicProductMeasureGreen
public import ArtinMatthews.SourceHyperbolicH1Gradient


set_option backward.privateInPublic true
@[expose] public section

/-! The exact positive diagonal coefficients in the product's Cartesian coordinates. -/

namespace ArtinMatthews.SourceHyperbolicGreen
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators ENNReal InnerProductSpace Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def productNativeDensity (x : ProductSpace ι) : ℝ :=
  ∏ i, ((x i 2)^3)⁻¹

theorem productNativeDensity_pos {x : ProductSpace ι} (hx : x ∈ productUpper ι) :
    0 < productNativeDensity x :=
  Finset.prod_pos fun i _ => inv_pos.mpr (pow_pos (productUpper_pos hx i) 3)

theorem productNativeDensity_complex (x : ProductSpace ι) :
    (productNativeDensity x : ℂ) = productComplexDensity x := by
  simp only [productNativeDensity, productComplexDensity, Complex.ofReal_prod,
    Complex.ofReal_inv, Complex.ofReal_pow]

theorem productNativeDensity_toReal {x : ProductSpace ι} (hx : x ∈ productUpper ι) :
    productNativeDensity x = (productDensity x).toReal :=
  Complex.ofReal_injective
    ((productNativeDensity_complex x).trans (productDensity_toReal_complex hx).symm)

theorem productNativeDensity_contDiffAt {x : ProductSpace ι} (hx : x ∈ productUpper ι) :
    ContDiffAt ℝ ∞ productNativeDensity x := by
  apply contDiffAt_prod
  intro i _
  have hi : ContDiffAt ℝ ∞ (fun y : ProductSpace ι => y i 2) x := by fun_prop
  exact (hi.pow 3).fun_inv (pow_ne_zero 3 (productUpper_pos hx i).ne')

theorem productVolume_volume_restrict_le_smul {S : Set (ProductSpace ι)}
    (hS : IsCompact S) (hSupper : S ⊆ productUpper ι) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ (volume.restrict S : Measure (ProductSpace ι)) ≤ c • productVolume ι := by
  by_cases he : S.Nonempty
  · have hρ : ContinuousOn productNativeDensity S :=
      fun x hx => (productNativeDensity_contDiffAt (hSupper hx)).continuousAt.continuousWithinAt
    obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn he hρ
    let a := ENNReal.ofReal (productNativeDensity x)
    have ha : a ≠ 0 := (ENNReal.ofReal_pos.mpr (productNativeDensity_pos (hSupper hx))).ne'
    have haf : a ≠ ⊤ := ENNReal.ofReal_ne_top
    have hle : a • (volume.restrict S : Measure (ProductSpace ι)) ≤ (productVolume ι).restrict S := by
      rw [← withDensity_const, productVolume_eq_density, restrict_withDensity hS.isClosed.measurableSet,
        Measure.restrict_restrict_of_subset hSupper]
      apply withDensity_mono
      filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with y hy
      change a ≤ productDensity y
      rw [← ENNReal.ofReal_toReal (productDensity_lt_top y).ne, ← productNativeDensity_toReal (hSupper hy)]
      exact ENNReal.ofReal_le_ofReal (hmin hy)
    refine ⟨a⁻¹, ENNReal.inv_ne_top.mpr ha, ?_⟩
    calc
      _ = a⁻¹ • (a • (volume.restrict S : Measure (ProductSpace ι))) := by
        rw [smul_smul, ENNReal.inv_mul_cancel ha haf, one_smul]
      _ ≤ a⁻¹ • (productVolume ι).restrict S := by gcongr
      _ ≤ _ := by gcongr; exact Measure.restrict_le_self
  · have hE : S = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    refine ⟨1, ENNReal.one_ne_top, ?_⟩
    simp only [hE, Measure.restrict_empty, one_smul]
    exact bot_le

private def productCoordinateProjection (ij : ι × Fin 3) : H1Vector ι →L[ℝ] H1Vector ι :=
  (((PiLp.proj 2 (fun _ : ι × Fin 3 => ℂ) ij : H1Vector ι →L[ℂ] ℂ).smulRight
    (EuclideanSpace.basisFun (ι × Fin 3) ℂ ij))).restrictScalars ℝ

def productNativeDiagonal (a : ι × Fin 3 → ℝ) : H1Vector ι →L[ℝ] H1Vector ι :=
  ∑ ij, a ij • productCoordinateProjection ij

theorem productNativeDiagonal_apply (a : ι × Fin 3 → ℝ) (w : H1Vector ι)
    (ij : ι × Fin 3) : productNativeDiagonal a w ij = (a ij : ℂ) * w ij := by
  rw [productNativeDiagonal, sum_apply]
  change (PiLp.proj 2 (fun _ : ι × Fin 3 => ℂ) ij : H1Vector ι →L[ℂ] ℂ)
    (∑ k : ι × Fin 3, (a k • productCoordinateProjection k) w) = _
  rw [map_sum, Finset.sum_eq_single ij]
  · simp [productCoordinateProjection, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      Complex.real_smul]
  · intro k _ hki
    simp [productCoordinateProjection, EuclideanSpace.basisFun_apply, PiLp.single_apply, hki]
  · simp

theorem productNativeDiagonal_smul (a : ι × Fin 3 → ℝ) (c : ℂ) (w : H1Vector ι) :
    productNativeDiagonal a (c • w) = c • productNativeDiagonal a w := by
  ext ij
  simp only [productNativeDiagonal_apply, PiLp.smul_apply, smul_eq_mul]
  ring

def productNativeCoefficient (x : ProductSpace ι) : H1Vector ι →L[ℝ] H1Vector ι :=
  productNativeDiagonal fun ij => productNativeDensity x * (x ij.1 2)^2

def productNativeUnweight (x : ProductSpace ι) : H1Vector ι →L[ℝ] H1Vector ι :=
  productNativeDiagonal fun ij => (x ij.1 2)⁻¹

theorem productNativeCoefficient_contDiffAt {x : ProductSpace ι} (hx : x ∈ productUpper ι) :
    ContDiffAt ℝ ∞ productNativeCoefficient x := by
  apply ContDiffAt.sum
  intro ij _
  have hi : ContDiffAt ℝ ∞ (fun y : ProductSpace ι => y ij.1 2) x := by fun_prop
  exact ((productNativeDensity_contDiffAt hx).mul (hi.pow 2)).smul contDiffAt_const

theorem productNativeUnweight_measurable :
    Measurable (productNativeUnweight (ι := ι)) := by
  apply Finset.measurable_sum
  intro ij _
  have hi : Measurable (fun y : ProductSpace ι => y ij.1 2) := by fun_prop
  exact hi.inv.smul measurable_const

theorem productNativeUnweight_continuousOn :
    ContinuousOn (productNativeUnweight (ι := ι)) (productUpper ι) := by
  intro x hx
  have hd : ContDiffAt ℝ ∞ productNativeUnweight x := by
    apply ContDiffAt.sum
    intro ij _
    have hi : ContDiffAt ℝ ∞ (fun y : ProductSpace ι => y ij.1 2) x := by fun_prop
    exact (hi.fun_inv (productUpper_pos hx ij.1).ne').smul contDiffAt_const
  exact hd.continuousAt.continuousWithinAt

theorem productNativeUnweight_bounded {S : Set (ProductSpace ι)}
    (hS : IsCompact S) (hSupper : S ⊆ productUpper ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ‖productNativeUnweight x‖ ≤ C := by
  by_cases he : S.Nonempty
  · obtain ⟨x, _, hm⟩ := hS.exists_isMaxOn he (productNativeUnweight_continuousOn.mono hSupper).norm
    exact ⟨‖productNativeUnweight x‖, norm_nonneg _, hm⟩
  · exact ⟨0, le_rfl, fun x hx => (he ⟨x,hx⟩).elim⟩

theorem productNativeDiagonal_coercive (a : ι × Fin 3 → ℝ) (ha : ∀ ij, 0 < a ij) :
    ∃ c > 0, ∀ w : H1Vector ι, c*‖w‖*‖w‖ ≤
      (Inner.rclikeToReal ℂ (H1Vector ι)).inner (productNativeDiagonal a w) w := by
  let R : ℝ := 1 + ∑ ij, (a ij)⁻¹
  have hR : 0 < R := by
    have h := Finset.sum_nonneg (fun ij (_ : ij ∈ Finset.univ) => (inv_pos.mpr (ha ij)).le)
    change 0 < 1 + ∑ ij, (a ij)⁻¹
    linarith
  refine ⟨R⁻¹, inv_pos.mpr hR, ?_⟩
  intro w
  have hle (ij : ι × Fin 3) : R⁻¹ ≤ a ij := by
    rw [← inv_inv (a ij), inv_le_inv₀ hR (inv_pos.mpr (ha ij))]
    have h := Finset.single_le_sum (f := fun k => (a k)⁻¹)
      (fun k _ => (inv_pos.mpr (ha k)).le) (Finset.mem_univ ij)
    dsimp only [R]
    linarith
  rw [real_inner_eq_re_inner ℂ, PiLp.inner_apply]
  have hre :
      RCLike.re (∑ ij : ι × Fin 3, inner ℂ (productNativeDiagonal a w ij) (w ij)) =
        ∑ ij : ι × Fin 3, a ij * ‖w ij‖^2 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ij _
    rw [productNativeDiagonal_apply, ← smul_eq_mul, inner_smul_left, inner_self_eq_norm_sq_to_K]
    change ((star (a ij : ℂ)) * (‖w ij‖ : ℂ)^2).re = _
    rw [Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hre, mul_assoc, ← pow_two, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun ij _ => mul_le_mul_of_nonneg_right (hle ij) (sq_nonneg _)

end
end ArtinMatthews.SourceHyperbolicGreen
