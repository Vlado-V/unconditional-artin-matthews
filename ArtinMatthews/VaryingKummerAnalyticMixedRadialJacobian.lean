module

public import ArtinMatthews.VaryingKummerAnalyticMixedRadialMeasure
public import ArtinMatthews.VaryingKummerAnalyticMixedRadialCoordinates
public import ArtinMatthews.VaryingKummerAnalyticMellinScaling


set_option backward.privateInPublic true
@[expose] public section

/-! The full mixed-signature radial/log-coordinate Jacobian. The archimedean
multiplicities and the field degree remain explicit. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedRadialLogCoordinates_continuous :
    Continuous (fun p : ℝ × logSpace K => mixedRadialLogCoordinates K p.2 p.1) := by
  apply continuous_pi
  intro w
  exact ((mixedRestoredPlaceLog_continuous K w).comp continuous_snd |>.div_const _).add
    (continuous_fst.div_const 2)

theorem lintegral_mixedRadialLogCoordinates
    (f : (InfinitePlace K → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v : ℝ, ∫⁻ u : logSpace K, f (mixedRadialLogCoordinates K u v)) =
      ENNReal.ofReal ((2 / (Module.finrank ℚ K : ℝ)) *
        ∏ w : InfinitePlace K, (InfinitePlace.mult w : ℝ)) * ∫⁻ x, f x := by
  let c : ℝ := (Module.finrank ℚ K : ℝ)/2
  have hc : 0 < c := div_pos (Nat.cast_pos.mpr Module.finrank_pos) (by norm_num)
  let F : (InfinitePlace K → ℝ) → ℝ≥0∞ :=
    fun x => f (fun w => x w / InfinitePlace.mult w)
  have hF : Measurable F := hf.comp (by fun_prop)
  have he (u : logSpace K) (v : ℝ) :
      mixedRadialLogCoordinates K u v = fun w =>
        mixedPlaceInsert K
          (u + fun z : {w : InfinitePlace K // w ≠ w₀} => (InfinitePlace.mult z.1 : ℝ)*v/2)
          (c*v - ∑ z, (u + fun z : {w : InfinitePlace K // w ≠ w₀} => (InfinitePlace.mult z.1 : ℝ)*v/2) z) w /
            InfinitePlace.mult w := by
    ext w
    by_cases hw : w = w₀
    · subst w
      simp only [mixedRadialLogCoordinates, mixedRestoredPlaceLog, mixedPlaceInsert,
        Pi.add_apply, Finset.sum_add_distrib]
      have hm : (InfinitePlace.mult (w₀ : InfinitePlace K) : ℝ) +
          ∑ z : {w : InfinitePlace K // w ≠ w₀}, (InfinitePlace.mult z.1 : ℝ) =
          Module.finrank ℚ K := by
        rw [← Fintype.sum_eq_add_sum_subtype_ne
          (fun w : InfinitePlace K => (InfinitePlace.mult w : ℝ)) w₀,
          ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
      simp only [dite_true]
      have hsum : (∑ z : {w : InfinitePlace K // w ≠ w₀},
          (InfinitePlace.mult z.1 : ℝ)*v/2) =
          (∑ z : {w : InfinitePlace K // w ≠ w₀}, (InfinitePlace.mult z.1 : ℝ))*v/2 := by
        rw [Finset.sum_mul, Finset.sum_div]
      rw [hsum]
      dsimp [c]
      field_simp
      linear_combination v * hm
    · simp only [mixedRadialLogCoordinates, mixedRestoredPlaceLog, mixedPlaceInsert,
        dite_eq_right hw, Pi.add_apply]
      field_simp
  calc
    _ = ∫⁻ v : ℝ, ∫⁻ u : logSpace K, F (mixedPlaceInsert K u (c*v - ∑ z, u z)) := by
      apply lintegral_congr
      intro v
      simp_rw [he]
      exact lintegral_add_right_eq_self (fun u : logSpace K =>
        F (mixedPlaceInsert K u (c*v - ∑ z, u z)))
        (fun z : {w : InfinitePlace K // w ≠ w₀} => (InfinitePlace.mult z.1 : ℝ)*v/2)
    _ = ∫⁻ u : logSpace K, ∫⁻ v : ℝ, F (mixedPlaceInsert K u (c*v - ∑ z, u z)) := by
      apply lintegral_lintegral_swap
      exact (hF.comp ((mixedPlaceInsert_measurable K).comp
        (measurable_snd.prodMk (by fun_prop)))).aemeasurable
    _ = ∫⁻ u : logSpace K, ENNReal.ofReal c⁻¹ * ∫⁻ v : ℝ, F (mixedPlaceInsert K u v) := by
      apply lintegral_congr
      intro u
      rw [lintegral_comp_pos_mul hc (fun v => F (mixedPlaceInsert K u (v - ∑ z, u z)))]
      congr 1
      exact lintegral_sub_right_eq_self (fun v => F (mixedPlaceInsert K u v)) (∑ z, u z)
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ x, F x := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_mixedPlaceInsert K F hF]
    _ = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (∏ w : InfinitePlace K,
        (InfinitePlace.mult w : ℝ)) * ∫⁻ x, f x) := by
      rw [lintegral_div_coordinates (fun w : InfinitePlace K => (InfinitePlace.mult w : ℝ))
        (fun _ => Nat.cast_pos.mpr InfinitePlace.mult_pos) f hf]
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
      congr 2
      dsimp [c]
      ring

end
end ArtinMatthews.VaryingKummerAnalytic
