module

public import ArtinMatthews.MarkedMajorFourierSeparationBase


set_option backward.privateInPublic true
@[expose] public section

/-! Derivative and L1 control under the actual volume-preserving Hilbert
plane lift used by the marked major-arc Fourier coefficient. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem markedMajorPlaneEquiv_norm_le (x : MarkedMajorFourierPlane) :
    ‖markedMajorPlaneEquiv x‖ ≤ ‖x‖ := by
  change max ‖x.fst‖ ‖x.snd‖ ≤ ‖x‖
  exact max_le (WithLp.norm_fst_le (α := ℝ) (β := ℝ) x)
    (WithLp.norm_snd_le (α := ℝ) (β := ℝ) x)

theorem markedMajorPlaneEquiv_opNorm_le :
    ‖markedMajorPlaneEquiv.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖markedMajorPlaneEquiv x‖ ≤ 1*‖x‖
  simpa only [one_mul] using markedMajorPlaneEquiv_norm_le x

theorem markedMajorPlaneEquiv_integral (H : ℝ × ℝ → ℝ) :
    (∫ x : MarkedMajorFourierPlane, H (markedMajorPlaneEquiv x)) = ∫ p, H p := by
  exact (WithLp.volume_preserving_ofLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).symm.measurableEmbedding H

theorem markedMajorPlane_derivative_norm_integrable (g : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) :
    Integrable (fun p => ‖iteratedFDeriv ℝ n g p‖) := by
  simpa only [pow_zero, one_mul] using
    SchwartzMap.integrable_pow_mul_iteratedFDeriv volume g 0 n

theorem markedMajorPlaneLift_derivative_norm_integrable (g : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) :
    Integrable (fun p => ‖iteratedFDeriv ℝ n (markedMajorPlaneLift g) p‖) := by
  simpa only [pow_zero, one_mul] using
    SchwartzMap.integrable_pow_mul_iteratedFDeriv volume (markedMajorPlaneLift g) 0 n

theorem markedMajorPlaneLift_derivative_norm_le (g : SchwartzMap (ℝ × ℝ) ℂ)
    (n : ℕ) (x : MarkedMajorFourierPlane) :
    ‖iteratedFDeriv ℝ n (markedMajorPlaneLift g) x‖ ≤
      ‖iteratedFDeriv ℝ n g (markedMajorPlaneEquiv x)‖ := by
  let L := markedMajorPlaneEquiv.toContinuousLinearMap
  change ‖iteratedFDeriv ℝ n ((g : (ℝ × ℝ) → ℂ) ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (g.smooth ⊤) x (by simp)]
  have hn := (iteratedFDeriv ℝ n g (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  have hp : (∏ _ : Fin n, ‖L‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => markedMajorPlaneEquiv_opNorm_le)
  exact hn.trans (mul_le_of_le_one_right (norm_nonneg _) hp)

theorem markedMajorPlaneLift_derivative_L1_le (g : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) :
    (∫ x : MarkedMajorFourierPlane, ‖iteratedFDeriv ℝ n (markedMajorPlaneLift g) x‖) ≤
      ∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n g p‖ := by
  have hcomp : Integrable (fun x : MarkedMajorFourierPlane =>
      ‖iteratedFDeriv ℝ n g (markedMajorPlaneEquiv x)‖) :=
    ((WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (ℝ × ℝ)).symm.measurableEmbedding).mpr
      (markedMajorPlane_derivative_norm_integrable g n)
  calc
    _ ≤ ∫ x : MarkedMajorFourierPlane, ‖iteratedFDeriv ℝ n g (markedMajorPlaneEquiv x)‖ :=
      integral_mono (markedMajorPlaneLift_derivative_norm_integrable g n) hcomp
        (markedMajorPlaneLift_derivative_norm_le g n)
    _ = _ := markedMajorPlaneEquiv_integral (fun p : ℝ × ℝ => ‖iteratedFDeriv ℝ n g p‖)

/-- The actual integration-by-parts identity behind the decay estimate. -/
theorem markedMajorPlaneLift_fourier_iteratedFDeriv (g : SchwartzMap (ℝ × ℝ) ℂ)
    (n : ℕ) (w : MarkedMajorFourierPlane) :
    (𝓕 (iteratedFDeriv ℝ n (markedMajorPlaneLift g))) w =
      VectorFourier.fourierPowSMulRight (-innerSL ℝ)
        (𝓕 (markedMajorPlaneLift g : MarkedMajorFourierPlane → ℂ)) w n := by
  have hi (k : ℕ) : Integrable (iteratedFDeriv ℝ k (markedMajorPlaneLift g)) := by
    apply (integrable_norm_iff
      (((markedMajorPlaneLift g).smooth ⊤).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable).mp
    exact markedMajorPlaneLift_derivative_norm_integrable g k
  exact congrFun
    (Real.fourier_iteratedFDeriv ((markedMajorPlaneLift g).smooth ⊤) (fun k _ => hi k)
      (n := n) le_top) w

end
end ArtinMatthews
