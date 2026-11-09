module

public import ArtinMatthews.ShiftedBesselLogSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform log separation for both actual shifted-correlation source
weights. The arbitrary g-family is controlled by finitely many T-scale
derivatives; the second source is the constructed fixed plateau. -/

noncomputable section
open Complex MeasureTheory Set OAI
open scoped ContDiff

namespace ArtinMatthews

/-- The actual first-source Bessel kernel has a genuine separated integral
with polynomial height moments and dual-scale decay, uniformly in m,T. -/
theorem shiftedSourceTest_log_separation
    {ι : Type*} [Fintype ι]
    (V : ι → ℝ → ℂ) (a M : ι → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j) (A J : ℕ) :
    ∃ L : ℕ, ∀ Cg : ℝ, 0 ≤ Cg → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → ∀ (T m : ℝ), 0 < T → 0 < m →
        Function.support g ⊆ Icc T (2*T) → 1 ≤ m*T →
        (∀ n ≤ L, ∀ x : ℝ, ‖iteratedDeriv n g x‖ ≤ Cg/T^n) →
        ∀ R : ℝ, 0 < R → ∃ b : SchwartzMap ℝ ℂ,
          (∀ y : ι → ℝ, (∏ j : ι, V j (y j)) *
            weightOneBesselTransform (shiftedSourceTest g m) (R*Real.exp (∑ j : ι, a j*y j)) =
              ∫ t : ℝ, (∏ j : ι, V j (y j)*FourierBridge.logPhase t (a j*y j))*b t) ∧
          (1+(m*T)*R)^A * (∫ t : ℝ, (1+‖t‖)^J*‖b t‖) ≤ C*(m*T) := by
  obtain ⟨s,hsep⟩ := scaled_bessel_log_separation_source_bounds V a M hM hVwindow A J
  refine ⟨s.sup Prod.snd,?_⟩
  intro Cg hCg
  obtain ⟨C,hC,hb⟩ := hsep (3^(s.sup Prod.fst)*Cg) (by positivity)
  refine ⟨C,hC,?_⟩
  intro g hg T m hT hm hgs hscale hderiv R hR
  let W := shiftedSourceTranslate (normalizedSourceSchwartz g hg T hT hgs) (1/(m*T))
  have hs : s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ 3^(s.sup Prod.fst)*Cg := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro p hp
    exact (shiftedSourceTest_normalized_seminorm g hg T m Cg hT hgs hscale p.1 p.2 hCg
      (hderiv p.2 (Finset.le_sup hp))).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Finset.le_sup hp)) hCg)
  have hsource : (fun x : ℝ ↦ W (x/(m*T))) = shiftedSourceTest g m := by
    funext x
    exact (shiftedSourceTest_eq_normalized g hg T m hT hm hgs x).symm
  have hh := hb W 3 (by norm_num) (shiftedSourceTest_normalized_support g hg T m hT hgs hscale)
    hs (m*T) R (mul_pos hm hT) hR
  rw [hsource] at hh
  exact hh

/-- The actual second-source Bessel kernel enjoys the same uniform separated
integral without any free-cutoff derivative hypothesis. -/
theorem shiftedSourceMajorant_log_separation
    {ι : Type*} [Fintype ι]
    (V : ι → ℝ → ℂ) (a M : ι → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T m : ℝ), 0 < T → 0 < m → 1 ≤ m*T →
      ∀ R : ℝ, 0 < R → ∃ b : SchwartzMap ℝ ℂ,
        (∀ y : ι → ℝ, (∏ j : ι, V j (y j)) *
          weightOneBesselTransform (shiftedSourceMajorant m T) (R*Real.exp (∑ j : ι, a j*y j)) =
            ∫ t : ℝ, (∏ j : ι, V j (y j)*FourierBridge.logPhase t (a j*y j))*b t) ∧
        (1+(m*T)*R)^A * (∫ t : ℝ, (1+‖t‖)^J*‖b t‖) ≤ C*(m*T) := by
  obtain ⟨s,hsep⟩ := scaled_bessel_log_separation_source_bounds V a M hM hVwindow A J
  let C0 : ℝ := ∑ p ∈ s, (7/2 : ℝ)^p.1 * SchwartzMap.seminorm ℝ 0 p.2 sourcePlateauSchwartz
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  obtain ⟨C,hC,hb⟩ := hsep C0 hC0
  refine ⟨C,hC,?_⟩
  intro T m hT hm hscale R hR
  let W := shiftedSourceTranslate sourcePlateauSchwartz (1/(m*T))
  have hδ : 1/(m*T) ∈ Icc 0 1 := ⟨by positivity,(div_le_one (mul_pos hm hT)).mpr hscale⟩
  have hsupport : Function.support sourcePlateauSchwartz ⊆ Icc 0 (5/2) :=
    shiftedSourcePlateau_support.trans (by intro y hy; exact ⟨by linarith [hy.1],hy.2⟩)
  have hs : s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ C0 := by
    apply Seminorm.finset_sup_apply_le hC0
    intro p hp
    have ht := shiftedSourceTranslate_seminorm sourcePlateauSchwartz (5/2) (1/(m*T))
      (by norm_num) hsupport hδ p.1 p.2
    norm_num only [show (5/2 : ℝ)+1=7/2 by norm_num] at ht
    apply ht.trans
    exact Finset.single_le_sum
      (f := fun p : ℕ × ℕ ↦ (7/2 : ℝ)^p.1 * SchwartzMap.seminorm ℝ 0 p.2 sourcePlateauSchwartz)
      (fun i _ ↦ by positivity) hp
  have hsource : (fun x : ℝ ↦ W (x/(m*T))) = shiftedSourceMajorant m T := by
    funext x
    exact (shiftedSourceMajorant_eq_normalized m T x).symm
  have hh := hb W (7/2) (by norm_num) (shiftedSourceMajorant_normalized_support m T hscale)
    hs (m*T) R (mul_pos hm hT) hR
  rw [hsource] at hh
  exact hh

end ArtinMatthews
