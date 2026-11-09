module

public import ArtinMatthews.SpectralUnitBeta


set_option backward.privateInPublic true
@[expose] public section

/-! The exact u -> exp(-u) substitution from the positive half-line to
the unit interval, including its absolute Jacobian and L1 equivalence. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralExpNeg_image_Ioi :
    (fun u : ℝ => Real.exp (-u)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨Real.exp_pos _,by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hu)⟩
  · intro ht
    refine ⟨-Real.log t,?_,?_⟩
    · have hlog : Real.log t < 0 := Real.log_neg ht.1 ht.2
      change 0 < -Real.log t
      linarith
    · simpa using Real.exp_log ht.1

theorem spectralExpNeg_integral (f : ℝ → ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, f t) =
      ∫ u in Ioi (0 : ℝ), (Real.exp (-u) : ℂ)*f (Real.exp (-u)) := by
  rw [← spectralExpNeg_image_Ioi]
  have hd (u : ℝ) (_hu : u ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) (Ioi (0 : ℝ)) u :=
    by simpa using! ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (-u)) (Ioi (0 : ℝ)) :=
    (Real.exp_injective.comp neg_injective).injOn
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only
  rw [abs_neg,abs_of_pos (Real.exp_pos _),Complex.real_smul]

theorem spectralExpNeg_integrable (f : ℝ → ℂ) :
    IntegrableOn f (Ioo (0 : ℝ) 1) ↔
      IntegrableOn (fun u : ℝ => (Real.exp (-u) : ℂ)*f (Real.exp (-u))) (Ioi (0 : ℝ)) := by
  rw [← spectralExpNeg_image_Ioi]
  have hd (u : ℝ) (_hu : u ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) (Ioi (0 : ℝ)) u :=
    by simpa using! ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (-u)) (Ioi (0 : ℝ)) :=
    (Real.exp_injective.comp neg_injective).injOn
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro u _
  dsimp only
  rw [abs_neg,abs_of_pos (Real.exp_pos _),Complex.real_smul]

end ArtinMatthews
