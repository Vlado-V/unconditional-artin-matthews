module

public import ArtinMatthews.SourcePrincipalContourAnalytic


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed principal strip and the actual distances from the two poles. -/

namespace ArtinMatthews.SourceEulerAssembly
open SourcePhysical Set
noncomputable section

theorem sourcePrincipalSigma_gt_one : (1 : ℝ) < sourcePrincipalSigma := by norm_num [sourcePrincipalSigma]
theorem sourcePrincipalSigma_le_four : sourcePrincipalSigma ≤ 4 := by norm_num [sourcePrincipalSigma]
theorem sourcePrincipalZetaLine_gt_sixth : (1 / 6 : ℝ) < sourcePrincipalZetaLine := by
  norm_num [sourcePrincipalZetaLine]
theorem sourcePrincipalZetaLine_mem : sourcePrincipalZetaLine ∈ Icc (16 / 100 : ℝ) 2 := by
  norm_num [sourcePrincipalZetaLine]

theorem sourcePrincipalVertical_w_gap_re (b t : ℝ) :
    |b - 1| ≤ ‖sourcePoissonVertical b t - 1‖ := by
  simpa only [Complex.sub_re, Complex.one_re, sourcePoissonVertical_re] using
    Complex.abs_re_le_norm (sourcePoissonVertical b t - 1)

theorem sourcePrincipalVertical_w_gap_im (b t : ℝ) :
    |t| ≤ ‖sourcePoissonVertical b t - 1‖ := by
  simpa only [Complex.sub_im, Complex.one_im, sub_zero, sourcePoissonVertical_im] using
    Complex.abs_im_le_norm (sourcePoissonVertical b t - 1)

theorem sourcePrincipalVertical_z_gap_re (c y : ℝ) :
    |6 * c - 1| ≤ ‖(6 : ℂ) * sourcePoissonVertical c y - 1‖ := by
  simpa [Complex.sub_re, Complex.mul_re] using
    Complex.abs_re_le_norm ((6 : ℂ) * sourcePoissonVertical c y - 1)

theorem sourcePrincipalVertical_z_gap_im (c y : ℝ) :
    6 * |y| ≤ ‖(6 : ℂ) * sourcePoissonVertical c y - 1‖ := by
  simpa [Complex.sub_im, Complex.mul_im, abs_mul] using
    Complex.abs_im_le_norm ((6 : ℂ) * sourcePoissonVertical c y - 1)

theorem sourcePrincipalVertical_w_ne_one {b : ℝ} (hb : b ≠ 1) (t : ℝ) :
    sourcePoissonVertical b t ≠ 1 := by
  intro h
  exact hb (by simpa only [sourcePoissonVertical_re, Complex.one_re] using congrArg Complex.re h)

theorem sourcePrincipalVertical_z_ne_sixth {c : ℝ} (hc : c ≠ 1 / 6) (y : ℝ) :
    sourcePoissonVertical c y ≠ 1 / 6 := by
  intro h
  apply hc
  simpa only [sourcePoissonVertical_re, show ((1 / 6 : ℂ)).re = 1 / 6 by norm_num [Complex.div_re]]
    using congrArg Complex.re h

theorem sourcePrincipalTripleScale_bounded {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ Icc sourcePrincipalSigma 4, ∀ b ∈ Icc (95 / 100 : ℝ) 4,
      ∀ c ∈ Icc (16 / 100 : ℝ) 2, sourcePoissonTripleScale X Y Z a b c ≤ B := by
  let D := Icc sourcePrincipalSigma 4 ×ˢ Icc (95 / 100 : ℝ) 4 ×ˢ Icc (16 / 100 : ℝ) 2
  let G (q : ℝ × ℝ × ℝ) := sourcePoissonTripleScale X Y Z q.1 q.2.1 q.2.2
  have hD : IsCompact D := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hG : Continuous G := by
    unfold G sourcePoissonTripleScale
    simp_rw [Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hY, Real.rpow_def_of_pos hZ]
    fun_prop
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max 0 B, le_max_left _ _, fun a ha b hb c hc => ?_⟩
  have h := hB (a, b, c) ⟨ha, hb, hc⟩
  exact (le_abs_self _).trans ((by simpa only [Real.norm_eq_abs, G] using h : |G (a,b,c)| ≤ B).trans
    (le_max_right _ _))

end
end ArtinMatthews.SourceEulerAssembly
