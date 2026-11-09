module

public import ArtinMatthews.SpectralABLDyadicDerivative
public import ArtinMatthews.SpectralABLOppositeCosine


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped ContDiff
noncomputable section

private theorem spectralDyadic_tsupport_iteratedDeriv (g : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j g) ⊆ tsupport g := by
  induction j with
  | zero => simp only [iteratedDeriv_zero,Subset.rfl]
  | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- The compact spatial derivative masses in the shifted K contour are
uniform on the source dyadic support. -/
theorem spectralABLDyadicDivMass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Z M : ℝ) (f : ℝ → ℂ),
      0 < X → 1 ≤ Z → X ≤ Z → 0 ≤ M → ContDiff ℝ ∞ f →
      tsupport f ⊆ Icc X (2*X) →
      (∀ j ≤ 3, ∀ x ∈ Icc X (2*X), (X/Z)^j*‖iteratedDeriv j f x‖ ≤ M) →
      let g := spectralKLPhysicalCompactDiv f
      (∫ x : ℝ, ‖g x‖)+(X/Z)^3*(∫ x : ℝ, ‖iteratedDeriv 3 g x‖) ≤ C*M := by
  let φ : ℝ → ℂ := fun x => (x : ℂ)⁻¹
  have hφ : ContDiffOn ℝ ∞ φ (Ioi (0 : ℝ)) := by
    exact Complex.ofRealCLM.contDiff.contDiffOn.inv (fun x hx => Complex.ofReal_ne_zero.mpr
      (show 0 < x from hx).ne')
  obtain ⟨D,hD,hprod⟩ := spectralDyadic_scaled_mul_deriv_bound φ hφ 3
  refine ⟨2*D,by positivity,?_⟩
  intro X Z M f hX hZ hXZ hM hf hsup hF
  let b := X/Z
  let g := spectralKLPhysicalCompactDiv f
  have hb : 0 < b := div_pos hX (zero_lt_one.trans_le hZ)
  have hbX : b ≤ X := div_le_self hX.le hZ
  have hpos : tsupport f ⊆ Ioi (0 : ℝ) := fun x hx => hX.trans_le (hsup hx).1
  have hg := spectralKLPhysicalCompactDiv_smooth f hf hpos
  have hsupg : tsupport g ⊆ Icc X (2*X) := (spectralKLPhysicalCompactDiv_tsupport f).trans hsup
  have hgEq : g = fun x => (X : ℂ)⁻¹*(φ (x/X)*f x) := by
    funext x
    change f x/(x : ℂ) = (X : ℂ)⁻¹*((((x/X : ℝ) : ℂ)⁻¹)*f x)
    rw [Complex.ofReal_div,inv_div]
    simp only [div_eq_mul_inv]
    calc
      _ = (f x*(x : ℂ)⁻¹)*((X : ℂ)⁻¹*(X : ℂ)) := by
        rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hX.ne'),mul_one]
      _ = _ := by ring
  have hbound (j : ℕ) (hj : j ≤ 3) (x : ℝ) (hx : x ∈ Icc X (2*X)) :
      b^j*‖iteratedDeriv j g x‖ ≤ D*M/X := by
    rw [hgEq,iteratedDeriv_const_mul_field,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hX.le]
    calc
      _ = X⁻¹*(b^j*‖iteratedDeriv j (fun x => φ (x/X)*f x) x‖) := by ring
      _ ≤ X⁻¹*(D*M) := mul_le_mul_of_nonneg_left (hprod X b M f hX hb.le hbX hM hf hF j hj x hx)
        (inv_nonneg.mpr hX.le)
      _ = _ := by ring
  have hmass (j : ℕ) (hj : j ≤ 3) :
      b^j*(∫ x : ℝ, ‖iteratedDeriv j g x‖) ≤ D*M := by
    have hs := (spectralDyadic_tsupport_iteratedDeriv g j).trans hsupg
    have hi : Integrable (fun x : ℝ => ‖iteratedDeriv j g x‖) :=
      (((hg.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport
        (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs)) :
        Integrable (iteratedDeriv j g)).norm
    have hm : IntegrableOn (fun _ : ℝ => D*M/X) (Icc X (2*X)) :=
      integrableOn_const (isCompact_Icc.measure_lt_top (μ := volume)).ne
    rw [← integral_const_mul,← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Icc X (2*X)) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx')),norm_zero,mul_zero])]
    calc
      _ ≤ ∫ x in Icc X (2*X), D*M/X :=
        integral_mono_ae (hi.const_mul _).restrict hm (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          exact hbound j hj x hx)
      _ = _ := by
        rw [setIntegral_const,smul_eq_mul,Measure.real,Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*X-X)]
        field_simp [hX.ne'] <;> ring
  have h0 := hmass 0 (by decide)
  have h3 := hmass 3 (by decide)
  simp only [pow_zero,one_mul,iteratedDeriv_zero] at h0
  change (∫ x : ℝ, ‖g x‖)+b^3*(∫ x : ℝ, ‖iteratedDeriv 3 g x‖) ≤ _
  linarith

end
end ArtinMatthews
