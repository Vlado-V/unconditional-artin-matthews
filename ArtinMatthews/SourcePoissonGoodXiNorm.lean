module

public import ArtinMatthews.SourcePoissonGoodXiMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Integrate the three actual classes of good-row errors separately.
The central vertical integral uses full Gaussian mass, the two finite
horizontal sides cost their real width, and the right tail uses the
full translated Gaussian moment after its cutoff factor is extracted. -/
namespace ArtinMatthews.SourcePhysical
open Set MeasureTheory VaryingKummerAnalytic
noncomputable section

local notation "μwt" => Measure.prod (volume : Measure ℝ) (volume : Measure ℝ)

def sourcePoissonHeightMomentMass (n : ℕ) : ℝ :=
  ∫ p, sourcePoissonHeightMoment n p ∂sourcePoissonHeightMeasure

theorem sourcePoissonHeightMomentMass_nonneg (n : ℕ) : 0 ≤ sourcePoissonHeightMomentMass n :=
  integral_nonneg (sourcePoissonHeightMoment_nonneg n)

def sourcePoissonHorizontalMass (n : ℕ) : ℝ :=
  (∫ y : ℝ, sourceContourHeightWeight y)*sourceGaussianPolynomialMoment n

theorem sourcePoissonHorizontalMass_nonneg (n : ℕ) : 0 ≤ sourcePoissonHorizontalMass n :=
  mul_nonneg (integral_nonneg sourceContourHeightWeight_nonneg) (sourceGaussianPolynomialMoment_nonneg n)

private theorem sourcePoissonVertical_integrable_norm_le
    (f : SourcePoissonHeights → ℂ) (s : Set ℝ) (hs : MeasurableSet s)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (hf : ContinuousOn f (univ ×ˢ s))
    (h : ∀ p, p.2 ∈ s → ‖f p‖ ≤ C*sourcePoissonHeightMoment n p) :
    Integrable f (sourcePoissonHeightRestrict s) ∧
      ‖∫ p, f p ∂sourcePoissonHeightRestrict s‖ ≤ C*sourcePoissonHeightMomentMass n := by
  let g := fun p => C*sourcePoissonHeightMoment n p
  have hg : Integrable g sourcePoissonHeightMeasure := (sourcePoissonHeightMoment_integrable n).const_mul C
  have hg' : Integrable g (sourcePoissonHeightRestrict s) := by rw [sourcePoissonHeightRestrict_eq]; exact hg.restrict
  refine ⟨sourcePoissonHeightRestrict_integrable_of_majorant s hs f g hf hg' h, ?_⟩
  calc
    _ ≤ ∫ p, g p ∂sourcePoissonHeightRestrict s := sourcePoissonHeightRestrict_integral_norm_le s hs f g hg' h
    _ ≤ ∫ p, g p ∂sourcePoissonHeightMeasure := sourcePoissonHeightRestrict_integral_le_full s g hg
      (fun p => mul_nonneg hC (sourcePoissonHeightMoment_nonneg n p))
    _ = _ := by rw [sourcePoissonHeightMomentMass]; exact integral_const_mul C _

private theorem sourcePoissonHorizontal_integrable_norm_le
    (f : SourcePoissonHeights → ℂ) {a b x : ℝ} (hab : a ≤ b)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (hf : ContinuousOn f (univ ×ˢ Ioc a b))
    (h : ∀ p, p.2 ∈ Ioc a b → ‖f p‖ ≤ C*sourcePoissonHeightMoment n (p.1,x)) :
    Integrable f (sourcePoissonHeightRestrict (Ioc a b)) ∧
      ‖∫ p, f p ∂sourcePoissonHeightRestrict (Ioc a b)‖ ≤ C*sourcePoissonHorizontalMass n*(b-a) := by
  let g (wt : ℝ×ℝ) := C*sourcePoissonHeightMoment n (wt,x)
  have hg : Integrable g μwt := (sourcePoissonHeightMoment_horizontal_integrable n x).const_mul C
  have hg' := sourcePoissonHeightRestrict_Ioc_fst_integrable (a := a) (b := b) g hg
  refine ⟨sourcePoissonHeightRestrict_integrable_of_majorant _ measurableSet_Ioc f _ hf hg' h, ?_⟩
  calc
    _ ≤ ∫ p, g p.1 ∂sourcePoissonHeightRestrict (Ioc a b) :=
      sourcePoissonHeightRestrict_integral_norm_le _ measurableSet_Ioc f _ hg' h
    _ = (∫ wt, g wt ∂μwt)*(b-a) := sourcePoissonHeightRestrict_Ioc_fst_mass hab g
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hab)
      dsimp only [g, sourcePoissonHorizontalMass]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (sourcePoissonHeightMoment_horizontal_mass n x) hC

theorem sourcePoissonFiniteXi_integral_norm_le
    (K : ℂ → (ℝ×ℝ) → ℂ) {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    (n : ℕ) (L H R : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLc : ContinuousOn (sourcePoissonXiVerticalKernel K a) (univ ×ˢ Ioc (-T) T))
    (hHc : ∀ x : ℝ, x = -T ∨ x = T → ContinuousOn (sourcePoissonXiHorizontalKernel K x) (univ ×ˢ Ioc a b))
    (hRc : ContinuousOn (sourcePoissonXiVerticalKernel K b) (univ ×ˢ (Ioc (-T) T)ᶜ))
    (hLb : ∀ p, p.2 ∈ Ioc (-T) T → ‖sourcePoissonXiVerticalKernel K a p‖ ≤ L*sourcePoissonHeightMoment 0 p)
    (hHb : ∀ x : ℝ, x = -T ∨ x = T → ∀ p, p.2 ∈ Ioc a b →
      ‖sourcePoissonXiHorizontalKernel K x p‖ ≤ H*sourcePoissonHeightMoment n (p.1,x))
    (hRb : ∀ p, p.2 ∈ (Ioc (-T) T)ᶜ → ‖sourcePoissonXiVerticalKernel K b p‖ ≤ R*sourcePoissonHeightMoment n p) :
    ‖∫ wt : ℝ×ℝ, finiteVerticalIntegral (fun ξ => K ξ wt) a T +
        finiteHorizontalError (fun ξ => K ξ wt) a b T + rightVerticalTail (fun ξ => K ξ wt) b T ∂μwt‖ ≤
      L*sourcePoissonHeightMomentMass 0 + 2*(H*sourcePoissonHorizontalMass n*(b-a)) +
        R*sourcePoissonHeightMomentMass n := by
  obtain ⟨iL, bL⟩ := sourcePoissonVertical_integrable_norm_le _ _ measurableSet_Ioc 0 L hL hLc hLb
  obtain ⟨iB, bB⟩ := sourcePoissonHorizontal_integrable_norm_le _ hab n H hH (hHc (-T) (Or.inl rfl))
    (hHb (-T) (Or.inl rfl))
  obtain ⟨iH, bH⟩ := sourcePoissonHorizontal_integrable_norm_le _ hab n H hH (hHc T (Or.inr rfl))
    (hHb T (Or.inr rfl))
  obtain ⟨iR, bR⟩ := sourcePoissonVertical_integrable_norm_le _ _ measurableSet_Ioc.compl n R hR hRc hRb
  rw [sourcePoissonFiniteXi_parts_integral K hab hT iL iB iH iR]
  let l := ∫ p, sourcePoissonXiVerticalKernel K a p ∂sourcePoissonHeightRestrict (Ioc (-T) T)
  let btm := ∫ p, sourcePoissonXiHorizontalKernel K (-T) p ∂sourcePoissonHeightRestrict (Ioc a b)
  let top := ∫ p, sourcePoissonXiHorizontalKernel K T p ∂sourcePoissonHeightRestrict (Ioc a b)
  let tail := ∫ p, sourcePoissonXiVerticalKernel K b p ∂sourcePoissonHeightRestrict (Ioc (-T) T)ᶜ
  change ‖l+Complex.I*(btm-top)+tail‖ ≤ _
  calc
    _ ≤ ‖l+Complex.I*(btm-top)‖+‖tail‖ := norm_add_le _ _
    _ ≤ (‖l‖+(‖btm‖+‖top‖))+‖tail‖ := by
      apply add_le_add _ le_rfl
      exact (norm_add_le _ _).trans (by rw [norm_mul, Complex.norm_I, one_mul]; exact add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ _ := by
      have h := add_le_add (add_le_add bL (add_le_add bB bH)) bR
      exact h.trans_eq (by ring)

end
end ArtinMatthews.SourcePhysical
