module

public import ArtinMatthews.VaryingKummerAnalyticHeckeGaussianDetectorDerivative
public import ArtinMatthews.VaryingKummerAnalyticGaussianSobolev


set_option backward.privateInPublic true
@[expose] public section

/-! Actual large values anywhere in a unit height window.  The Sobolev
estimate uses the true vertical derivative, whose logarithmic coefficients
are fed back into the same conductor sieve.  All constants are explicit and
depend on the field alone; no large-value or zero-density estimate is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal MeasureTheory Complex
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem norm_source_centered_gaussian (σ t₀ t : ℝ) :
    ‖Complex.exp ((((σ : ℂ) + ((t+t₀ : ℝ) : ℂ) * I) -
      ((5/6 : ℂ) + (t₀ : ℂ) * I))^2)‖ =
      Real.exp ((σ-5/6)^2) * Real.exp (-t^2) := by
  have hlin : ((σ : ℂ) + ((t+t₀ : ℝ) : ℂ) * I) -
      ((5/6 : ℂ) + (t₀ : ℂ) * I) = ((σ-5/6 : ℝ) : ℂ) + (t : ℂ)*I := by
    push_cast
    ring
  rw [hlin,Complex.norm_exp,← Real.exp_add]
  congr 1
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

/-- The squared source Gaussian at the manuscript center `5/6` is exactly
the weight used in the actual coefficient-family energy estimate. -/
theorem coefficientClass_source_gaussian_energy
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (t₀ : ℝ) :
    (∫ t : ℝ, ‖Complex.exp ((((5/6 : ℂ) + ((t+t₀ : ℝ) : ℂ) * I) -
      ((5/6 : ℂ) + (t₀ : ℂ) * I))^2) *
        coefficientClassDirichletPolynomial K a B v (5/6) (t+t₀)‖^2) =
      coefficientClassGaussianEnergy K a B v (5/6) t₀ := by
  unfold coefficientClassGaussianEnergy
  apply integral_congr_ae
  filter_upwards [] with t
  have hn : ‖Complex.exp ((((5/6 : ℂ) + ((t+t₀ : ℝ) : ℂ) * I) -
      ((5/6 : ℂ) + (t₀ : ℂ) * I))^2)‖ = Real.exp (-t^2) := by
    simpa using norm_source_centered_gaussian (5/6) t₀ t
  rw [norm_mul,hn]
  rw [mul_pow,pow_two (Real.exp _),← Real.exp_add]
  congr 2
  ring

def heckeGaussianWindowConstant : ℝ :=
  (2 * Real.exp 8) * Real.sqrt (Real.pi/2) *
    ((NumberField.classNumber K : ℝ) * heckeConductorClassConstant K)

theorem heckeGaussianWindowConstant_pos : 0 < heckeGaussianWindowConstant K := by
  have hC := heckeConductorClassConstant_pos K
  have hclass : 0 < (NumberField.classNumber K : ℝ) := by
    exact_mod_cast NumberField.classNumber_pos K
  unfold heckeGaussianWindowConstant
  positivity

theorem coefficientClassDirichletPolynomial_norm_sq_le_gaussian_energy
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ : ℝ) {t : ℝ} (ht : |t-t₀| ≤ 1) :
    ‖coefficientClassDirichletPolynomial K a B v σ t‖^2 ≤
      (2 * Real.exp 8) * (coefficientClassGaussianEnergy K a B v σ t₀ +
        coefficientClassGaussianDerivativeEnergy K a B v σ t₀) := by
  let F : ℝ → ℂ := fun u => coefficientClassDirichletPolynomial K a B v σ (u+t₀)
  let F' : ℝ → ℂ := fun u =>
    coefficientClassDirichletPolynomial K a B (coefficientClassLogWeight K v) σ (u+t₀)
  have hd (u : ℝ) : HasDerivAt F (F' u) u := by
    have hs : HasDerivAt (fun y : ℝ => y+t₀) 1 u := by
      simpa only [id_eq] using (hasDerivAt_id u).add_const t₀
    simpa only [F,F',one_smul,Function.comp_def] using
      (coefficientClassDirichletPolynomial_hasDerivAt K a B v σ (u+t₀)).scomp u hs
  have hc : Continuous F' :=
    (coefficientClassDirichletPolynomial_continuous K a B (coefficientClassLogWeight K v) σ).comp
      (continuous_id.add continuous_const)
  have h0 := coefficientClassGaussianEnergy_integrable K a B v σ t₀
  have h1 := coefficientClassGaussianEnergy_integrable K a B (coefficientClassLogWeight K v) σ t₀
  have hi : Integrable (fun u : ℝ => Real.exp (-2*u^2) * (‖F u‖^2+‖F' u‖^2)) := by
    exact (h0.add h1).congr (Filter.Eventually.of_forall fun u => by dsimp [F,F']; ring)
  have H := norm_sq_le_gaussian_derivative_energy hd hc hi ht
  simp only [F,sub_add_cancel] at H
  rw [coefficientClassGaussianDerivativeEnergy_eq]
  convert H using 1
  unfold coefficientClassGaussianEnergy
  rw [← integral_add h0 h1]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by dsimp [F,F']; ring

theorem actualHecke_coefficientFamily_gaussian_sobolev_sieve
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ : ℝ) :
    (∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
      (coefficientClassGaussianEnergy K a B v σ t₀ +
        coefficientClassGaussianDerivativeEnergy K a B v σ t₀)) ≤
      (Real.sqrt (Real.pi/2) *
        ((NumberField.classNumber K:ℝ) * heckeConductorClassConstant K * (X+U^2))) *
          ((1+(Real.log X)^2) * coefficientClassDirichletMass K B v σ) := by
  rw [show (∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
      (coefficientClassGaussianEnergy K a B v σ t₀ +
        coefficientClassGaussianDerivativeEnergy K a B v σ t₀)) =
      (∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
        coefficientClassGaussianEnergy K a B v σ t₀) +
      (∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
        coefficientClassGaussianDerivativeEnergy K a B v σ t₀) by
        simp only [Finset.sum_add_distrib]]
  apply (add_le_add
    (actualHecke_coefficientFamily_gaussian_sieve K hU hX T hT A hA B hB v σ t₀)
    (actualHecke_coefficientFamily_gaussian_derivative_sieve K hU hX T hT A hA B hB v σ t₀)).trans_eq
  ring

/-- A genuine maximal height-window bound, with the large-value set defined
by the actual finite Hecke polynomial rather than supplied as a hypothesis. -/
theorem actualHecke_coefficientFamily_unit_window_count
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ δ : ℝ) (hδ : 0 < δ) :
    (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
      (fun a => ∃ t : ℝ, |t-t₀| ≤ 1 ∧
        δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)).card : ℝ) ≤
      (heckeGaussianWindowConstant K * (X+U^2) * (1+(Real.log X)^2) *
        coefficientClassDirichletMass K B v σ) / δ^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  let E := fun a : integralFractionalIdeals K → ℂ =>
    coefficientClassGaussianEnergy K a B v σ t₀ +
      coefficientClassGaussianDerivativeEnergy K a B v σ t₀
  have hEn (a : integralFractionalIdeals K → ℂ) : 0 ≤ E a := by
    dsimp [E]
    rw [coefficientClassGaussianDerivativeEnergy_eq]
    exact add_nonneg (coefficientClassGaussianEnergy_nonneg K a B v σ t₀)
      (coefficientClassGaussianEnergy_nonneg K a B (coefficientClassLogWeight K v) σ t₀)
  have hsub :
      (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
        (fun a => ∃ t : ℝ, |t-t₀| ≤ 1 ∧
          δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)).card : ℝ) * δ^2 ≤
      (2 * Real.exp 8) * ∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient), E a := by
    rw [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro M _
    calc
      _ = ∑ a ∈ (((A M).image (fun ψ => ψ.coefficient)).filter
          (fun a => ∃ t : ℝ, |t-t₀| ≤ 1 ∧
            δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)), δ^2 := by simp
      _ ≤ ∑ a ∈ (((A M).image (fun ψ => ψ.coefficient)).filter
          (fun a => ∃ t : ℝ, |t-t₀| ≤ 1 ∧
            δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)),
          (2 * Real.exp 8) * E a := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨t,ht,hval⟩ := (Finset.mem_filter.mp ha).2
        exact ((sq_le_sq₀ hδ.le (norm_nonneg _)).mpr hval).trans
          (coefficientClassDirichletPolynomial_norm_sq_le_gaussian_energy K a B v σ t₀ ht)
      _ ≤ (2 * Real.exp 8) * ∑ a ∈ (A M).image (fun ψ => ψ.coefficient), E a := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun a _ _ => mul_nonneg (by positivity) (hEn a))
  apply hsub.trans
  have H := mul_le_mul_of_nonneg_left
    (actualHecke_coefficientFamily_gaussian_sobolev_sieve K hU hX T hT A hA B hB v σ t₀)
    (show 0 ≤ 2 * Real.exp 8 by positivity)
  convert H using 1
  unfold heckeGaussianWindowConstant
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
