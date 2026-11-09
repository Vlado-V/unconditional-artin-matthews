module

public import ArtinMatthews.VaryingKummerAnalyticHeckeConductorSieveDistinct
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Complex.RealDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! Gaussian mean-square estimates for actual general-field Hecke families.
The finite polynomial uses the genuine ideal norm and coefficient function.
The family sum is over distinct coefficient functions, exactly as in the
conductor large sieve.  Both the center of the height window and the vertical
line are arbitrary; at the source line `5/6` the Gaussian has unit real factor.
No zero-detection implication or power-saving premise is used here. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal MeasureTheory Complex
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

def heckeVerticalPhase (N σ t : ℝ) : ℂ :=
  Complex.exp (-((σ : ℂ) + (t : ℂ) * I) * (Real.log N : ℂ))

theorem heckeVerticalPhase_eq_cpow {N : ℝ} (hN : 0 < N) (σ t : ℝ) :
    heckeVerticalPhase N σ t = (N : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    ← Complex.ofReal_log hN.le]
  unfold heckeVerticalPhase
  congr 1
  ring

theorem norm_heckeVerticalPhase {N : ℝ} (hN : 0 < N) (σ t : ℝ) :
    ‖heckeVerticalPhase N σ t‖ = N ^ (-σ) := by
  rw [heckeVerticalPhase_eq_cpow hN,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp

theorem heckeVerticalPhase_continuous (N σ : ℝ) :
    Continuous (heckeVerticalPhase N σ) := by
  unfold heckeVerticalPhase
  fun_prop

theorem heckeVerticalPhase_hasDerivAt (N σ t : ℝ) :
    HasDerivAt (heckeVerticalPhase N σ)
      ((-I * (Real.log N : ℂ)) * heckeVerticalPhase N σ t) t := by
  have h := (((((hasDerivAt_id (t : ℂ)).mul_const I).const_add (σ : ℂ)).neg).mul_const
    (Real.log N : ℂ)).cexp.comp_ofReal
  simp only [Pi.neg_apply,id_eq,one_mul] at h
  exact h.congr_deriv (mul_comm _ _)

variable (K : Type*) [Field K] [NumberField K]

def coefficientClassDirichletPolynomial (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t : ℝ) : ℂ :=
  coefficientClassPolynomial K a B (fun c J => v c J *
    heckeVerticalPhase (FractionalIdeal.absNorm J.val.val : ℝ) σ t)

def coefficientClassDirichletMass
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ : ℝ) : ℝ :=
  ∑ c : ClassGroup (𝓞 K), ∑ J ∈ B c,
    (‖v c J‖ * (FractionalIdeal.absNorm J.val.val : ℝ)^(-σ))^2

theorem coefficientClassDirichletMass_nonneg
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ : ℝ) : 0 ≤ coefficientClassDirichletMass K B v σ := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coefficientClassDirichletPolynomial_continuous
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ : ℝ) : Continuous (coefficientClassDirichletPolynomial K a B v σ) := by
  unfold coefficientClassDirichletPolynomial coefficientClassPolynomial
  exact continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun J _ =>
    (continuous_const.mul (heckeVerticalPhase_continuous _ _)).mul continuous_const

theorem coefficientClassDirichletPolynomial_norm_le
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t : ℝ) :
    ‖coefficientClassDirichletPolynomial K a B v σ t‖ ≤
      ∑ c : ClassGroup (𝓞 K), ∑ J ∈ B c,
        ‖v c J‖ * (FractionalIdeal.absNorm J.val.val : ℝ)^(-σ) *
          ‖a ⟨J.val,J.property.1⟩‖ := by
  unfold coefficientClassDirichletPolynomial coefficientClassPolynomial
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro J _
  rw [norm_mul,norm_mul,norm_heckeVerticalPhase (fractionalIdeal_absNorm_pos J.val)]

def coefficientClassGaussianEnergy (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-2*t^2) *
    ‖coefficientClassDirichletPolynomial K a B v σ (t+t₀)‖^2

theorem coefficientClassGaussianEnergy_integrable
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-2*t^2) *
      ‖coefficientClassDirichletPolynomial K a B v σ (t+t₀)‖^2) := by
  let C := ∑ c : ClassGroup (𝓞 K), ∑ J ∈ B c,
    ‖v c J‖ * (FractionalIdeal.absNorm J.val.val : ℝ)^(-σ) *
      ‖a ⟨J.val,J.property.1⟩‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun J _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
      (fractionalIdeal_absNorm_pos J.val).le _)) (norm_nonneg _)
  have hg : Integrable (fun t : ℝ => Real.exp (-2*t^2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  apply (hg.mul_const (C^2)).mono'
  · exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-2*t^2))).mul
      (((coefficientClassDirichletPolynomial_continuous K a B v σ).comp
        (continuous_id.add continuous_const)).norm.pow 2)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact (sq_le_sq₀ (norm_nonneg _) hC).mpr
      (coefficientClassDirichletPolynomial_norm_le K a B v σ (t+t₀))

theorem coefficientClassGaussianEnergy_nonneg
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ : ℝ) : 0 ≤ coefficientClassGaussianEnergy K a B v σ t₀ :=
  integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- The actual ideal-conductor sieve on any vertical line and at any height. -/
theorem actualHecke_coefficientFamily_vertical_sieve
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
    (σ t : ℝ) :
    (∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
      ‖coefficientClassDirichletPolynomial K a B v σ t‖^2) ≤
      ((NumberField.classNumber K:ℝ) * heckeConductorClassConstant K * (X+U^2)) *
        coefficientClassDirichletMass K B v σ := by
  have H := actualHecke_coefficientFamily_conductor_sieve K hU hX T hT A hA B hB
    (fun c J => v c J * heckeVerticalPhase (FractionalIdeal.absNorm J.val.val : ℝ) σ t)
  simpa only [coefficientClassDirichletPolynomial,coefficientClassDirichletMass,
    norm_mul,norm_heckeVerticalPhase (fractionalIdeal_absNorm_pos _)] using H

/-- Gaussian integration preserves the sharp `X+U²` family bound, uniformly
in the center `t₀`. At `σ=5/6` this is exactly the squared source Gaussian. -/
theorem actualHecke_coefficientFamily_gaussian_sieve
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
      coefficientClassGaussianEnergy K a B v σ t₀) ≤
      Real.sqrt (Real.pi/2) *
        (((NumberField.classNumber K:ℝ) * heckeConductorClassConstant K * (X+U^2)) *
          coefficientClassDirichletMass K B v σ) := by
  let C := ((NumberField.classNumber K:ℝ) * heckeConductorClassConstant K * (X+U^2)) *
    coefficientClassDirichletMass K B v σ
  have hs : (∫ t : ℝ, ∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
      Real.exp (-2*t^2) * ‖coefficientClassDirichletPolynomial K a B v σ (t+t₀)‖^2) =
      ∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
        coefficientClassGaussianEnergy K a B v σ t₀ := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro M _
      exact integral_finsetSum _ fun a _ =>
        coefficientClassGaussianEnergy_integrable K a B v σ t₀
    · intro M _
      exact integrable_finsetSum _ fun a _ =>
        coefficientClassGaussianEnergy_integrable K a B v σ t₀
  rw [← hs]
  calc
    _ ≤ ∫ t : ℝ, Real.exp (-2*t^2) * C := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun t => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
      · exact (integrable_exp_neg_mul_sq (b := 2) (by norm_num)).mul_const C
      · filter_upwards [] with t
        simp only [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (actualHecke_coefficientFamily_vertical_sieve K hU hX T hT A hA B hB v σ (t+t₀))
          (Real.exp_pos _).le
    _ = _ := by rw [integral_mul_const,integral_gaussian]

end
end ArtinMatthews.VaryingKummerAnalytic
