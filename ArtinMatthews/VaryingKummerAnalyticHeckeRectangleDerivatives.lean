module

public import ArtinMatthews.VaryingKummerAnalyticHeckeGaussianDetectorDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! Both real derivatives of the actual coefficient polynomial. These
identities allow the pinned two-variable row estimate to be used over an
arbitrary number field. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Complex
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

theorem heckeVerticalPhase_sigma_hasDerivAt (N σ t : ℝ) :
    HasDerivAt (fun x : ℝ => heckeVerticalPhase N x t)
      (-(Real.log N : ℂ)*heckeVerticalPhase N σ t) σ := by
  have h := (((hasDerivAt_id (σ : ℂ)).add_const ((t : ℂ)*I)).neg.mul_const
    (Real.log N : ℂ)).cexp.comp_ofReal
  simpa only [heckeVerticalPhase,Pi.neg_apply,id_eq,one_mul,neg_one_mul,mul_comm] using h

variable (K : Type*) [Field K] [NumberField K]

def coefficientClassRealLogWeight
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (c : ClassGroup (𝓞 K))
    (J : integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) : ℂ :=
  (Real.log (FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)*v c J

theorem coefficientClassDirichletPolynomial_joint_continuous
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    Continuous (Function.uncurry (coefficientClassDirichletPolynomial K a B v)) := by
  unfold Function.uncurry coefficientClassDirichletPolynomial coefficientClassPolynomial heckeVerticalPhase
  apply continuous_finsetSum
  intro c _
  apply continuous_finsetSum
  intro J _
  fun_prop

theorem coefficientClassDirichletPolynomial_sigma_hasDerivAt
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t : ℝ) :
    HasDerivAt (fun x : ℝ => coefficientClassDirichletPolynomial K a B v x t)
      (-coefficientClassDirichletPolynomial K a B (coefficientClassRealLogWeight K v) σ t) σ := by
  have h := HasDerivAt.fun_sum (x := σ) (u := Finset.univ) (fun c _ =>
    HasDerivAt.fun_sum (u := B c) (fun J _ =>
      ((heckeVerticalPhase_sigma_hasDerivAt (FractionalIdeal.absNorm J.val.val : ℝ) σ t).const_mul
        (v c J)).mul_const (a ⟨J.val,J.property.1⟩)))
  convert h using 1
  · rfl
  · unfold coefficientClassDirichletPolynomial coefficientClassPolynomial coefficientClassRealLogWeight
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J _
    ring

theorem coefficientClassDirichletPolynomial_reflected_hasDerivAt
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t : ℝ) :
    HasDerivAt (fun y : ℝ => coefficientClassDirichletPolynomial K a B v σ (-y))
      (I*coefficientClassDirichletPolynomial K a B (coefficientClassRealLogWeight K v) σ (-t)) t := by
  have h := (coefficientClassDirichletPolynomial_hasDerivAt K a B v σ (-t)).scomp t
    ((hasDerivAt_id t).neg)
  convert h using 1
  · rfl
  · simp only [neg_one_smul]
    unfold coefficientClassDirichletPolynomial coefficientClassPolynomial coefficientClassRealLogWeight
      coefficientClassLogWeight
    rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J _
    ring

theorem coefficientClassDirichletMass_antitone
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    Antitone (coefficientClassDirichletMass K B v) := by
  intro σ τ hστ
  unfold coefficientClassDirichletMass
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro J _
  have hN := integralFractionalIdeals_absNorm_ge_one ⟨J.val,J.property.1⟩
  gcongr

theorem coefficientClassRealLogWeight_mass_le
    {X : ℝ} (hX : 1 ≤ X)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ : ℝ) :
    coefficientClassDirichletMass K B (coefficientClassRealLogWeight K v) σ ≤
      (Real.log X)^2*coefficientClassDirichletMass K B v σ := by
  convert coefficientClassLogWeight_mass_le K hX B hB v σ using 1
  unfold coefficientClassDirichletMass coefficientClassRealLogWeight coefficientClassLogWeight
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro J _
  simp only [norm_mul,norm_neg,norm_I,one_mul]

theorem coefficientClassRealLogWeight_iterate_mass_le
    {X : ℝ} (hX : 1 ≤ X)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ : ℝ) (n : ℕ) :
    coefficientClassDirichletMass K B ((coefficientClassRealLogWeight K)^[n] v) σ ≤
      ((Real.log X)^2)^n*coefficientClassDirichletMass K B v σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (coefficientClassRealLogWeight_mass_le K hX B hB _ σ).trans
      (by simpa [pow_succ,mul_assoc,mul_left_comm] using
        mul_le_mul_of_nonneg_left ih (sq_nonneg (Real.log X)))

end
end ArtinMatthews.VaryingKummerAnalytic
