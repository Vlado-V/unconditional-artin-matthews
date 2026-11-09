module

public import ArtinMatthews.SpectralMixedCuspPositiveWeilSum


set_option backward.privateInPublic true
@[expose] public section

/-! The actual same-cusp zero-modulus matrices are the two central signs
of every genuine width translation. This accounts for the factor two in
the zero sector before the Poincare unfolding multiplicity. -/

noncomputable section
open Matrix Set MeasureTheory
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

theorem spectral_SL2_lower_zero_eq_signed_translation (M : SL(2, ℤ)) (hM : M 1 0 = 0) :
    (M 1 1 = 1 ∧ M = integerTranslation (M 0 1)) ∨
      (M 1 1 = -1 ∧ M = -integerTranslation (-(M 0 1))) := by
  have hdet : M 0 0*M 1 1 = 1 := by
    simpa only [Matrix.det_fin_two,hM,mul_zero,sub_zero] using M.property
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨hA,hD⟩ | ⟨hA,hD⟩
  · refine Or.inl ⟨hD,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [integerTranslation,hA,hM,hD]
  · refine Or.inr ⟨hD,?_⟩
    ext i j
    change M i j = -((integerTranslation (-(M 0 1))) i j)
    fin_cases i <;> fin_cases j <;> simp [integerTranslation,hA,hM,hD]

def gamma0SameCuspZeroTranslation (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (p : Bool × ℤ) :
    {M : gamma0CuspCorrespondence N r r // M.val 1 0 = 0} := by
  let T := integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*p.2)
  have hT : T ∈ gamma0CuspCorrespondence N r r :=
    (gamma0CuspTrueWidth_translation_iff N r _).mpr (dvd_mul_right _ _)
  exact if p.1 then ⟨⟨T,hT⟩,rfl⟩ else
    ⟨⟨-T,(gamma0CuspCorrespondence_neg_iff N r r T).mpr hT⟩,by change -(0 : ℤ) = 0; simp⟩

theorem gamma0SameCuspZeroTranslation_val (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (p : Bool × ℤ) :
    (gamma0SameCuspZeroTranslation N r p).val.val =
      if p.1 then integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*p.2)
      else -integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*p.2) := by
  rcases p with ⟨b,k⟩
  cases b <;> rfl

theorem gamma0SameCuspZeroTranslation_bijective (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    Function.Bijective (gamma0SameCuspZeroTranslation N r) := by
  constructor
  · rintro ⟨p,k⟩ ⟨q,l⟩ h
    have he := congrArg (fun M => M.val.val) h
    rw [gamma0SameCuspZeroTranslation_val,gamma0SameCuspZeroTranslation_val] at he
    have hw : (gamma0CuspTrueWidth N r : ℤ) ≠ 0 := by exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'
    cases p <;> cases q <;> simp only [Bool.false_eq_true,ite_false,ite_true] at he
    · have hB := congrArg (fun M : SL(2, ℤ) => M 0 1) (neg_injective he)
      change (gamma0CuspTrueWidth N r : ℤ)*k = (gamma0CuspTrueWidth N r : ℤ)*l at hB
      exact Prod.ext rfl (mul_left_cancel₀ hw hB)
    · have hD := congrArg (fun M : SL(2, ℤ) => M 1 1) he
      change (-1 : ℤ) = 1 at hD
      omega
    · have hD := congrArg (fun M : SL(2, ℤ) => M 1 1) he
      change (1 : ℤ) = -1 at hD
      omega
    · have hB := congrArg (fun M : SL(2, ℤ) => M 0 1) he
      change (gamma0CuspTrueWidth N r : ℤ)*k = (gamma0CuspTrueWidth N r : ℤ)*l at hB
      exact Prod.ext rfl (mul_left_cancel₀ hw hB)
  · intro M
    rcases spectral_SL2_lower_zero_eq_signed_translation M.val.val M.property with ⟨_,h⟩ | ⟨_,h⟩
    · have hT : integerTranslation (M.val.val 0 1) ∈ gamma0CuspCorrespondence N r r :=
        h ▸ M.val.property
      obtain ⟨k,hk⟩ := (gamma0CuspTrueWidth_translation_iff N r _).mp hT
      refine ⟨(true,k),?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rw [gamma0SameCuspZeroTranslation_val,h,hk]
      rfl
    · have hT : -integerTranslation (-(M.val.val 0 1)) ∈ gamma0CuspCorrespondence N r r :=
        h ▸ M.val.property
      obtain ⟨k,hk⟩ := (gamma0CuspTrueWidth_translation_iff N r _).mp
        ((gamma0CuspCorrespondence_neg_iff N r r _).mp hT)
      refine ⟨(false,k),?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rw [gamma0SameCuspZeroTranslation_val,h,hk]
      rfl

theorem gamma0ZeroGeometricSum_sameCusp_translations (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (ψ φ : h2SmoothCompactSeeds) :
    gamma0ZeroGeometricSum N r r ψ φ =
      2*(∑ᶠ k : ℤ, compactPoincareGeometricKernel ψ φ (integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k))) := by
  classical
  let A := {M : gamma0CuspCorrespondence N r r // M.val 1 0 = 0}
  let F (M : gamma0CuspCorrespondence N r r) := compactPoincareGeometricKernel ψ φ M.val
  let e : Bool × ℤ ≃ A := Equiv.ofBijective (gamma0SameCuspZeroTranslation N r)
    (gamma0SameCuspZeroTranslation_bijective N r)
  have hI : Function.Injective (fun p : Bool × ℤ => (e p).val.val) :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.injective)
  have hF : Function.HasFiniteSupport (fun p : Bool × ℤ => F (e p).val) :=
    Function.HasFiniteSupport.fun_comp_of_injective (g := fun p => (e p).val.val) hI
      (compactPoincareGeometricKernel_all_hasFiniteSupport ψ φ)
  have hcond := finsum_subtype_eq_finsum_cond (f := F) (fun M => M.val 1 0 = 0)
  change (∑ᶠ M : A, F M.val) = ∑ᶠ M ∈ {M | M.val 1 0 = 0}, F M at hcond
  rw [finsum_mem_def] at hcond
  calc
    _ = ∑ᶠ M : A, F M.val := by
      rw [hcond]
      unfold gamma0ZeroGeometricSum
      apply finsum_congr
      intro M
      by_cases hM : M.val 1 0 = 0 <;> simp [hM,F]
    _ = ∑ᶠ p : Bool × ℤ, F (e p).val := (finsum_comp_equiv (f := fun M : A => F M.val) e).symm
    _ = _ := by
      rw [finsum_curry _ hF,finsum_eq_sum_of_fintype]
      have h (b : Bool) (k : ℤ) :
          F (e (b,k)).val = compactPoincareGeometricKernel ψ φ
            (integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) := by
        change compactPoincareGeometricKernel ψ φ (gamma0SameCuspZeroTranslation N r (b,k)).val.val = _
        rw [gamma0SameCuspZeroTranslation_val]
        cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,compactPoincareGeometricKernel_neg]
      simp_rw [h]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul,Nat.cast_ofNat]

end ArtinMatthews
