module

public import ArtinMatthews.VaryingKummerAnalyticRayClassRepresentatives


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite ideal-class partition of the genuine ray Dirichlet series,
using the proved coprime integral representatives and residue coefficients. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField FractionalIdeal Set
open scoped NumberField nonZeroDivisors Classical BigOperators

variable (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]

/-- The exact class-fiber partition, using actual representatives coprime
to the actual modulus. The inverse convention agrees with relative ideals. -/
def rayIdealClassPartitionEquiv :
    (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K N c)) ≃
      integralFractionalIdeals K where
  toFun x := ⟨x.2.1, x.2.2.1⟩
  invFun J := ⟨(ClassGroup.mk K J.1)⁻¹,
    ⟨J.1, J.2, by rw [rayClassFractionalRepresentative_spec, inv_inv]⟩⟩
  left_inv := by
    rintro ⟨c, J⟩
    have h : (ClassGroup.mk K J.1)⁻¹ = c := by
      rw [J.2.2, rayClassFractionalRepresentative_spec, inv_inv]
    apply Sigma.ext h
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change (x.val ≤ 1 ∧ ClassGroup.mk K x =
        (ClassGroup.mk K (rayClassFractionalRepresentative K N ((ClassGroup.mk K J.val)⁻¹)))⁻¹) ↔ _
      rw [h])).mpr rfl
  right_inv _ := rfl

variable {K N}

/-- The literal residue-weighted partial ideal-class series. -/
def idealResidueDirichlet (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (s : ℂ) : ℂ :=
  ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
    idealResidueCoefficient I hI N χ J * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)

theorem idealResidueDirichlet_summable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralIdealClassFiber (integralIdealFractionalUnit I hI) =>
      idealResidueCoefficient I hI N χ J * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)) :=
  idealResidueCoefficient_summable I hI N χ hs

namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} (ψ : EvenRayCharacter K N)

def partialDirichlet (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∑' J : integralIdealClassFiber I,
    ψ.coefficient ⟨J.val, J.property.1⟩ * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)

theorem partialDirichlet_summable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralIdealClassFiber I =>
      ψ.coefficient ⟨J.val, J.property.1⟩ * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)) := by
  apply Summable.of_norm_bounded (mixedPartialDedekind_norm_summable K I hs)
  intro J
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _), Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
    (ψ.coefficient_norm_le_one ⟨J.val, J.property.1⟩)

/-- The exact coefficient identity gives equality of the literal class sums. -/
theorem partialDirichlet_eq_residue (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N)) (s : ℂ) :
    ψ.partialDirichlet (integralIdealFractionalUnit I hI) s =
      (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)⁻¹ *
        idealResidueDirichlet I hI N ψ.residue s := by
  unfold partialDirichlet idealResidueDirichlet
  rw [← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [ψ.coefficient_eq_residue I hI hcop J]
  ring

/-- Actual absolute convergence justifies the finite class partition. -/
theorem dirichlet_eq_partial_class_sum [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s =
      ∑ c : ClassGroup (𝓞 K), ψ.partialDirichlet (rayClassFractionalRepresentative K N c) s := by
  let F : integralFractionalIdeals K → ℂ := fun J =>
    ψ.coefficient J * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)
  have h := ((rayIdealClassPartitionEquiv K N).summable_iff.mpr
    (ψ.dirichlet_summable hs)).tsum_sigma
  change (∑' x, F (rayIdealClassPartitionEquiv K N x)) = _ at h
  rw [(rayIdealClassPartitionEquiv K N).tsum_eq F] at h
  simp only [tsum_fintype] at h
  exact h

/-- The actual arbitrary-field ray series is a finite weighted sum of actual
residue ideal-class series, with coprime representatives genuinely constructed. -/
theorem dirichlet_eq_residue_class_sum [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = ∑ c : ClassGroup (𝓞 K),
      (ψ.idealHom (rayClassFractionalRepresentative K N c) : ℂ)⁻¹ *
        idealResidueDirichlet (rayClassRepresentative K N c) (rayClassRepresentative_ne_bot K N c)
          N ψ.residue s := by
  rw [ψ.dirichlet_eq_partial_class_sum hs]
  apply Finset.sum_congr rfl
  intro c _
  exact ψ.partialDirichlet_eq_residue _ _ (rayClassRepresentative_coprime K N c) s

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
