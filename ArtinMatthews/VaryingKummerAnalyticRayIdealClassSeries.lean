module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
public import ArtinMatthews.VaryingKummerAnalyticRayIdealFixedCoefficients
public import ArtinMatthews.VaryingKummerAnalyticRayClassSeries
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyBalanced


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine ideal-conductor series is a finite sum of unit-invariant
residue-weighted ideal-class series. The fixed integral representatives
are chosen at modulus one, so they do not depend on the conductor. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Set Filter
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem idealModuleIntegerElement_eq_integer (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    (idealModuleIntegerElement K I hI a : 𝓞 K) = idealIntegerElement I hI a := by
  apply NumberField.RingOfIntegers.coe_injective
  change ((idealModuleIntegerElement K I hI a).val : K) = (idealIntegerElement I hI a : K)
  rw [idealModuleIntegerElement_coe,idealIntegerElement_coe]

theorem idealModuleIntegerElement_unitAction (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) (z : (𝓞 K)ˣ) :
    idealModuleIntegerElement K I hI (idealElementUnitAction _ z a) =
      (z:𝓞 K) • idealModuleIntegerElement K I hI a := by
  apply Subtype.ext
  change (idealModuleIntegerElement K I hI (idealElementUnitAction _ z a):𝓞 K) =
    (z:𝓞 K)*(idealModuleIntegerElement K I hI a:𝓞 K)
  rw [idealModuleIntegerElement_eq_integer,idealModuleIntegerElement_eq_integer,
    idealIntegerElement_unitAction]

def idealModuleResidueElementWeight (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) : ℂ :=
  χ (idealResidueCoordinate I M hI hM (idealModuleIntegerElement K I hI a))

theorem idealModuleResidueElementWeight_unitAction (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) (z : (𝓞 K)ˣ) :
    idealModuleResidueElementWeight I M hI hM χ (idealElementUnitAction _ z a) =
      χ (Ideal.Quotient.mk M (z:𝓞 K)) * idealModuleResidueElementWeight I M hI hM χ a := by
  unfold idealModuleResidueElementWeight
  rw [idealModuleIntegerElement_unitAction,map_smul]
  change χ (Ideal.Quotient.mk M (z:𝓞 K) * _) = _
  rw [map_mul]

def idealModuleResidueCoefficient (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) : ℂ :=
  idealModuleResidueElementWeight I M hI hM χ (idealElementRepresentative _ J)

theorem idealModuleResidueCoefficient_eq_of_generator (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ, χ (Ideal.Quotient.mk M (z:𝓞 K)) = 1)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    idealModuleResidueCoefficient I M hI hM χ (relativeElementClassMap _ a) =
      idealModuleResidueElementWeight I M hI hM χ a := by
  obtain ⟨z,hz,_⟩ := exists_unique_unit_of_relativeElementClassMap_eq _
    (idealElementRepresentative _ (relativeElementClassMap _ a)) a
    (idealElementRepresentative_spec _ _)
  conv_rhs => rw [← hz,idealModuleResidueElementWeight_unitAction,hunit,one_mul]
  rfl

theorem idealModuleResidueElementWeight_norm_le_one (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    ‖idealModuleResidueElementWeight I M hI hM χ a‖ ≤ 1 := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  exact finiteMulChar_norm_le_one χ _

def idealModuleResidueDirichlet (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (s : ℂ) : ℂ :=
  ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
    idealModuleResidueCoefficient I M hI hM χ J * ((FractionalIdeal.absNorm J.1.val : ℝ):ℂ)^(-s)

theorem idealModuleResidueDirichlet_summable (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (χ : MulChar ((𝓞 K) ⧸ M) ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralIdealClassFiber (integralIdealFractionalUnit I hI) =>
      idealModuleResidueCoefficient I M hI hM χ J * ((FractionalIdeal.absNorm J.1.val : ℝ):ℂ)^(-s)) := by
  apply (mixedPartialDedekind_norm_summable K (integralIdealFractionalUnit I hI) hs).of_norm_bounded
  intro J
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
    (idealModuleResidueElementWeight_norm_le_one I M hI hM χ _)

namespace EvenIdealRayCharacter
variable {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)

theorem moduleResidueWeight_invariant (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) (z : (𝓞 K)ˣ) :
    idealModuleResidueElementWeight I M hI hM ψ.residue (idealElementUnitAction _ z a) =
      idealModuleResidueElementWeight I M hI hM ψ.residue a := by
  rw [idealModuleResidueElementWeight_unitAction,ψ.residue_unit,one_mul]

def partialDirichlet (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∑' J : integralIdealClassFiber I,
    ψ.coefficient ⟨J.val,J.property.1⟩ * ((FractionalIdeal.absNorm J.1.val : ℝ):ℂ)^(-s)

theorem exists_partialDirichlet_eq_moduleResidue (hM : M ≠ ⊥)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ s : ℂ,
      ψ.partialDirichlet (integralIdealFractionalUnit I hI) s =
        κ * idealModuleResidueDirichlet I M hI hM ψ.residue s := by
  obtain ⟨κ,hκ,h⟩ := ψ.exists_fixedIdeal_coefficient_residue hM I hI
  refine ⟨κ,hκ,fun s => ?_⟩
  unfold partialDirichlet idealModuleResidueDirichlet
  rw [← tsum_mul_left]
  apply tsum_congr
  intro J
  let a := idealModuleIntegerElement K I hI (idealElementRepresentative _ J)
  have ha : (a:𝓞 K) ≠ 0 := by
    rw [show (a:𝓞 K) = idealIntegerElement I hI (idealElementRepresentative _ J) from
      idealModuleIntegerElement_eq_integer I hI _]
    exact EvenRayCharacter.generator_integer_ne_zero I hI J
  have hprod : Ideal.span {(a:𝓞 K)} = I * EvenRayCharacter.underlyingIdeal ⟨J.val,J.property.1⟩ := by
    rw [show (a:𝓞 K) = idealIntegerElement I hI (idealElementRepresentative _ J) from
      idealModuleIntegerElement_eq_integer I hI _]
    exact EvenRayCharacter.generator_principal_product I hI J
  have H := h (EvenRayCharacter.underlyingIdeal ⟨J.val,J.property.1⟩)
    (EvenRayCharacter.underlyingIdeal_ne_bot _) a ha hprod
  have hu : integralIdealFractionalUnit (EvenRayCharacter.underlyingIdeal ⟨J.val,J.property.1⟩)
      (EvenRayCharacter.underlyingIdeal_ne_bot ⟨J.val,J.property.1⟩) = J.val :=
    EvenRayCharacter.underlyingIdeal_unit ⟨J.val,J.property.1⟩
  rw [hu] at H
  change ψ.coefficient ⟨J.val,J.property.1⟩ = κ * idealModuleResidueCoefficient I M hI hM ψ.residue J at H
  rw [H]
  ring

theorem dirichlet_eq_partial_class_sum {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = ∑ c : ClassGroup (𝓞 K),
      ψ.partialDirichlet (rayClassFractionalRepresentative K 1 c) s := by
  let F : integralFractionalIdeals K → ℂ := fun J =>
    ψ.coefficient J * ((FractionalIdeal.absNorm J.1.val : ℝ):ℂ)^(-s)
  have h := ((rayIdealClassPartitionEquiv K 1).summable_iff.mpr
    (ψ.dirichlet_summable hs)).tsum_sigma
  change (∑' x, F (rayIdealClassPartitionEquiv K 1 x)) = _ at h
  rw [(rayIdealClassPartitionEquiv K 1).tsum_eq F] at h
  simp only [tsum_fintype] at h
  exact h

theorem exists_dirichlet_eq_moduleResidue_class_sum (hM : M ≠ ⊥) :
    ∃ κ : ClassGroup (𝓞 K) → ℂ, (∀ c, ‖κ c‖ = 1) ∧ ∀ s : ℂ, 1 < s.re →
      ψ.dirichlet s = ∑ c : ClassGroup (𝓞 K), κ c *
        idealModuleResidueDirichlet (rayClassRepresentative K 1 c) M
          (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue s := by
  choose κ hκ heq using fun c : ClassGroup (𝓞 K) =>
    ψ.exists_partialDirichlet_eq_moduleResidue hM
      (rayClassRepresentative K 1 c) (rayClassRepresentative_ne_bot K 1 c)
  refine ⟨κ,hκ,fun s hs => ?_⟩
  rw [ψ.dirichlet_eq_partial_class_sum hs]
  apply Finset.sum_congr rfl
  intro c _
  exact heq c s

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
