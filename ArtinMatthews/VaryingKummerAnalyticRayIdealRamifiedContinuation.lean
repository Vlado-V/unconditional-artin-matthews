module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveIdealContinuation
public import ArtinMatthews.VaryingKummerAnalyticRayIdealClassSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ideal-conductor Hecke series with nontrivial residue character
continues to an entire function by its genuine finite class theta sum. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

def classThetaScalar (hM : M ≠ ⊥) : ClassGroup (𝓞 K) → ℂ :=
  (ψ.exists_dirichlet_eq_moduleResidue_class_sum hM).choose

theorem classThetaScalar_norm (hM : M ≠ ⊥) (c : ClassGroup (𝓞 K)) :
    ‖ψ.classThetaScalar hM c‖ = 1 :=
  (ψ.exists_dirichlet_eq_moduleResidue_class_sum hM).choose_spec.1 c

theorem dirichlet_eq_classThetaScalar_sum (hM : M ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = ∑ c : ClassGroup (𝓞 K), ψ.classThetaScalar hM c *
      idealModuleResidueDirichlet (rayClassRepresentative K 1 c) M
        (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue s :=
  (ψ.exists_dirichlet_eq_moduleResidue_class_sum hM).choose_spec.2 s hs

def ramifiedContinued (hM : M ≠ ⊥) (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K), ψ.classThetaScalar hM c *
    mixedPrimitiveIdealContinued K (rayClassRepresentative K 1 c) M
      (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue s

theorem ramifiedContinued_entire (hM : M ≠ ⊥) (hψ : ψ.residue ≠ 1) :
    Differentiable ℂ (ψ.ramifiedContinued hM) := by
  apply Differentiable.fun_sum
  intro c _
  exact (mixedPrimitiveIdealContinued_entire K _ M _ hM ψ.residue hψ).const_mul _

theorem ramifiedContinued_eq_dirichlet (hM : M ≠ ⊥) (hψ : ψ.residue ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : ψ.ramifiedContinued hM s = ψ.dirichlet s := by
  rw [ψ.dirichlet_eq_classThetaScalar_sum hM hs]
  unfold ramifiedContinued
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact mixedPrimitiveIdealContinued_eq_series K _ M _ hM ψ.residue hψ ψ.residue_unit hs

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
