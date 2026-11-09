module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealClassSeries
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaDualClasses


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ideal-ray partial series depend only on their ideal class.
The conductor-twisted trace-dual representatives therefore give the full
inverse ray series after summing their genuine class permutation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

theorem partialDirichlet_eq_of_class_eq (F J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hclass : ClassGroup.mk K F = ClassGroup.mk K J) (s : ℂ) :
    ψ.partialDirichlet F s = ψ.partialDirichlet J s := by
  let e : integralIdealClassFiber F ≃ integralIdealClassFiber J :=
    Equiv.subtypeEquivRight (fun L => by rw [hclass])
  exact e.tsum_eq (fun L : integralIdealClassFiber J =>
    ψ.coefficient ⟨L.val,L.property.1⟩ * ((FractionalIdeal.absNorm L.val.val:ℝ):ℂ)^(-s))

theorem conductorDual_partial_class_sum (hM : M ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    (∑ c : ClassGroup (𝓞 K), ψ.partialDirichlet
      (mixedTraceDualIdeal K (mixedConductorIdeal K (rayClassRepresentative K 1 c) M
        (rayClassRepresentative_ne_bot K 1 c) hM)) s) = ψ.dirichlet s := by
  calc
    _ = ∑ c : ClassGroup (𝓞 K), ψ.partialDirichlet
        (rayClassFractionalRepresentative K 1 (mixedPrimitiveDualClassEquiv K M hM c)) s := by
      apply Finset.sum_congr rfl
      intro c _
      apply ψ.partialDirichlet_eq_of_class_eq
      rw [rayClassFractionalRepresentative_spec]
      have H := (mixedPrimitiveDualIntegralIdeal_class K M hM
        (rayClassRepresentative K 1 c) (rayClassRepresentative_ne_bot K 1 c)).symm.trans
        (mixedPrimitiveDualIntegralIdeal_class_permutation K M hM
          (rayClassRepresentative K 1 c) (rayClassRepresentative_ne_bot K 1 c))
      change _ = mixedPrimitiveDualClassEquiv K M hM
        (ClassGroup.mk K (rayClassFractionalRepresentative K 1 c)) at H
      rwa [rayClassFractionalRepresentative_spec] at H
    _ = ∑ c : ClassGroup (𝓞 K), ψ.partialDirichlet (rayClassFractionalRepresentative K 1 c) s :=
      (mixedPrimitiveDualClassEquiv K M hM).sum_comp
        (fun c => ψ.partialDirichlet (rayClassFractionalRepresentative K 1 c) s)
    _ = ψ.dirichlet s := (ψ.dirichlet_eq_partial_class_sum hs).symm

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
