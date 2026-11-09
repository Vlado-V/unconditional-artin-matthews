module

public import ArtinMatthews.VaryingKummerAnalyticMixedThetaPeriodicity


set_option backward.privateInPublic true
@[expose] public section

/-! Translation and reflection invariance of the actual Dirichlet-unit average.
The fundamental-domain comparison uses genuine unit periodicity. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- An affine reflection carries the actual unit domain to another fundamental
domain for exactly the same lattice. -/
theorem mixedUnitLogDomain_reflection_fundamental (c : logSpace K) :
    IsAddFundamentalDomain (unitLattice K)
      ((fun u : logSpace K => c-u) ⁻¹' mixedUnitLogDomain K) volume := by
  apply (mixedUnitLogDomain_fundamental K).preimage_of_equiv
    (volume.measurePreserving_sub_left c).quasiMeasurePreserving
    (e := fun g : unitLattice K => -g) (Equiv.neg _).bijective
  intro g u
  change c-((-g : unitLattice K) +ᵥ u) = g +ᵥ (c-u)
  change c-(-(g : logSpace K)+u) = (g : logSpace K)+(c-u)
  abel

/-- A periodic integrand has the same true unit average after any affine
reflection; no symmetry of the chosen half-open parallelotope is assumed. -/
theorem mixedUnitLogDomain_integral_reflection (f : logSpace K → ℂ)
    (hf : ∀ (g : unitLattice K) u, f ((g : logSpace K)+u) = f u)
    (c : logSpace K) :
    (∫ u in mixedUnitLogDomain K, f (c-u)) = ∫ u in mixedUnitLogDomain K, f u := by
  have : VAddInvariantMeasure (unitLattice K) (logSpace K) volume :=
    (inferInstance : VAddInvariantMeasure (unitLattice K).toAddSubgroup (logSpace K) volume)
  let S := ((fun u : logSpace K => c-u) ⁻¹' mixedUnitLogDomain K)
  have hS := mixedUnitLogDomain_reflection_fundamental K c
  have he : (∫ u in mixedUnitLogDomain K, f u) = ∫ u in S, f u :=
    (mixedUnitLogDomain_fundamental K).setIntegral_eq hS hf
  have hm : MeasurableEmbedding (fun u : logSpace K => c-u) :=
    (Homeomorph.subLeft c).measurableEmbedding
  have ht := (volume.measurePreserving_sub_left c).setIntegral_preimage_emb hm
    (fun u => f (c-u)) (mixedUnitLogDomain K)
  simp only [sub_sub_cancel] at ht
  exact ht.symm.trans he.symm

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The literal mixed ideal xi average is unchanged by the affine reflection
needed for the trace-dual Poisson transformation. -/
theorem mixedIdealUnitXi_reflection (c : logSpace K) (s : ℂ) :
    (∫ u in mixedUnitLogDomain K,
      thetaMellinXi (logScaledLattice (mixedIdealMatrix K I)
        (mixedIdealLogScale K I (c-u))) ((Module.finrank ℚ K : ℂ)*s/2)) =
      mixedIdealUnitXi K I s := by
  unfold mixedIdealUnitXi
  refine mixedUnitLogDomain_integral_reflection K
    (fun u => thetaMellinXi (logScaledLattice (mixedIdealMatrix K I)
      (mixedIdealLogScale K I u)) ((Module.finrank ℚ K : ℂ)*s/2)) ?_ c
  intro g u
  obtain ⟨z, hz⟩ := mixedUnitLogOnto_surjective K g
  have hg : logEmbedding K z = (g : logSpace K) := congrArg Subtype.val hz
  rw [← hg]
  exact mixedIdealFlowXi_unit_periodic K I z.toMul u _

end
end ArtinMatthews.VaryingKummerAnalytic
