module

public import ArtinMatthews.SourcePoissonAngularOfReflected
public import ArtinMatthews.KummerAngularSourceBounds
public import ArtinMatthews.KummerCyclotomicTowerComplex


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain SourceEulerAssembly QuadraticWeil
open Filter Asymptotics OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- One actual finite starting set covers both the trace/Weil places and the
character cutoff. The completed Hilbert set can add the required places. -/
def angularReflectedSeed (J : Ideal (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 F)) :=
  standardWeilBadPlaces F ∪ principalAngularCutoff F J

theorem angularReflectedSeed_bad_subset (J : Ideal (𝓞 F)) :
    standardWeilBadPlaces F ⊆ sourceHilbertSet F (angularReflectedSeed F J) :=
  Finset.subset_union_left.trans (required_subset_sourceHilbertSet F _)

theorem angularReflectedSeed_cutoff_subset (J : Ideal (𝓞 F)) :
    principalAngularCutoff F J ⊆ sourceHilbertSet F (angularReflectedSeed F J) :=
  Finset.subset_union_right.trans (required_subset_sourceHilbertSet F _)

variable (q : ℕ) [NeZero q]
local notation "K" => twelfthCyclotomicField q
local notation "hz" => twelfthAngularRoot_isPrimitiveRoot q

/-- The literal reflected square moments on the cyclotomic fields
suffice for the actual principal/primitive Kummer zero-exclusion interface. -/
theorem twelfthAngularSourceBounds_of_reflected
    (hprincipal : SourcePoissonReflectedSecondMoment K (angularReflectedSeed K ⊤)
      hz (principalAngularTrivialRay K) (angularReflectedSeed_bad_subset K ⊤))
    (hprimitive : ∀ (J : Ideal (𝓞 K)) (_ : J ≠ ⊥) (ψ : EvenIdealRayCharacter K J),
      IsPrimitiveOnIdeals ψ.residue → ψ.IsNonprincipal →
      ψ.coefficient ≠ ψ.inverse.coefficient →
      Real.log (J.absNorm : ℝ) ≤ (12 * q : ℝ) * ((72 * (q : ℝ) ^ 2 + 2) * Real.log (12 * q)) →
      SourcePoissonReflectedSecondMoment K (angularReflectedSeed K J) hz ψ
        (angularReflectedSeed_bad_subset K J)) :
    TwelfthAngularSourceBounds q := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace K))
  constructor
  · refine ⟨sourceHilbertSet K (angularReflectedSeed K ⊤),
      angularReflectedSeed_cutoff_subset K ⊤, ?_⟩
    exact sourcePoissonAngularSignal_bound_of_reflected K (angularReflectedSeed K ⊤)
      hz (principalAngularTrivialRay K) v (angularReflectedSeed_bad_subset K ⊤) top_ne_bot
      (angularReflectedSeed_cutoff_subset K ⊤) hprincipal
  · intro J hJ ψ hprim hnp hreal hcond
    refine ⟨sourceHilbertSet K (angularReflectedSeed K J),
      angularReflectedSeed_cutoff_subset K J, ?_⟩
    exact sourcePoissonAngularSignal_bound_of_reflected K (angularReflectedSeed K J)
      hz ψ v (angularReflectedSeed_bad_subset K J) hJ (angularReflectedSeed_cutoff_subset K J)
      (hprimitive J hJ ψ hprim hnp hreal hcond)

end
end ArtinMatthews.VaryingKummerAnalytic
