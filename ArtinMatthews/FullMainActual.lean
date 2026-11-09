module

public import ArtinMatthews.FullMainOrdinaryActual
public import ArtinMatthews.SourceReflectionLiteralActual


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed ordinary cancellation and actual angular expansion prove
the original simultaneous primitive-root theorem. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField

theorem giantAngularSourceInput_actual : GiantAngularSourceInput := by
  intro q _ _ _
  let K := twelfthCyclotomicField q
  let hz := twelfthAngularRoot_isPrimitiveRoot q
  apply twelfthAngularSourceBounds_of_literal_expansions q
  · exact sourceReflectionLiteralExpansion_actual K hz (angularReflectedSeed K ⊤)
      (angularReflectedSeed_bad_subset K ⊤) (principalAngularTrivialRay K)
      top_ne_bot (angularReflectedSeed_cutoff_subset K ⊤)
  · intro J hJ ψ _ _ _ _
    exact sourceReflectionLiteralExpansion_actual K hz (angularReflectedSeed K J)
      (angularReflectedSeed_bad_subset K J) ψ hJ (angularReflectedSeed_cutoff_subset K J)

theorem main_result : FullMainStatement :=
  fullMainStatement_of_angular_input giantAngularSourceInput_actual

end ArtinMatthews
