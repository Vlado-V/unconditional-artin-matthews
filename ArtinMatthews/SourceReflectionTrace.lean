module

public import ArtinMatthews.KummerAngularOfReflected


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The actual source Weil condition contains every trace-bad place. -/
theorem sourceTraceBadPlaces_subset_of_weil
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) :
    traceBadPlaces F ⊆ sourceHilbertSet F S₀ :=
  fun _ hp => hBad (Finset.mem_union_left _ hp)

/-- Every finite set used by the twelfth-cyclotomic angular source includes the trace-bad places. -/
theorem angularReflectedSeed_trace_subset (J : Ideal (𝓞 F)) :
    traceBadPlaces F ⊆
      sourceHilbertSet F (VaryingKummerAnalytic.angularReflectedSeed F J) :=
  sourceTraceBadPlaces_subset_of_weil F _
    (VaryingKummerAnalytic.angularReflectedSeed_bad_subset F J)

end
end ArtinMatthews.SourceEulerAssembly
