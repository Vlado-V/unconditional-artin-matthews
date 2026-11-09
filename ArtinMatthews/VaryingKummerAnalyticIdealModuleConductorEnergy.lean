module

public import ArtinMatthews.VaryingKummerAnalyticFiniteConductorEnergy
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyLabels


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive residue-character energy on an arbitrary fixed ideal, reduced
to its actual trace-frequency energy without a coprimality assumption. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) [NeZero M]
local instance idealModuleConductorQuotient_finite : Finite ((𝓞 K) ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance idealModuleConductorQuotient_fintype : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _

theorem idealModule_conductor_character_le_additive_energy {ι : Type*}
    (B : Finset ι) (n : ι → I) (a : ι → ℂ)
    (S : Finset (MulChar ((𝓞 K) ⧸ M) ℂ)) (hS : ∀ χ ∈ S, IsPrimitiveOnIdeals χ) :
    (∑ χ ∈ S, ‖∑ i ∈ B, a i * χ (idealResidueCoordinate I M hI (NeZero.ne M) (n i))‖^2) ≤
      ∑ u : ((𝓞 K) ⧸ M)ˣ, ‖∑ i ∈ B, a i *
        idealModuleTraceChar K I (idealModuleFrequencyValue K I M hI (NeZero.ne M) u) (n i)‖^2 := by
  have H := primitive_character_family_le_additive_energy B
    (fun i => idealResidueCoordinate I M hI (NeZero.ne M) (n i)) a S hS
    (idealTraceAddChar K M (NeZero.ne M)) (idealTraceAddChar_isPrimitive K M (NeZero.ne M))
  simpa only [idealModuleFrequencyValue_character,mul_comm] using H

end
end ArtinMatthews.VaryingKummerAnalytic
