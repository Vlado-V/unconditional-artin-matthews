module

public import ArtinMatthews.VaryingKummerAnalyticFiniteConductorEnergy
public import ArtinMatthews.VaryingKummerAnalyticIdealGaussFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Conductor-character energy on actual number-field ideal quotients. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) [NeZero M]
local instance idealConductorQuotient_finite : Finite ((𝓞 K) ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance idealConductorQuotient_fintype : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _

theorem ideal_conductor_character_energy {ι : Type*} (I : Finset ι)
    (n : ι → 𝓞 K) (a : ι → ℂ) (S : Finset (MulChar ((𝓞 K) ⧸ M) ℂ))
    (hS : ∀ χ ∈ S, IsPrimitiveOnIdeals χ) :
    (Ideal.absNorm M : ℝ) *
      (∑ χ ∈ S, ‖∑ i ∈ I, a i * χ (Ideal.Quotient.mk M (n i))‖ ^ 2) ≤
      (Fintype.card ((𝓞 K) ⧸ M)ˣ : ℝ) *
        ∑ u : ((𝓞 K) ⧸ M)ˣ,
          ‖∑ i ∈ I, a i * idealTraceAddChar K M (NeZero.ne M)
            (Ideal.Quotient.mk M (n i) * u)‖ ^ 2 := by
  simpa only [idealQuotient_card_eq_absNorm K M] using
    primitive_character_family_energy I (fun i => Ideal.Quotient.mk M (n i)) a S hS
      (idealTraceAddChar K M (NeZero.ne M)) (idealTraceAddChar_isPrimitive K M (NeZero.ne M))

theorem ideal_conductor_character_le_additive_energy {ι : Type*} (I : Finset ι)
    (n : ι → 𝓞 K) (a : ι → ℂ) (S : Finset (MulChar ((𝓞 K) ⧸ M) ℂ))
    (hS : ∀ χ ∈ S, IsPrimitiveOnIdeals χ) :
    (∑ χ ∈ S, ‖∑ i ∈ I, a i * χ (Ideal.Quotient.mk M (n i))‖ ^ 2) ≤
      ∑ u : ((𝓞 K) ⧸ M)ˣ,
        ‖∑ i ∈ I, a i * idealTraceAddChar K M (NeZero.ne M)
          (Ideal.Quotient.mk M (n i) * u)‖ ^ 2 :=
  primitive_character_family_le_additive_energy I (fun i => Ideal.Quotient.mk M (n i)) a S hS
    (idealTraceAddChar K M (NeZero.ne M)) (idealTraceAddChar_isPrimitive K M (NeZero.ne M))

end
end ArtinMatthews.VaryingKummerAnalytic
