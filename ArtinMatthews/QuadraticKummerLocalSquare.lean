module

public import ArtinMatthews.QuadraticKummerGenerator
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm


set_option backward.privateInPublic true
@[expose] public section

/-! A local square parameter splits the actual quadratic radical field. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations LocalClassFieldTheory
open scoped NumberField Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 6)

include hζ

theorem quadraticKummer_finitePlaceSplitsCompletely_of_localSquare
    (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hsquare : ∃ s : v.adicCompletion F,
      s ^ 2 = algebraMap F (v.adicCompletion F) (u : F)) :
    FinitePlaceSplitsCompletely (K := F) (L := QuadraticKummerField u) v := by
  obtain ⟨s, hs⟩ := hsquare
  let L := QuadraticKummerField u
  let vF := HeightOneSpectrum.adicAbv F v
  let w := chosenFinitePlaceExtension (L := L) v
  let hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
  let : SMul F w.1.Completion := hF.toSMul
  let : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  let := localizedCompletionGlobalAlgebra vF w
  let := localizedCompletionIsScalarTower vF w
  let E := LocalizedCompletion vF w
  let e := finitePlaceCompletionAlgEquiv (K := F) v
  let t : vF.Completion := e.symm s
  have ht : t ^ 2 = algebraMap F vF.Completion (u : F) := by
    apply e.injective
    change e (e.symm s ^ 2) = e (algebraMap F vF.Completion (u : F))
    rw [map_pow, e.apply_symm_apply, e.commutes]
    exact hs
  let f := localizedCompletionToAlgHom vF w
  let beta : E := f (quadraticKummerRoot u)
  have hbeta : beta ^ 2 = (algebraMap vF.Completion E t) ^ 2 := by
    calc
      beta ^ 2 = f (quadraticKummerRoot u ^ 2) := (map_pow f _ _).symm
      _ = f (algebraMap F L (u : F)) := congrArg f (quadraticKummerRoot_sq u)
      _ = algebraMap vF.Completion E (algebraMap F vF.Completion (u : F)) :=
        AbsoluteValue.toAlgebraicLocalization_algebraMap vF w.1 w.2 _
      _ = (algebraMap vF.Completion E t) ^ 2 := by rw [← ht, map_pow]
  have hmem : beta ∈ (⊥ : IntermediateField vF.Completion E) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hbeta with hpos | hneg
    · exact ⟨t, hpos.symm⟩
    · exact ⟨-t, by rw [map_neg]; exact hneg.symm⟩
  have hbot : IntermediateField.adjoin vF.Completion {beta} = ⊥ :=
    IntermediateField.adjoin_simple_eq_bot_iff.mpr hmem
  have htop : IntermediateField.adjoin vF.Completion {beta} = ⊤ :=
    localizedCompletion_adjoin_image_eq_top_of_adjoin_eq_top vF w
      (quadraticKummerRoot u) (quadraticKummerRoot_adjoin hζ u)
  have hdegree : Module.finrank vF.Completion E = 1 := by
    have h := IntermediateField.finrank_eq_one_iff.mpr (htop.symm.trans hbot)
    simpa only [IntermediateField.finrank_top'] using h
  apply (finitePlaceSplitsCompletely_iff_localDegree_eq_one
    (K := F) (L := L) v).mpr
  exact hdegree

theorem quadraticKummer_localNormSubgroup_eq_top_of_localSquare
    (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hsquare : ∃ s : v.adicCompletion F,
      s ^ 2 = algebraMap F (v.adicCompletion F) (u : F)) :
    chosenFinitePlaceLocalNormSubgroup (K := F) (L := QuadraticKummerField u) v = ⊤ :=
  chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely v
    (quadraticKummer_finitePlaceSplitsCompletely_of_localSquare hζ u v hsquare)

end
end ArtinMatthews
