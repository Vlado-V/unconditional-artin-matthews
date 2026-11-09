module

public import ArtinMatthews.StandardWeilHilbertProducts


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical complex sign of the actual transported local pairing is
the same sign as its global finite-place factor. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open ArtinMatthews.QuadraticGauss
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem finiteQuadraticHilbertSign_eq_local (a b : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    finiteQuadraticHilbertSign F a b v = rootSign (v.adicCompletion F)
      (finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F) v
        (powerClass (v.adicCompletion F) 2 (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a))
        (powerClass (v.adicCompletion F) 2 (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b))) := by
  let C := v.adicCompletion F
  let e : rootsOfUnity 2 F ≃* rootsOfUnity 2 C :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F C).injective (numberFieldQuadraticRoots F)
  let z : rootsOfUnity 2 C := finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F) v
    (powerClass C 2 (Units.map (algebraMap F C).toMonoidHom a))
    (powerClass C 2 (Units.map (algebraMap F C).toMonoidHom b))
  change rootSign F (e.symm z) = rootSign C z
  exact rootSign_eq_of_one_iff _ _ e.symm.map_eq_one_iff

end

end ArtinMatthews.QuadraticWeil
