module

public import ArtinMatthews.SLocalAnalyticWeil
public import ArtinMatthews.StandardWeilHilbertProducts


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite S-Hilbert product on diagonal global classes is the
literal product of the globally normalized finite Hilbert signs. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open ArtinMatthews.QuadraticGauss
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem sLocalHilbertSign_globalClass (S : Finset (HeightOneSpectrum (𝓞 F))) (a b : Fˣ) :
    rootSign F (sLocalHilbertForm F 2 (numberFieldQuadraticRoots F) S
      (sLocalGlobalClassMap F 2 S a) (sLocalGlobalClassMap F 2 S b)) =
      ∏ v : S, finiteQuadraticHilbertSign F a b v.1 := by
  let H : S → rootsOfUnity 2 F := fun v =>
    GlobalHilbertPairingFamily.finiteFactor F
      (finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F))
      (numberFieldQuadraticRoots F) v.1 a b
  change rootSign F (∏ v : S, H v) = ∏ v : S, rootSign F (H v)
  exact map_prod _ _ _

end

end ArtinMatthews.QuadraticWeil
