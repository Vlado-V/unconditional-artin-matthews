module

public import ArtinMatthews.ArtinRayFaithfulEulerLocal
public import ArtinMatthews.ArtinAbelianGlobalEuler
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The exact faithful norm-conductor ray series is the full Artin
Euler product, with all finite local factors retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField AbelianLocal OAI.PrimeDegreePackets
open scoped NumberField Classical BigOperators
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] [IsTotallyComplex K]

theorem abelianNormConductorRayCharacter_dirichlet_eq_artin
    (χ : Gal(L/K) →* ℂˣ) (hχ : Function.Injective χ) {s : ℂ} (hs : 1 < s.re) :
    (abelianNormConductorRayCharacter K L χ).dirichlet s =
      abelianArtinEulerProduct K L χ s := by
  let ψ := abelianNormConductorRayCharacter K L χ
  have hf : (fun p : Nat.Primes => abelianArtinRationalFactor K L χ p s) =
      (fun p : Nat.Primes => ∏ P : idealsOverPrime K (p : ℕ), (1 - ψ.idealTerm hs P.val)⁻¹) := by
    funext p
    unfold abelianArtinRationalFactor
    apply Finset.prod_congr rfl
    intro P _
    rw [ψ.idealTerm_apply hs P.val]
    exact abelianNormConductorRayCharacter_localFactor χ hχ (primeOverHeightOne K p P) s
  have ha := abelianArtinEulerProduct_hasProd K L χ hs
  rw [hf] at ha
  exact (ψ.dirichlet_hasProd hs).unique ha

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
