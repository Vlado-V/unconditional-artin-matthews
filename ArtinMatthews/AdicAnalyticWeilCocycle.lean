module

public import ArtinMatthews.AdicAnalyticWeil
public import ArtinMatthews.QuadraticHilbertNormSign
public import ArtinMatthews.AnalyticWeilSquareClasses


set_option backward.privateInPublic true
@[expose] public section

/-! Actual tame adic analytic Weil cocycle with a transported genuine
Hilbert pairing. The character is arbitrary conductor zero; its residue
Gauss comparison and the pairing sign are both derived. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance adicCocycleCharZero : CharZero (v.adicCompletion F) :=
  charZero_of_injective_ringHom (algebraMap F (v.adicCompletion F)).injective
local instance adicCocycleMeasurable : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance adicCocycleBorel : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem adicAnalyticWeil_cocycle (ψ : AddChar (v.adicCompletion F) ℂ)
    (hψ : adicConductorZero F v ψ) (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
    (htwo : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1)
    (B : HilbertPairing (v.adicCompletion F) 2) (hB : B.IsLocalHilbertPairing)
    (a b : (v.adicCompletion F)ˣ) :
    analyticNormalizedWeil ψ a * analyticNormalizedWeil ψ b =
      rootSign (v.adicCompletion F)
        (B (powerClass (v.adicCompletion F) 2 a) (powerClass (v.adicCompletion F) 2 b)) *
      analyticNormalizedWeil ψ (a * b) := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ValuativeRel C := adicRelation F v
  let : IsNonarchimedeanLocalField C := adicLocalField F v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  have h2 : ValuativeRel.valuation C (2 : C) = 1 := by
    have hrel : (2 : C) =ᵥ (1 : C) := (Valuation.veq_iff_eq ν).mpr (by simpa only [map_one] using htwo)
    simpa only [map_one] using (Valuation.veq_iff_eq (ValuativeRel.valuation C)).mp hrel
  let μ := tamePrimitiveRoots C h2
  let χ := conductorResidueChar C ψ hψ
  have hcmp (x : Cˣ) : analyticNormalizedWeil ψ x = localTameGaussSection C χ x :=
    adic_normalizedAnalyticWeil_eq_tame F v ψ hψ hu hc htwo x
  calc
    _ = localTameGaussSection C χ a * localTameGaussSection C χ b :=
      congrArg₂ (· * ·) (hcmp a) (hcmp b)
    _ = localQuadraticHilbert C h2 μ a b * localTameGaussSection C χ (a * b) :=
      localTameGaussSection_cocycle C h2 μ χ (conductorResidueChar_nontrivial C ψ hψ) a b
    _ = _ := congrArg₂ (· * ·) (localQuadraticHilbert_eq_pairingSign C h2 μ B hB a b) (hcmp (a * b)).symm

end

end ArtinMatthews.QuadraticWeil
