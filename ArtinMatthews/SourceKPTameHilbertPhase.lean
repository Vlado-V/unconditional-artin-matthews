module

public import ArtinMatthews.SourceKPUniformizerDecomposition
public import ArtinMatthews.SourceFiniteKPTameUnits
public import ArtinMatthews.SourceKubotaRationalProduct
public import ArtinMatthews.SourceAngularEmbedding


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine tame torus phase in valuation and unit coordinates.
The cubic roots are embedded in C by the inverse of the actual angular
embedding. This is the orientation fixed by the source torus phase. Unit-pair cancellation is the proved local CFT law. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AngularLambda
open scoped NumberField ValuativeRel
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceKPCentralComplex : rootsOfUnity 3 (P.adicCompletion K) →* ℂˣ :=
  (MulEquiv.inv ℂˣ).toMonoidHom.comp ((Units.map (sourceComplexEmbedding hζ).toMonoidHom).comp
    ((rootsOfUnity 3 K).subtype.comp (sourceKPRootsTransport K hζ P).symm.toMonoidHom))

theorem sourceKPCentralComplex_injective : Function.Injective (sourceKPCentralComplex K hζ P) :=
  (MulEquiv.inv ℂˣ).injective.comp ((Units.map_injective (sourceComplexEmbedding hζ).injective).comp
    (Subtype.val_injective.comp (sourceKPRootsTransport K hζ P).symm.injective))

theorem sourceKPCentralComplex_value (z : rootsOfUnity 3 (P.adicCompletion K)) :
    ((sourceKPCentralComplex K hζ P z : ℂˣ) : ℂ) =
      (sourceComplexEmbedding hζ ((((sourceKPRootsTransport K hζ P).symm z).val : Kˣ) : K))⁻¹ := by
  change (((Units.map (sourceComplexEmbedding hζ).toMonoidHom
    ((sourceKPRootsTransport K hζ P).symm z).val)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val, Units.coe_map]
  rfl

theorem sourceKPCentralComplex_cube (z : rootsOfUnity 3 (P.adicCompletion K)) :
    sourceKPCentralComplex K hζ P z ^ 3 = 1 := by
  rw [← map_pow, sourceCubicRoot_cube, map_one]

def sourceKPTameUniformizerCharacter (π : (P.adicCompletion K)ˣ) : (P.adicCompletion K)ˣ →* ℂˣ :=
  (sourceKPCentralComplex K hζ P).comp ((powMonoidHom 2).comp (sourceFiniteKPHilbert K hζ P π))

theorem sourceKPTameUniformizerCharacter_apply (π u : (P.adicCompletion K)ˣ) :
    sourceKPTameUniformizerCharacter K hζ P π u =
      sourceKPCentralComplex K hζ P (sourceFiniteKPHilbert K hζ P π u ^ 2) := by
  simp only [sourceKPTameUniformizerCharacter, MonoidHom.comp_apply, powMonoidHom_apply]

theorem sourceKPTameUniformizerCharacter_cube (π u : (P.adicCompletion K)ˣ) :
    sourceKPTameUniformizerCharacter K hζ P π u ^ 3 = 1 := by
  rw [sourceKPTameUniformizerCharacter_apply, sourceKPCentralComplex_cube]

private theorem sourceKP_zpow_square {A : Type*} [Group A] (u : A) (n : ℤ) :
    (u ^ n) ^ (2 : ℕ) = (u ^ (2 : ℕ)) ^ n := by
  rw [← zpow_natCast (u ^ n) 2, ← zpow_mul, ← zpow_natCast u 2, ← zpow_mul, mul_comm]

theorem sourceKPTameHilbert_phase (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (π : (P.adicCompletion K)ˣ) (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (y z : (P.adicCompletion K)ˣ) :
    sourceKPCentralComplex K hζ P (sourceFiniteKPHilbert K hζ P y z ^ 2) =
      sourceKPTameUniformizerCharacter K hζ P π (sourceKPUnitPart (sourceKPFiniteVal K P) π z) ^
        sourceKPValuationOrder (sourceKPFiniteVal K P) y *
      sourceKPTameUniformizerCharacter K hζ P π (sourceKPUnitPart (sourceKPFiniteVal K P) π y) ^
        (-sourceKPValuationOrder (sourceKPFiniteVal K P) z) := by
  let ν := sourceKPFiniteVal K P
  let H := sourceFiniteKPHilbert K hζ P
  let j := sourceKPValuationOrder ν y
  let k := sourceKPValuationOrder ν z
  let u := sourceKPUnitPart ν π y
  let v := sourceKPUnitPart ν π z
  have hu := sourceKPUnitPart_valuation ν π hπ y
  have hv := sourceKPUnitPart_valuation ν π hπ z
  have hππ : H π π = 1 := sourceFiniteKPHilbert_diag K hζ P π
  have huv : H u v = 1 := sourceFiniteKPHilbert_units K hζ P h6 u v hu hv
  have hskew : H u π = (H π u)⁻¹ := sourceFiniteKPHilbert_skew K hζ P u π
  have hsplit : H y z = H π v ^ j * H π u ^ (-k) := by
    calc
      _ = H (π ^ j * u) (π ^ k * v) := by
        rw [sourceKPUnitPart_factor ν π y, sourceKPUnitPart_factor ν π z]
      _ = _ := by
        simp only [map_mul, map_zpow, MonoidHom.mul_apply, MonoidHom.zpow_apply,
          hππ, one_zpow, one_mul, huv, mul_one, hskew, inv_zpow, zpow_neg]
        exact mul_comm _ _
  rw [sourceKPTameUniformizerCharacter_apply, sourceKPTameUniformizerCharacter_apply]
  let e := sourceKPCentralComplex K hζ P
  have hpow : H y z ^ (2 : ℕ) = (H π v ^ (2 : ℕ)) ^ j * (H π u ^ (2 : ℕ)) ^ (-k) := by
    calc
      _ = (H π v ^ j * H π u ^ (-k)) ^ (2 : ℕ) := congrArg (· ^ (2 : ℕ)) hsplit
      _ = (H π v ^ j) ^ (2 : ℕ) * (H π u ^ (-k)) ^ (2 : ℕ) := mul_pow _ _ _
      _ = _ := congrArg₂ (· * ·) (sourceKP_zpow_square (H π v) j) (sourceKP_zpow_square (H π u) (-k))
  calc
    _ = e ((H π v ^ (2 : ℕ)) ^ j * (H π u ^ (2 : ℕ)) ^ (-k)) := congrArg e hpow
    _ = _ := by rw [map_mul e, map_zpow e, map_zpow e]

end
end ArtinMatthews
