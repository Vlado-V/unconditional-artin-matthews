module

public import ArtinMatthews.SourceKPAdeleMultiplier


set_option backward.privateInPublic true
@[expose] public section

/-! The rational lift in the compact adelic section. Its phase is the
inverse of the finite product of local compact cochains. The sign
follows from the exact local change of section and cubic reciprocity. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPRationalLocalPhase (g : GL (Fin 2) K) (P : HeightOneSpectrum (𝓞 K)) : rootsOfUnity 3 K :=
  (sourceKPRootsTransport K hζ P).symm (sourceKPFinitePhase K hζ P
    (sourceKPAdeleMatrixAt K P (sourceKPRationalDiagonal K g)))

theorem sourceKPRationalLocalPhase_hasFiniteMulSupport (g : GL (Fin 2) K) :
    Function.HasFiniteMulSupport (sourceKPRationalLocalPhase K hζ g) := by
  apply Filter.eventually_cofinite.mp
  by_cases hg : g 1 0 = 0
  · apply Filter.Eventually.of_forall
    intro P
    have h0 : sourceKPAdeleMatrixAt K P (sourceKPRationalDiagonal K g) 1 0 = 0 := by
      rw [sourceKPAdeleMatrixAt_rational, GeneralLinearGroup.map_apply, hg, map_zero]
    rw [sourceKPRationalLocalPhase, sourceKPFinitePhase_zero_left K hζ P _ h0, map_one]
  · filter_upwards [sourceKPRational_eventually_unit K (g 1 0) hg] with P hP
    have hu : sourceKPFiniteVal K P (sourceKPAdeleMatrixAt K P (sourceKPRationalDiagonal K g) 1 0) = 1 := by
      rw [sourceKPAdeleMatrixAt_rational, GeneralLinearGroup.map_apply]
      exact hP
    rw [sourceKPRationalLocalPhase, sourceKPFinitePhase_unit_left K hζ P _ hu, map_one]

theorem sourceKPRationalLocalPhase_one (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPRationalLocalPhase K hζ 1 P = 1 := by
  rw [sourceKPRationalLocalPhase, map_one, map_one, sourceKPFinitePhase_one, map_one]

theorem sourceKPRationalLocalPhase_scalar (u : Kˣ) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPRationalLocalPhase K hζ (GeneralLinearGroup.scalar (Fin 2) u) P = 1 := by
  rw [sourceKPRationalLocalPhase, sourceKPAdeleMatrixAt_rational, GeneralLinearGroup.map_scalar,
    sourceKPFinitePhase_scalar, map_one]

theorem sourceKPAdeleLocalMultiplier_rational (g h : GL (Fin 2) K) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleLocalMultiplier K hζ (sourceKPRationalDiagonal K g) (sourceKPRationalDiagonal K h) P =
      sourceKPRationalLocalPhase K hζ g P * sourceKPRationalLocalPhase K hζ h P *
        sourceFiniteKP2RationalMultiplier K hζ g h P / sourceKPRationalLocalPhase K hζ (g * h) P := by
  rw [sourceKPAdeleLocalMultiplier, sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist,
    map_div, map_mul, map_mul, ← map_mul (sourceKPAdeleMatrixAt K P),
    ← map_mul (sourceKPRationalDiagonal K)]
  unfold sourceKPRationalLocalPhase sourceFiniteKP2RationalMultiplier
  rw [sourceKPAdeleMatrixAt_rational K P g, sourceKPAdeleMatrixAt_rational K P h]

def sourceKPRationalPhaseProduct (g : GL (Fin 2) K) : rootsOfUnity 3 K :=
  ∏ᶠ P, sourceKPRationalLocalPhase K hζ g P

theorem sourceKPAdeleMultiplier_rational (g h : GL (Fin 2) K) :
    sourceKPAdeleMultiplier K hζ (sourceKPRationalDiagonal K g) (sourceKPRationalDiagonal K h) =
      (sourceKPRationalPhaseProduct K hζ g * sourceKPRationalPhaseProduct K hζ h) /
        sourceKPRationalPhaseProduct K hζ (g * h) := by
  let A := sourceKPRationalLocalPhase K hζ g
  let B := sourceKPRationalLocalPhase K hζ h
  let C := sourceFiniteKP2RationalMultiplier K hζ g h
  let D := sourceKPRationalLocalPhase K hζ (g * h)
  have hA : Function.HasFiniteMulSupport A := sourceKPRationalLocalPhase_hasFiniteMulSupport K hζ g
  have hB : Function.HasFiniteMulSupport B := sourceKPRationalLocalPhase_hasFiniteMulSupport K hζ h
  have hC : Function.HasFiniteMulSupport C := sourceFiniteKP2RationalMultiplier_hasFiniteMulSupport K hζ g h
  have hD : Function.HasFiniteMulSupport D := sourceKPRationalLocalPhase_hasFiniteMulSupport K hζ (g * h)
  have habc : (∏ᶠ P, ((A * B) * C) P) =
      (∏ᶠ P, A P) * (∏ᶠ P, B P) * (∏ᶠ P, C P) := by
    calc
      _ = (∏ᶠ P, (A * B) P) * (∏ᶠ P, C P) := finprod_mul_distrib (hA.mul hB) hC
      _ = _ := congrArg (· * (∏ᶠ P, C P)) (finprod_mul_distrib hA hB)
  unfold sourceKPAdeleMultiplier sourceKPRationalPhaseProduct
  calc
    _ = ∏ᶠ P, A P * B P * C P / D P :=
      finprod_congr (sourceKPAdeleLocalMultiplier_rational K hζ g h)
    _ = (∏ᶠ P, ((A * B) * C) P) / (∏ᶠ P, D P) :=
      finprod_div_distrib ((hA.mul hB).mul hC) hD
    _ = ((∏ᶠ P, A P) * (∏ᶠ P, B P) * (∏ᶠ P, C P)) / (∏ᶠ P, D P) :=
      congrArg (· / (∏ᶠ P, D P)) habc
    _ = _ := by rw [sourceFiniteKP2RationalMultiplier_finprod K hζ g h, mul_one]

def sourceKPRationalLiftPhase (g : GL (Fin 2) K) : rootsOfUnity 3 K :=
  (sourceKPRationalPhaseProduct K hζ g)⁻¹

theorem sourceKPRationalLiftPhase_one : sourceKPRationalLiftPhase K hζ 1 = 1 := by
  simp only [sourceKPRationalLiftPhase, sourceKPRationalPhaseProduct, sourceKPRationalLocalPhase_one, finprod_one, inv_one]

theorem sourceKPRationalLiftPhase_scalar (u : Kˣ) :
    sourceKPRationalLiftPhase K hζ (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  simp only [sourceKPRationalLiftPhase, sourceKPRationalPhaseProduct, sourceKPRationalLocalPhase_scalar,
    finprod_one, inv_one]

theorem sourceKPRationalLiftPhase_mul (g h : GL (Fin 2) K) :
    sourceKPRationalLiftPhase K hζ (g * h) =
      sourceKPRationalLiftPhase K hζ g * sourceKPRationalLiftPhase K hζ h *
        sourceKPAdeleMultiplier K hζ (sourceKPRationalDiagonal K g) (sourceKPRationalDiagonal K h) := by
  rw [sourceKPAdeleMultiplier_rational]
  unfold sourceKPRationalLiftPhase
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

end
end ArtinMatthews
