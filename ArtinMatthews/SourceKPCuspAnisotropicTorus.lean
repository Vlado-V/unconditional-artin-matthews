module

public import ArtinMatthews.SourceKPCuspHorizontalSymbol
public import ArtinMatthews.UnitTorusDerivativeCombination


set_option backward.privateInPublic true
@[expose] public section

/-! Anisotropic Fourier energy on the actual scaled Minkowski torus. -/
namespace ArtinMatthews
open NumberField Module Module.Free MeasureTheory UnitAddTorus
open scoped NumberField Classical BigOperators ENNReal
noncomputable section

local instance sourceKPCuspAnisotropicCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sourceKPCuspAnisotropicCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0) [IsTotallyComplex K]
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

def sourceKPCuspTorusHorizontalGradient (g : I → UnitTorusL2 I)
    (v : InfinitePlace K) (k : Fin 2) : UnitTorusL2 I :=
  unitTorusDerivativeCombination I g
    (sourceKPCuspCoordinates K d hd (sourceKPCuspHorizontalDirection K v k))

theorem sourceKPCuspTorusHorizontalGradient_fourier
    (f : UnitTorusL2 I) (g : I → UnitTorusL2 I) (hg : UnitTorusWeakGradient I f g)
    (v : InfinitePlace K) (k : Fin 2) (n : I → ℤ) :
    mFourierCoeff (sourceKPCuspTorusHorizontalGradient K d hd g v k) n =
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (sourceKPCuspTraceFunctional K (sourceKPCuspTraceFrequency K d n)
          (sourceKPCuspHorizontalDirection K v k) : ℂ)) * mFourierCoeff f n := by
  rw [sourceKPCuspTorusHorizontalGradient, unitTorusDerivativeCombination_fourier I f g hg,
    ← sourceKPCuspTraceFunctional_coordinates K d hd n (sourceKPCuspHorizontalDirection K v k)]

theorem sourceKPCuspTorusHorizontalGradient_coefficient_energy
    (f : UnitTorusL2 I) (g : I → UnitTorusL2 I) (hg : UnitTorusWeakGradient I f g)
    (y : InfinitePlace K → ℝ) (n : I → ℤ) :
    (∑ v, y v ^ 2 * ∑ k : Fin 2,
      ‖mFourierCoeff (sourceKPCuspTorusHorizontalGradient K d hd g v k) n‖ ^ 2) =
      sourceKPCuspHorizontalSymbol K (sourceKPCuspTraceFrequency K d n) y * ‖mFourierCoeff f n‖ ^ 2 := by
  unfold sourceKPCuspHorizontalSymbol
  simp_rw [sourceKPCuspTorusHorizontalGradient_fourier K d hd f g hg]
  simp only [norm_mul, mul_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_mul]
  ring

theorem sourceKPCuspTorus_anisotropic_poincare
    (f : UnitTorusL2 I) (g : I → UnitTorusL2 I) (hg : UnitTorusWeakGradient I f g)
    (hm : (∫ x, f x ∂unitTorusHaar I) = 0)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspHorizontalGap K d y * ‖f‖ ^ 2 ≤
      ∑ v, y v ^ 2 * ∑ k : Fin 2, ‖sourceKPCuspTorusHorizontalGradient K d hd g v k‖ ^ 2 := by
  have hsum : HasSum (fun n : I → ℤ => ∑ v, y v ^ 2 * ∑ k : Fin 2,
      ‖mFourierCoeff (sourceKPCuspTorusHorizontalGradient K d hd g v k) n‖ ^ 2)
      (∑ v, y v ^ 2 * ∑ k : Fin 2, ‖sourceKPCuspTorusHorizontalGradient K d hd g v k‖ ^ 2) :=
    hasSum_sum fun v _ => (hasSum_sum fun k _ =>
      unitTorus_fourier_parseval_norm I (sourceKPCuspTorusHorizontalGradient K d hd g v k)).mul_left (y v ^ 2)
  apply hasSum_le _ ((unitTorus_fourier_parseval_norm I f).mul_left
    (sourceKPCuspHorizontalGap K d y)) hsum
  intro n
  rw [sourceKPCuspTorusHorizontalGradient_coefficient_energy K d hd f g hg]
  by_cases hn : n = 0
  · subst n
    rw [unitTorus_fourier_zero I f, hm]
    simp
  · exact mul_le_mul_of_nonneg_right (sourceKPCuspHorizontalSymbol_lower K d hd y hy hn)
      (sq_nonneg _)

theorem sourceKPCuspTorus_anisotropic_height_poincare
    (f : UnitTorusL2 I) (g : I → UnitTorusL2 I) (hg : UnitTorusWeakGradient I f g)
    (hm : (∫ x, f x ∂unitTorusHaar I) = 0)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspHorizontalGapConstant K d * (∏ v, y v ^ 2) ^
        (1 / (InfinitePlace.nrComplexPlaces K : ℝ)) * ‖f‖ ^ 2 ≤
      ∑ v, y v ^ 2 * ∑ k : Fin 2, ‖sourceKPCuspTorusHorizontalGradient K d hd g v k‖ ^ 2 := by
  rw [← sourceKPCuspHorizontalGap_height]
  exact sourceKPCuspTorus_anisotropic_poincare K d hd f g hg hm y hy

end
end ArtinMatthews
