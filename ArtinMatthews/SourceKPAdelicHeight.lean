module

public import ArtinMatthews.SourceKPAdelicCompactIntersection
public import ArtinMatthews.SourceKPRationalHeightComplex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual adelic Iwasawa height, with the normalized complex
place multiplicities and all finite factors retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicHeight (g : GL (Fin 2) 𝔸[K]) : ℝ :=
  sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det (sourceKPAdelicIwasawaBorel K hζ g))

theorem sourceKPAdelicHeight_pos (g : GL (Fin 2) 𝔸[K]) : 0 < sourceKPAdelicHeight K hζ g :=
  sourceKPIdeleAbsoluteNorm_pos K _

theorem sourceKPAdelicFiniteCoordinate_det (g : GL (Fin 2) 𝔸[K])
    (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPIdeleFiniteCoordinate K P (GeneralLinearGroup.det g) =
      GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P g) := by
  apply Units.ext
  change (Matrix.det (g : Matrix (Fin 2) (Fin 2) 𝔸[K])).2 P =
    Matrix.det (sourceKPAdelicBaseFiniteAt K P g : Matrix (Fin 2) (Fin 2) (P.adicCompletion K))
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  rfl

theorem sourceKPAdelicComplexCoordinate_det (g : GL (Fin 2) 𝔸[K]) (v : InfinitePlace K) :
    sourceKPArchComplexEquiv K hζ v
      (sourceKPIdeleInfiniteCoordinate K v (GeneralLinearGroup.det g) : v.Completion) =
        (GeneralLinearGroup.det (sourceKPAdelicBaseComplexAt K hζ v g) : ℂ) := by
  change sourceKPArchComplexEquiv K hζ v
    ((Matrix.det (g : Matrix (Fin 2) (Fin 2) 𝔸[K])).1 v) =
      Matrix.det (sourceKPAdelicBaseComplexAt K hζ v g : Matrix (Fin 2) (Fin 2) ℂ)
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  change sourceKPArchComplexEquiv K hζ v
    ((g 0 0).1 v * (g 1 1).1 v - (g 0 1).1 v * (g 1 0).1 v) =
    sourceKPArchComplexEquiv K hζ v ((g 0 0).1 v) *
        sourceKPArchComplexEquiv K hζ v ((g 1 1).1 v) -
      sourceKPArchComplexEquiv K hζ v ((g 0 1).1 v) *
        sourceKPArchComplexEquiv K hζ v ((g 1 0).1 v)
  rw [map_sub, map_mul, map_mul]

theorem sourceKPAdelicHeight_product (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeight K hζ g =
      (∏ v : InfinitePlace K, sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v g) ^ v.mult) *
        ∏ᶠ P : HeightOneSpectrum (𝓞 K),
          ‖(GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P g) : P.adicCompletion K)‖ /
            max ‖sourceKPAdelicBaseFiniteAt K P g 1 0‖ ‖sourceKPAdelicBaseFiniteAt K P g 1 1‖ ^ 2 := by
  change ‖(sourceKPIdeleInfiniteUnit K (GeneralLinearGroup.det
      (sourceKPAdelicIwasawaBorel K hζ g)) : InfiniteAdeleRing K)‖ *
    ‖(sourceKPIdeleFiniteUnit K (GeneralLinearGroup.det
      (sourceKPAdelicIwasawaBorel K hζ g)) : 𝔸ᶠ[K])‖ = _
  rw [InfiniteAdeleRing.norm_def, FiniteAdeleRing.norm_eq_finprod_of_unit]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    change ‖(sourceKPIdeleInfiniteCoordinate K v (GeneralLinearGroup.det
      (sourceKPAdelicIwasawaBorel K hζ g)) : v.Completion)‖ ^ v.mult = _
    rw [← sourceKPArchComplexEquiv_norm K hζ v,
      sourceKPAdelicComplexCoordinate_det, sourceKPAdelicIwasawa_arch_torus_norm]
  · apply finprod_congr
    intro P
    change ‖(sourceKPIdeleFiniteCoordinate K P (GeneralLinearGroup.det
      (sourceKPAdelicIwasawaBorel K hζ g)) : P.adicCompletion K)‖ = _
    rw [sourceKPAdelicFiniteCoordinate_det, sourceKPAdelicIwasawa_finite_torus_norm]

end
end ArtinMatthews
