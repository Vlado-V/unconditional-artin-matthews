module

public import ArtinMatthews.SourceKPCuspProductCoordinates
public import ArtinMatthews.SourceKPCuspFourierCell
public import ArtinMatthews.SourceKPCompactTruncatedChart
public import ArtinMatthews.SourceKPCompactChartMassLift


set_option backward.privateInPublic true
@[expose] public section

/-! The native Minkowski cusp chart is the literal adelic upper
translate of a fixed-finite height section. -/
namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet SourceHyperbolicGreen Module.Free
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

private theorem sourceCuspUpperSection_translate (z : ℂ) (y : ℝ) (hy : 0 < y) :
    sourceKPUpperMatrix ℂ z * (upperSection 0 y hy : GL (Fin 2) ℂ) =
      (upperSection z y hy : GL (Fin 2) ℂ) := by
  have hentry (w : ℂ) (i j : Fin 2) : (upperSection w y hy : Matrix (Fin 2) (Fin 2) ℂ) i j =
      !![(Real.sqrt y : ℂ), w / (Real.sqrt y : ℂ); 0, (Real.sqrt y : ℂ)⁻¹] i j := rfl
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two,hentry,div_eq_mul_inv]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)

local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K

def sourceKPCuspHeightPoint (y : V → ℝ) : ProductSpace V :=
  fun v => WithLp.toLp 2 ![0,0,y v]

theorem sourceKPCuspHeightPoint_positive (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    ∀ v, 0 < sourceKPCuspHeightPoint K y v 2 := hy

def sourceKPCuspHeightSection (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    PGL(2,InfiniteAdeleRing K) :=
  ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ (sourceKPCuspHeightPoint K y) hy)

theorem sourceKPCuspNativeUpperPoint_matrix (x : I → ℝ) (y : V → ℝ)
    (hy : ∀ v, 0 < y v) :
    sourceArchUpperHalfspaceMatrix K hζ (sourceKPCuspProductCoordinates K hζ d hd (x,y))
        (fun v => by simpa only [sourceKPCuspProductCoordinates_height] using hy v) =
      sourceKPUpperMatrix (InfiniteAdeleRing K) (sourceKPCuspUnitCellAdelicPoint K d hd x).1 *
        sourceArchUpperHalfspaceMatrix K hζ (sourceKPCuspHeightPoint K y) hy := by
  apply (sourceArchGLPiEquiv K).injective
  funext v
  apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
  simp only [map_mul,Pi.mul_apply,sourceArchUpperHalfspaceMatrix,MulEquiv.apply_symm_apply]
  have hupper :
      sourceKPArchMatrixComplexEquiv K hζ v
        (sourceArchGLPiEquiv K (sourceKPUpperMatrix (InfiniteAdeleRing K)
          (sourceKPCuspUnitCellAdelicPoint K d hd x).1) v) =
        sourceKPUpperMatrix ℂ (sourceKPArchComplexEquiv K hζ v
          ((sourceKPCuspUnitCellAdelicPoint K d hd x).1 v)) := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceKPArchMatrixComplexEquiv_apply,sourceArchGLPiEquiv_apply,sourceKPUpperMatrix] <;> rfl
  rw [hupper]
  simp only [sourceKPCuspProductCoordinates_apply_arch]
  change (upperSection
    (((sourceKPArchComplexEquiv K hζ v ((sourceKPCuspUnitCellAdelicPoint K d hd x).1 v)).re:ℂ) +
      ((sourceKPArchComplexEquiv K hζ v ((sourceKPCuspUnitCellAdelicPoint K d hd x).1 v)).im:ℂ)*Complex.I)
    (y v) (hy v) : GL (Fin 2) ℂ) = _
  rw [Complex.re_add_im]
  simpa [sourceKPCuspHeightPoint] using
    (sourceCuspUpperSection_translate (sourceKPArchComplexEquiv K hζ v
      ((sourceKPCuspUnitCellAdelicPoint K d hd x).1 v)) (y v) (hy v)).symm

theorem sourceKPCuspNativeUpperPoint_adelic (x : I → ℝ) (y : V → ℝ)
    (hy : ∀ v, 0 < y v) (qf : SourceKPFiniteAdeleProjective K hζ) :
    (1,qf) * sourceKPAdelicUpperProductPoint K hζ
      (sourceKPCuspProductCoordinates K hζ d hd (x,y))
      (fun v => by simpa only [sourceKPCuspProductCoordinates_height] using hy v) =
      sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x) *
        (sourceKPCuspHeightSection K hζ y hy,qf) := by
  apply Prod.ext
  · change 1 * ProjGenLinGroup.mk _ = ProjGenLinGroup.mk _ * sourceKPCuspHeightSection K hζ y hy
    rw [one_mul,sourceKPCuspNativeUpperPoint_matrix, map_mul]
    rfl
  · change qf * 1 =
      sourceKPFiniteAdeleUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x).2 * qf
    rw [show (sourceKPCuspUnitCellAdelicPoint K d hd x).2 = 0 from rfl,
      sourceKPFiniteAdeleUpperLift_zero,mul_one,one_mul]

theorem sourceKPCuspNativeUpperPoint_compact (x : I → ℝ) (y : V → ℝ)
    (hy : ∀ v, 0 < y v) (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
      (sourceKPCuspProductCoordinates K hζ d hd (x,y)) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        (sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x) *
          (sourceKPCuspHeightSection K hζ y hy,qf))) := by
  unfold sourceKPCompactCoordinateProjection
  have hp : sourceKPCuspProductCoordinates K hζ d hd (x,y) ∈ productUpper V := by
    intro v _
    change 0 < sourceKPCuspProductCoordinates K hζ d hd (x,y) v 2
    simpa only [sourceKPCuspProductCoordinates_height] using hy v
  rw [sourceKPUpperToCompact_product_point K hζ qf _ hp]
  rw [sourceKPCuspNativeUpperPoint_adelic]

end
end ArtinMatthews
