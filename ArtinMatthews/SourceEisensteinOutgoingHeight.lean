module

public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceAdelicHeightFibers


set_option backward.privateInPublic true
@[expose] public section

/-! The outgoing constant term has its exact decreasing height power. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchSphericalProduct_norm_height (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ‖sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk g)‖ =
      sourceKPArchMatrixHeight K hζ g ^ (s.re + 1 / 2) := by
  let := source_isTotallyComplex K hζ
  rw [sourceArchSphericalProduct_mk, norm_prod]
  unfold sourceKPArchMatrixHeight
  rw [← Real.finsetProd_rpow Finset.univ _ (fun v _ =>
    pow_nonneg (sourceArchHeight_pos _).le _) (s.re + 1 / 2)]
  apply Finset.prod_congr rfl
  intro v _
  let G := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  have hG : 0 < sourceArchHeight G := sourceArchHeight_pos G
  change ‖sourceArchSphericalGL s G‖ = (sourceArchHeight G ^ v.mult) ^ (s.re + 1 / 2)
  rw [sourceArchSphericalGL, Complex.norm_cpow_eq_rpow_re_of_pos hG,
    NumberField.IsTotallyComplex.mult_eq, ← Real.rpow_two, ← Real.rpow_mul hG.le]
  congr 1
  norm_num [Complex.add_re, Complex.mul_re]
  ring

theorem sourceKPAdelicTraceIntertwiner_norm_height {s : ℂ} (hs : 0 < s.re)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ) :
    ‖sourceKPAdelicTraceIntertwiner K hζ s (ProjGenLinGroup.mk g, qf)‖ =
      ‖((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) * sourceKPFiniteIntertwiner K hζ s qf‖ *
        sourceKPArchMatrixHeight K hζ g ^ (1 / 2 - s.re) := by
  rw [sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs, norm_mul, norm_mul,
    sourceArchSphericalProduct_norm_height, norm_mul]
  have he : (-s).re + 1 / 2 = 1 / 2 - s.re := by simp only [Complex.neg_re]; ring
  rw [he]
  ring

end
end ArtinMatthews
