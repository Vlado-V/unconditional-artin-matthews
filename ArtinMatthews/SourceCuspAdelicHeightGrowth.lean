module

public import ArtinMatthews.SourceCuspLocalHeightGrowth
public import ArtinMatthews.SourceKPIdeleNormFlow
public import ArtinMatthews.SourceKPAdelicTranslatedHeight


set_option backward.privateInPublic true
@[expose] public section

/-! Actual archimedean norm-flow bounds for the adelic inverse-entry height constant. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicBaseComplexAt_diagonal (v : InfinitePlace K)
    (u : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicBaseComplexAt K hζ v (sourceKPDiagonalHom 𝔸[K] u) =
      sourceKPDiagonalHom ℂ
        (Units.map (sourceKPArchComplexEquiv K hζ v) (sourceKPIdeleInfiniteCoordinate K v u)) := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change (sourceKPArchComplexEquiv K hζ v) (0 : v.Completion) = 0
    exact map_zero _
  · change (sourceKPArchComplexEquiv K hζ v) (0 : v.Completion) = 0
    exact map_zero _
  · change (sourceKPArchComplexEquiv K hζ v) (1 : v.Completion) = 1
    exact map_one _

theorem sourceKPAdelicBaseFiniteAt_diagonal (P : HeightOneSpectrum (𝓞 K))
    (u : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicBaseFiniteAt K P (sourceKPDiagonalHom 𝔸[K] u) =
      sourceKPDiagonalHom (P.adicCompletion K) (sourceKPIdeleFiniteCoordinate K P u) := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sourceKPIdeleFiniteCoordinate_archOnly (P : HeightOneSpectrum (𝓞 K))
    (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPIdeleFiniteCoordinate K P (sourceArchOnlyIdele K a) = 1 := by
  apply Units.ext
  rfl

theorem sourceKPAdelicHeightConstant_right_archOnly
    (g : GL (Fin 2) 𝔸[K]) (a : (InfiniteAdeleRing K)ˣ)
    (ha : ∀ v, 1 ≤ ‖(a : InfiniteAdeleRing K) v‖) :
    sourceKPAdelicHeightConstant K hζ (g * sourceKPDiagonalHom 𝔸[K] (sourceArchOnlyIdele K a)) ≤
      ‖(a : InfiniteAdeleRing K)‖ * sourceKPAdelicHeightConstant K hζ g := by
  let u := sourceArchOnlyIdele K a
  let A (v : InfinitePlace K) : ℂˣ :=
    Units.map (sourceKPArchComplexEquiv K hζ v).toMonoidHom (sourceKPIdeleInfiniteCoordinate K v u)
  have hA (v : InfinitePlace K) : ‖(A v : ℂ)‖ = ‖(a : InfiniteAdeleRing K) v‖ := by
    change ‖sourceKPArchComplexEquiv K hζ v ((a : InfiniteAdeleRing K) v)‖ = _
    exact sourceKPArchComplexEquiv_norm K hζ v _
  have harch (v : InfinitePlace K) :
      sourceArchMatrixHeightConstant
        (sourceKPAdelicBaseComplexAt K hζ v (g * sourceKPDiagonalHom 𝔸[K] u)) ≤
      ‖(a : InfiniteAdeleRing K) v‖ *
        sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v g) := by
    rw [map_mul, sourceKPAdelicBaseComplexAt_diagonal]
    have hb := sourceArchMatrixHeightConstant_right_diagonal
      (sourceKPAdelicBaseComplexAt K hζ v g) (A v) (by rw [hA]; exact ha v)
    rwa [hA] at hb
  have hfinite (P : HeightOneSpectrum (𝓞 K)) :
      sourceKPAdelicBaseFiniteAt K P (g * sourceKPDiagonalHom 𝔸[K] u) =
        sourceKPAdelicBaseFiniteAt K P g := by
    rw [map_mul, sourceKPAdelicBaseFiniteAt_diagonal,
      sourceKPIdeleFiniteCoordinate_archOnly, map_one, mul_one]
  have hp : (∏ v, sourceArchMatrixHeightConstant
      (sourceKPAdelicBaseComplexAt K hζ v (g * sourceKPDiagonalHom 𝔸[K] u)) ^ v.mult) ≤
      (∏ v, ‖(a : InfiniteAdeleRing K) v‖ ^ v.mult) *
        ∏ v, sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v g) ^ v.mult := by
    calc
      _ ≤ ∏ v, (‖(a : InfiniteAdeleRing K) v‖ *
          sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v g)) ^ v.mult := by
        apply Finset.prod_le_prod₀
        · intro v _
          exact pow_nonneg (sourceArchMatrixHeightConstant_pos _).le _
        · intro v _
          exact pow_le_pow_left₀ (sourceArchMatrixHeightConstant_pos _).le (harch v) _
      _ = _ := by simp only [mul_pow, Finset.prod_mul_distrib]
  have hfinpos : 0 ≤ ∏ᶠ P : HeightOneSpectrum (𝓞 K),
      sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P g) := by
    rw [finprod_eq_prod _ (sourceKPAdelicHeightConstant_finite_support K g)]
    exact Finset.prod_nonneg (fun P _ => (sourceKPFiniteMatrixHeightConstant_pos K P _).le)
  change (∏ v, sourceArchMatrixHeightConstant
      (sourceKPAdelicBaseComplexAt K hζ v (g * sourceKPDiagonalHom 𝔸[K] u)) ^ v.mult) *
      (∏ᶠ P : HeightOneSpectrum (𝓞 K), sourceKPFiniteMatrixHeightConstant K P
        (sourceKPAdelicBaseFiniteAt K P (g * sourceKPDiagonalHom 𝔸[K] u))) ≤
    ‖(a : InfiniteAdeleRing K)‖ *
      ((∏ v, sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v g) ^ v.mult) *
        ∏ᶠ P : HeightOneSpectrum (𝓞 K),
          sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P g))
  simp_rw [hfinite]
  rw [InfiniteAdeleRing.norm_def]
  calc
    _ ≤ ((∏ v, ‖(a : InfiniteAdeleRing K) v‖ ^ v.mult) *
        ∏ v, sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v g) ^ v.mult) *
      (∏ᶠ P : HeightOneSpectrum (𝓞 K),
        sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P g)) :=
      mul_le_mul_of_nonneg_right hp hfinpos
    _ = _ := by ring

theorem sourceKPAdelicHeightConstant_right_normFlow
    (g : GL (Fin 2) 𝔸[K]) (v₀ : InfinitePlace K) {t : ℝ} (ht : 0 ≤ t) :
    sourceKPAdelicHeightConstant K hζ
      (g * sourceKPDiagonalHom 𝔸[K] (sourceKPIdeleNormFlow K hζ v₀ t)) ≤
        Real.exp t * sourceKPAdelicHeightConstant K hζ g := by
  have ha (v : InfinitePlace K) : 1 ≤ ‖(sourceKPIdeleNormFlowArch K hζ v₀ t : InfiniteAdeleRing K) v‖ := by
    rw [sourceKPIdeleNormFlowArch_coordinate]
    split_ifs
    · exact Real.one_le_exp_iff.mpr (by linarith)
    · exact le_rfl
  have h := sourceKPAdelicHeightConstant_right_archOnly K hζ g
    (sourceKPIdeleNormFlowArch K hζ v₀ t) ha
  have hn : ‖(sourceKPIdeleNormFlowArch K hζ v₀ t : InfiniteAdeleRing K)‖ = Real.exp t := by
    rw [← sourceArchOnlyIdele_norm K, ← sourceKPIdeleNormFlow, sourceKPIdeleNormFlow_norm]
  rwa [hn] at h

end
end ArtinMatthews
