module

public import ArtinMatthews.SourceKPAdelicProjectiveHeight
public import ArtinMatthews.SourceFiniteWindowExhaustion
public import ArtinMatthews.SourceAdelicHeightComparison
public import ArtinMatthews.SourceKPAdelicSectionBound
public import ArtinMatthews.SourceKPAdelicUpperProjection
public import ArtinMatthews.SourceKPLocalFiniteKernel
public import ArtinMatthews.SourceKubotaGL2Generation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact section on every finite fibre has the product height envelope. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private def finiteAdelicArgument (y : 𝔸ᶠ[K]) : 𝔸[K] := (0, y)

private def finiteOpenCellMatrix (y : 𝔸ᶠ[K]) : GL (Fin 2) 𝔸[K] :=
  sourceKPWeylMatrix 𝔸[K] * sourceKPUpperMatrix 𝔸[K] (finiteAdelicArgument K y)

private theorem finiteOpenCell_finite (y : 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdelicBaseFiniteAt K P (finiteOpenCellMatrix K y) =
      sourceGL2Weyl * sourceGL2Upper (y P) := by
  let φ := (sourceKPAdeleEval K P).comp (sourceKPAdeleFiniteProjection K)
  have he : sourceKPAdelicBaseFiniteAt K P (finiteOpenCellMatrix K y) =
      GeneralLinearGroup.map φ (finiteOpenCellMatrix K y) := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he, finiteOpenCellMatrix, map_mul, sourceKPWeylMatrix_map, sourceKPUpperMatrix_map,
    sourceKPWeylMatrix_field, sourceKPUpperMatrix_field]
  rfl

private theorem finiteOpenCell_complex (y : 𝔸ᶠ[K]) (v : InfinitePlace K) :
    sourceKPAdelicBaseComplexAt K hζ v (finiteOpenCellMatrix K y) = sourceGL2Weyl := by
  let φ := (sourceKPArchComplexEquiv K hζ v).toRingHom.comp
    ((sourceArchAdeleEval K v).comp (sourceKPAdeleInfiniteProjection K))
  have he : sourceKPAdelicBaseComplexAt K hζ v (finiteOpenCellMatrix K y) =
      GeneralLinearGroup.map φ (finiteOpenCellMatrix K y) := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he, finiteOpenCellMatrix, map_mul, sourceKPWeylMatrix_map, sourceKPUpperMatrix_map,
    sourceKPWeylMatrix_field, sourceKPUpperMatrix_field]
  have hz : φ (finiteAdelicArgument K y) = 0 := by
    change sourceKPArchComplexEquiv K hζ v (0 : v.Completion) = 0
    exact map_zero _
  rw [hz, sourceGL2Upper_zero, mul_one]

private theorem finiteOpenCell_height (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : 𝔸ᶠ[K]) (hy : y ∈ sourceKPFiniteWindow K S) :
    sourceKPAdelicHeight K hζ (finiteOpenCellMatrix K y) =
      ∏ P ∈ S, (max 1 ‖y P‖)⁻¹ ^ 2 := by
  have hA : (∏ v : InfinitePlace K,
      sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v (finiteOpenCellMatrix K y)) ^ v.mult) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    rw [finiteOpenCell_complex K hζ y v]
    simp [sourceArchHeight, sourceArchBottomNorm, sourceGL2Weyl,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  rw [sourceKPAdelicHeight_product]
  change (∏ v : InfinitePlace K,
      sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v (finiteOpenCellMatrix K y)) ^ v.mult) *
    (∏ᶠ P : HeightOneSpectrum (𝓞 K),
      sourceKPFiniteMatrixHeight K P (sourceKPAdelicBaseFiniteAt K P (finiteOpenCellMatrix K y))) = _
  rw [hA, one_mul]
  simp_rw [finiteOpenCell_finite K y, sourceKPFiniteMatrixHeight_weyl_upper]
  apply finprod_eq_prod_of_mulSupport_subset
  intro P hP
  by_contra hn
  have hx : ‖y P‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mp (hy P hn))
  apply hP
  change (max 1 ‖y P‖)⁻¹ ^ 2 = 1
  rw [max_eq_left hx, inv_one, one_pow]

private theorem finiteOpenCell_projection (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hg : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (y : 𝔸ᶠ[K]) :
    sourceKPAdelicProjectiveProjection K hζ
      (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (finiteAdelicArgument K y) * q) =
        ProjGenLinGroup.mk (finiteOpenCellMatrix K y * g) := by
  have hw : sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicProjectiveWeyl K hζ) =
      ProjGenLinGroup.mk (sourceKPWeylMatrix 𝔸[K]) := by
    rw [sourceKPAdelicProjectiveWeyl, sourceKPAdelicProjectiveRationalLift_projection,
      ProjGenLinGroup.map_mk, sourceKPWeylMatrix_map]
  rw [map_mul, map_mul, hw, sourceKPAdelicUpperLift_projection, hg, ← map_mul, ← map_mul]
  rfl

theorem sourceKPFiniteWindow_coverHeight_bound (g : SourceKPFiniteAdeleProjective K hζ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ sourceKPFiniteWindow K S,
      sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveWeyl K hζ *
        sourceKPAdelicUpperLift K hζ (0, y) * (1, g)) ≤
          C * ∏ P ∈ S, (max 1 ‖y P‖)⁻¹ ^ 2 := by
  let q : SourceKPAdelicProjective K hζ := (1, g)
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  refine ⟨sourceKPAdelicHeightConstant K hζ u, sourceKPAdelicHeightConstant_pos K hζ u, ?_⟩
  intro y hy
  change sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveWeyl K hζ *
    sourceKPAdelicUpperLift K hζ (finiteAdelicArgument K y) * q) ≤ _
  rw [sourceKPAdelicCoverHeight, finiteOpenCell_projection K hζ q u hu.symm y,
    sourceKPAdelicHeightOnProjective_mk, ← finiteOpenCell_height K hζ S y hy]
  exact sourceKPAdelicHeight_mul_le K hζ (finiteOpenCellMatrix K y) u

def sourceKPFiniteWindowPower (S : Finset (HeightOneSpectrum (𝓞 K))) (a : ℝ)
    (y : 𝔸ᶠ[K]) : ℝ := ∏ P ∈ S, (max 1 ‖y P‖) ^ (-a)

theorem sourceKPFiniteIntertwiningKernel_eq_adelic (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ) (y : 𝔸ᶠ[K]) :
    sourceKPFiniteIntertwiningKernel K hζ s g y =
      sourceKPAdelicIntertwiningKernel K hζ s (1, g) (0, y) :=
  (sourceKPLocalFiniteKernel_eq_full K hζ s g y).symm

theorem sourceKPFiniteIntertwiningKernel_window_bound (g : SourceKPFiniteAdeleProjective K hζ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 < s.re → ∀ y ∈ sourceKPFiniteWindow K S,
      ‖sourceKPFiniteIntertwiningKernel K hζ s g y‖ ≤
        C ^ (s.re + 1 / 2) * sourceKPFiniteWindowPower K S (2 * s.re + 1) y := by
  obtain ⟨C, hC, hheight⟩ := sourceKPFiniteWindow_coverHeight_bound K hζ g S
  refine ⟨C, hC, ?_⟩
  intro s hs y hy
  let q : SourceKPAdelicProjective K hζ := sourceKPAdelicProjectiveWeyl K hζ *
    sourceKPAdelicUpperLift K hζ (0, y) * (1, g)
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hh : sourceKPAdelicCoverHeight K hζ q = sourceKPAdelicHeight K hζ u := by
    rw [sourceKPAdelicCoverHeight, ← hu, sourceKPAdelicHeightOnProjective_mk]
  have hr : 0 ≤ s.re + 1 / 2 := by linarith
  have hp : 0 ≤ ∏ P ∈ S, (max 1 ‖y P‖)⁻¹ ^ 2 := Finset.prod_nonneg (fun _ _ => sq_nonneg _)
  rw [sourceKPFiniteIntertwiningKernel_eq_adelic]
  change ‖sourceKPAdelicCompactScalar K hζ s q‖ ≤ _
  calc
    _ ≤ sourceKPAdelicHeight K hζ u ^ (s.re + 1 / 2) :=
      sourceKPAdelicCompactScalar_height_bound K hζ s q u hu.symm
    _ ≤ (C * ∏ P ∈ S, (max 1 ‖y P‖)⁻¹ ^ 2) ^ (s.re + 1 / 2) :=
      Real.rpow_le_rpow (sourceKPAdelicHeight_pos K hζ u).le
        (by rw [← hh]; exact hheight y hy) hr
    _ = _ := by
      unfold sourceKPFiniteWindowPower
      rw [Real.mul_rpow hC.le hp, ← Real.finsetProd_rpow S _ (fun _ _ => sq_nonneg _)]
      congr 1
      apply Finset.prod_congr rfl
      intro P _
      have hn : 0 ≤ max 1 ‖y P‖ := zero_le_one.trans (le_max_left _ _)
      rw [show ((max 1 ‖y P‖)⁻¹ ^ 2) = (max 1 ‖y P‖) ^ (-2 : ℝ) by
        rw [Real.rpow_neg hn, Real.rpow_two, inv_pow], ← Real.rpow_mul hn]
      congr 1
      ring

end
end ArtinMatthews
