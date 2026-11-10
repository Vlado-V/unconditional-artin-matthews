module

public import ArtinMatthews.SourceKPAdelicCutoffProductChart
public import ArtinMatthews.SourceKPAdelicProductCoordinatePaths
public import ArtinMatthews.SourceKPAutomorphicCompactDefect
public import ArtinMatthews.SourceKPAutomorphicCompactCutoff
public import ArtinMatthews.SourceArchCoordinateReparameterization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The native positive product Laplacian of the literal cutoff agrees
with the actual right-Casimir defect on the same adelic section. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein Filter SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators ContDiff Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCutoffEisensteinProductChart_casimir_place {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ w, 0 < p w 2) (v : InfinitePlace K) :
    positiveEuclideanLaplacian
      (fun u => sourceKPAdelicCutoffEisensteinProductChart K hζ T s q (Function.update p v u)) (p v) =
      sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s)
        (q*sourceKPAdelicUpperProductPoint K hζ p hp) v := by
  let F : EuclideanSpatial → ℂ := fun u =>
    sourceKPAdelicCutoffEisensteinProductChart K hζ T s q (Function.update p v u)
  let q₀ := q*sourceKPAdelicUpperProductPoint K hζ p hp
  let f := sourceKPAdelicCutoffEisenstein K hζ T s
  have hupdate : ContDiff ℝ (∞ : ℕ∞ω) (fun u : EuclideanSpatial => Function.update p v u) := by
    apply contDiff_pi.mpr
    intro w
    by_cases hw : w=v
    · subst w
      have he : (fun u : EuclideanSpatial => Function.update p v u v) = id := by
        funext u
        simp only [Function.update_self,id_eq]
      rw [he]
      exact contDiff_id
    · simpa only [Function.update_of_ne hw] using
        (contDiff_const : ContDiff ℝ (∞ : ℕ∞ω) (fun _ : EuclideanSpatial => p w))
  have hF (u : EuclideanSpatial) (hu : 0 < u 2) : ContDiffAt ℝ (∞ : ℕ∞ω) F u := by
    have hup (w : InfinitePlace K) : 0 < Function.update p v u w 2 := by
      by_cases hw : w=v
      · subst w
        simpa only [Function.update_self] using hu
      · simpa only [Function.update_of_ne hw] using hp w
    exact (sourceKPAdelicCutoffEisensteinProductChart_contDiffAt K hζ hT s q _ hup).comp u hupdate.contDiffAt
  have hr : sourceArchGlobalUpperTranslate K hζ f q₀ v 1 =
      fun t => F (euclideanAxisPath (p v) 0 (p v 0+p v 2*t)) := by
    funext t
    unfold sourceArchGlobalUpperTranslate
    dsimp only [q₀,F]
    rw [mul_assoc,sourceKPAdelicUpperProductPoint_right_real]
    exact (sourceKPAdelicCutoffEisensteinProductChart_apply K hζ T s q _
      (sourceKPProductUpperAxisUpdate_pos K p hp v 0 _ (by simp))).symm
  have hi : sourceArchGlobalUpperTranslate K hζ f q₀ v Complex.I =
      fun t => F (euclideanAxisPath (p v) 1 (p v 1+p v 2*t)) := by
    funext t
    unfold sourceArchGlobalUpperTranslate
    dsimp only [q₀,F]
    rw [mul_assoc,sourceKPAdelicUpperProductPoint_right_imag]
    exact (sourceKPAdelicCutoffEisensteinProductChart_apply K hζ T s q _
      (sourceKPProductUpperAxisUpdate_pos K p hp v 1 _ (by simp))).symm
  have ha : sourceArchGlobalDiagonalTranslate K hζ f q₀ v =
      fun t => F (euclideanAxisPath (p v) 2 (p v 2*Real.exp t)) := by
    funext t
    unfold sourceArchGlobalDiagonalTranslate
    dsimp only [q₀,F]
    rw [mul_assoc,sourceKPAdelicUpperProductPoint_right_diagonal]
    exact (sourceKPAdelicCutoffEisensteinProductChart_apply K hζ T s q _
      (sourceKPProductUpperAxisUpdate_pos K p hp v 2 _ (fun _ => mul_pos (hp v) (Real.exp_pos t)))).symm
  change positiveEuclideanLaplacian F (p v) = sourceArchGlobalCasimir K hζ f q₀ v
  rw [sourceArchEuclideanLaplacian_right_paths F hF (p v) (hp v),sourceArchGlobalCasimir,hr,hi,ha]

theorem sourceKPAdelicCutoffEisensteinProductChart_defect {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian (sourceKPAdelicCutoffEisensteinProductChart K hζ T s q) p-
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)*sourceKPAdelicCutoffEisensteinProductChart K hζ T s q p =
      sourceKPAdelicCutoffCasimirDefect K hζ T s (q*sourceKPAdelicUpperProductPoint K hζ p hp) := by
  unfold sourceArchProductCoordinateLaplacian sourceKPAdelicCutoffCasimirDefect
  simp_rw [sourceKPAdelicCutoffEisensteinProductChart_casimir_place K hζ hT s q p hp]
  rw [sourceKPAdelicCutoffEisensteinProductChart_apply K hζ T s q p hp]
  rfl

theorem sourceKPAdelicCutoffEisensteinProductChart_laplacian_defect {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian (sourceKPAdelicCutoffEisensteinProductChart K hζ T s q) p =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)*sourceKPAdelicCutoffEisensteinProductChart K hζ T s q p+
      sourceKPAdelicCutoffCasimirDefect K hζ T s (q*sourceKPAdelicUpperProductPoint K hζ p hp) := by
  simpa only [add_comm] using sub_eq_iff_eq_add.mp
    (sourceKPAdelicCutoffEisensteinProductChart_defect K hζ hT s q p hp)

theorem sourceKPAdelicCutoffEisensteinProductChart_compact_value (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    sourceKPAdelicCutoffEisensteinProductChart K hζ T s q p =
      sourceKPAutomorphicCompactCutoffEisenstein K hζ T s
        (sourceKPAutomorphicCompactMk K hζ
          (sourceKPAutomorphicLevelMk K hζ (q*sourceKPAdelicUpperProductPoint K hζ p hp))) :=
  sourceKPAdelicCutoffEisensteinProductChart_apply K hζ T s q p hp

theorem sourceKPAdelicCutoffEisensteinProductChart_compact_defect {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian (sourceKPAdelicCutoffEisensteinProductChart K hζ T s q) p-
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)*sourceKPAdelicCutoffEisensteinProductChart K hζ T s q p =
      sourceKPAutomorphicCompactCutoffDefect K hζ hT s
        (sourceKPAutomorphicCompactMk K hζ
          (sourceKPAutomorphicLevelMk K hζ (q*sourceKPAdelicUpperProductPoint K hζ p hp))) :=
  sourceKPAdelicCutoffEisensteinProductChart_defect K hζ hT s q p hp

end
end ArtinMatthews
