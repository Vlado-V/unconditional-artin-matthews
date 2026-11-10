module

public import ArtinMatthews.SourceKPArchTranslatedProfile
public import ArtinMatthews.SourceArchProductCasimir
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Joint smoothness and the native product Laplacian for the actual
translated spherical factors. -/

namespace ArtinMatthews.SourceArchJacquet
open OAI.CubicEisenstein Matrix
open scoped MatrixGroups BigOperators ContDiff Classical
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceArchTranslatedCoordinateProduct (s : ℂ) (g : ι → GL (Fin 2) ℂ)
    (p : ι → EuclideanSpatial) : ℂ :=
  ∏ v, sourceArchTranslatedProfile s (g v) (p v)

omit [DecidableEq ι] in
theorem sourceArchTranslatedCoordinateProduct_contDiffAt (s : ℂ) (g : ι → GL (Fin 2) ℂ)
    (p : ι → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    ContDiffAt (ℝ) (∞ : ℕ∞ω) (sourceArchTranslatedCoordinateProduct s g) p := by
  apply contDiffAt_prod
  intro v _
  change ContDiffAt (ℝ) (∞ : ℕ∞ω)
    (fun q : ι → EuclideanSpatial => sourceArchTranslatedProfile s (g v) (q v)) p
  have hev : ContDiffAt (ℝ) (∞ : ℕ∞ω) (fun q : ι → EuclideanSpatial => q v) p := by fun_prop
  have h := (sourceArchTranslatedProfile_contDiffAt s (g v) (p v) (hp v)).comp p hev
  exact h

theorem sourceArchTranslatedCoordinateProduct_update (s : ℂ) (g : ι → GL (Fin 2) ℂ)
    (p : ι → EuclideanSpatial) (v : ι) (q : EuclideanSpatial) :
    sourceArchTranslatedCoordinateProduct s g (Function.update p v q) =
      sourceArchTranslatedProfile s (g v) q *
        ∏ w ∈ Finset.univ \ {v}, sourceArchTranslatedProfile s (g w) (p w) := by
  have hfun : (fun w => sourceArchTranslatedProfile s (g w) (Function.update p v q w)) =
      Function.update (fun w => sourceArchTranslatedProfile s (g w) (p w)) v
        (sourceArchTranslatedProfile s (g v) q) := by
    funext w
    by_cases hw : w=v <;> simp [hw]
  unfold sourceArchTranslatedCoordinateProduct
  rw [hfun,Finset.prod_update_of_mem (Finset.mem_univ v)]

theorem sourceArchTranslatedProfile_const_laplacian (s c : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    positiveEuclideanLaplacian (fun q => c*sourceArchTranslatedProfile s g q) p =
      (1-4*s^2)*(c*sourceArchTranslatedProfile s g p) := by
  have hr (q : EuclideanSpatial) (hq : 0 < q 2) :
      ContDiffAt (ℝ) (∞ : ℕ∞ω) (fun r => c*sourceArchTranslatedProfile s g r) q :=
    contDiffAt_const.mul (sourceArchTranslatedProfile_contDiffAt s g q hq)
  calc
    _ = c*positiveEuclideanLaplacian (sourceArchTranslatedProfile s g) p := by
      rw [positiveEuclideanLaplacian_eq_axis _ hr p hp,
        positiveEuclideanLaplacian_eq_axis _ (sourceArchTranslatedProfile_contDiffAt s g) p hp,
        axisLaplacian_const_mul]
      ring
    _ = _ := by rw [sourceArchTranslatedProfile_laplacian s g p hp]; ring

theorem sourceArchTranslatedCoordinateProduct_laplacian (s c : ℂ) (g : ι → GL (Fin 2) ℂ)
    (p : ι → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian (fun q => c*sourceArchTranslatedCoordinateProduct s g q) p =
      (Fintype.card ι : ℂ)*(1-4*s^2)*(c*sourceArchTranslatedCoordinateProduct s g p) := by
  have hterm (v : ι) : positiveEuclideanLaplacian
      (fun q => c*sourceArchTranslatedCoordinateProduct s g (Function.update p v q)) (p v) =
      (1-4*s^2)*(c*sourceArchTranslatedCoordinateProduct s g p) := by
    let C := ∏ w ∈ Finset.univ \ {v}, sourceArchTranslatedProfile s (g w) (p w)
    have hslice : (fun q => c*sourceArchTranslatedCoordinateProduct s g (Function.update p v q)) =
        fun q => (c*C)*sourceArchTranslatedProfile s (g v) q := by
      funext q
      rw [sourceArchTranslatedCoordinateProduct_update]
      dsimp only [C]
      ring
    have hvalue : sourceArchTranslatedCoordinateProduct s g p =
        sourceArchTranslatedProfile s (g v) (p v)*C := by
      simpa only [Function.update_eq_self] using sourceArchTranslatedCoordinateProduct_update s g p v (p v)
    rw [hslice,sourceArchTranslatedProfile_const_laplacian s (c*C) (g v) (p v) (hp v),hvalue]
    ring
  unfold sourceArchProductCoordinateLaplacian
  simp_rw [hterm]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

end
end ArtinMatthews.SourceArchJacquet
