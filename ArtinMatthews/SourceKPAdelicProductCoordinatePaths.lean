module

public import ArtinMatthews.SourceArchSingleRightAction
public import ArtinMatthews.SourceArchDiagonalLog
public import ArtinMatthews.SourceArchSphericalProductCasimir
public import ArtinMatthews.SourceKPArchUpperCoordinatePaths
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

/-! Right translation at one archimedean place changes exactly one
native product coordinate and retains every other component. -/
namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private theorem projective_eq_of_arch_places
    (a b : GL (Fin 2) (InfiniteAdeleRing K))
    (h : ∀ w, ProjGenLinGroup.mk (sourceKPArchMatrixComplexEquiv K hζ w
        (sourceArchGLPiEquiv K a w)) =
      ProjGenLinGroup.mk (sourceKPArchMatrixComplexEquiv K hζ w
        (sourceArchGLPiEquiv K b w))) :
    ProjGenLinGroup.mk a = ProjGenLinGroup.mk b := by
  apply ProjGenLinGroup.mk_eq_mk_iff'.mpr
  refine ⟨a⁻¹*b,Subgroup.mem_center_iff.mpr ?_,by simp⟩
  intro c
  apply (sourceArchGLPiEquiv K).injective
  funext w
  apply (sourceKPArchMatrixComplexEquiv K hζ w).injective
  simp only [map_mul,map_inv,Pi.mul_apply,Pi.inv_apply]
  have hz : (sourceKPArchMatrixComplexEquiv K hζ w (sourceArchGLPiEquiv K a w))⁻¹*
        sourceKPArchMatrixComplexEquiv K hζ w (sourceArchGLPiEquiv K b w) ∈
      Subgroup.center (GL (Fin 2) ℂ) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    rw [map_mul,map_inv,h w,inv_mul_cancel]
  exact Subgroup.mem_center_iff.mp hz _

private theorem productUpper_update_pos (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ w, 0 < p w 2) (v : InfinitePlace K) (u : EuclideanSpatial) (hu : 0 < u 2) :
    ∀ w, 0 < Function.update p v u w 2 := by
  intro w
  by_cases hw : w=v
  · subst w
    simpa only [Function.update_self] using hu
  · simpa only [Function.update_of_ne hw] using hp w

private theorem axisPath_apply (p : EuclideanSpatial) (j i : Fin 3) (t : ℝ) :
    euclideanAxisPath p j t i = Function.update p.ofLp j t i := rfl

theorem sourceKPProductUpperAxisUpdate_pos (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ w, 0 < p w 2) (v : InfinitePlace K) (j : Fin 3) (t : ℝ)
    (ht : j=2 → 0<t) :
    ∀ w, 0 < Function.update p v (euclideanAxisPath (p v) j t) w 2 := by
  apply productUpper_update_pos K p hp v
  by_cases h : (2 : Fin 3)=j
  · subst j
    simpa only [axisPath_apply,Function.update_self] using ht rfl
  · simpa only [axisPath_apply,Function.update_of_ne h] using hp v

def sourceKPAdelicUpperProductPoint (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) : SourceKPAdelicProjective K hζ :=
  (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)

private theorem upperProductPoint_right_update (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ w, 0 < p w 2) (v : InfinitePlace K) (a : GL (Fin 2) ℂ)
    (u : EuclideanSpatial) (hu : 0 < u 2)
    (hlocal : sourceArchUpperPoint ((p v 0 : ℂ)+(p v 1 : ℂ)*Complex.I) (p v 2) (hp v)*
        ProjGenLinGroup.mk a = sourceArchUpperPoint ((u 0 : ℂ)+(u 1 : ℂ)*Complex.I) (u 2) hu) :
    sourceKPAdelicUpperProductPoint K hζ p hp*sourceArchGroupSingle K hζ v a =
      sourceKPAdelicUpperProductPoint K hζ (Function.update p v u)
        (productUpper_update_pos K p hp v u hu) := by
  apply Prod.ext
  · change ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)*
      ProjGenLinGroup.mk (sourceArchMatrixSingle K hζ v a) =
        ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ (Function.update p v u)
          (productUpper_update_pos K p hp v u hu))
    rw [← map_mul]
    apply projective_eq_of_arch_places K hζ
    intro w
    simp only [map_mul,Pi.mul_apply,sourceArchMatrixSingle_at,
      sourceArchUpperHalfspaceMatrix,MulEquiv.apply_symm_apply]
    by_cases hw : w=v
    · subst w
      simp only [Pi.mulSingle_eq_same,Function.update_self]
      exact hlocal
    · simp only [Pi.mulSingle_eq_of_ne hw,Function.update_of_ne hw,ProjGenLinGroup.mk_one,mul_one]
  · change (1 : SourceKPFiniteAdeleProjective K hζ)*1 = 1
    exact one_mul _

private theorem upperPoint_congr {z w : ℂ} {y u : ℝ} {hy : 0 < y} {hu : 0 < u}
    (hz : z=w) (hh : y=u) : sourceArchUpperPoint z y hy = sourceArchUpperPoint w u hu := by
  subst w
  subst u
  rfl

theorem sourceKPAdelicUpperProductPoint_right_real (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ w, 0 < p w 2) (v : InfinitePlace K) (t : ℝ) :
    sourceKPAdelicUpperProductPoint K hζ p hp*
      sourceArchGroupSingle K hζ v (sourceKPUpperMatrix ℂ ((t : ℂ)*1)) =
      sourceKPAdelicUpperProductPoint K hζ
        (Function.update p v (euclideanAxisPath (p v) 0 (p v 0+p v 2*t)))
        (sourceKPProductUpperAxisUpdate_pos K p hp v 0 _ (by simp)) := by
  let u := euclideanAxisPath (p v) 0 (p v 0+p v 2*t)
  have hy : u 2 = p v 2 := by
    simp only [u,axisPath_apply,Function.update_of_ne (by decide : (2 : Fin 3)≠0)]
  have hz : (u 0 : ℂ)+(u 1 : ℂ)*Complex.I =
      ((p v 0 : ℂ)+(p v 1 : ℂ)*Complex.I)+(p v 2 : ℂ)*((t : ℂ)*1) := by
    simp only [u,axisPath_apply,Function.update_self,Function.update_of_ne (by decide : (1 : Fin 3)≠0),
      Complex.ofReal_add,Complex.ofReal_mul,mul_one]
    ring
  have hu : 0 < u 2 := by rw [hy]; exact hp v
  apply upperProductPoint_right_update K hζ p hp v _ u hu
  exact (sourceArchUpperPoint_upper _ _ _ (hp v)).trans (upperPoint_congr hz.symm hy.symm)

theorem sourceKPAdelicUpperProductPoint_right_imag (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ w, 0 < p w 2) (v : InfinitePlace K) (t : ℝ) :
    sourceKPAdelicUpperProductPoint K hζ p hp*
      sourceArchGroupSingle K hζ v (sourceKPUpperMatrix ℂ ((t : ℂ)*Complex.I)) =
      sourceKPAdelicUpperProductPoint K hζ
        (Function.update p v (euclideanAxisPath (p v) 1 (p v 1+p v 2*t)))
        (sourceKPProductUpperAxisUpdate_pos K p hp v 1 _ (by simp)) := by
  let u := euclideanAxisPath (p v) 1 (p v 1+p v 2*t)
  have hy : u 2 = p v 2 := by
    simp only [u,axisPath_apply,Function.update_of_ne (by decide : (2 : Fin 3)≠1)]
  have hz : (u 0 : ℂ)+(u 1 : ℂ)*Complex.I =
      ((p v 0 : ℂ)+(p v 1 : ℂ)*Complex.I)+(p v 2 : ℂ)*((t : ℂ)*Complex.I) := by
    simp only [u,axisPath_apply,Function.update_self,Function.update_of_ne (by decide : (0 : Fin 3)≠1),
      Complex.ofReal_add,Complex.ofReal_mul]
    ring
  have hu : 0 < u 2 := by rw [hy]; exact hp v
  apply upperProductPoint_right_update K hζ p hp v _ u hu
  exact (sourceArchUpperPoint_upper _ _ _ (hp v)).trans (upperPoint_congr hz.symm hy.symm)

theorem sourceKPAdelicUpperProductPoint_right_diagonal (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ w, 0 < p w 2) (v : InfinitePlace K) (t : ℝ) :
    sourceKPAdelicUpperProductPoint K hζ p hp*
      sourceArchGroupSingle K hζ v (sourceArchPositiveDiagonal t) =
      sourceKPAdelicUpperProductPoint K hζ
        (Function.update p v (euclideanAxisPath (p v) 2 (p v 2*Real.exp t)))
        (sourceKPProductUpperAxisUpdate_pos K p hp v 2 _ (fun _ => mul_pos (hp v) (Real.exp_pos t))) := by
  let u := euclideanAxisPath (p v) 2 (p v 2*Real.exp t)
  have hy : u 2 = p v 2*Real.exp t := by simp only [u,axisPath_apply,Function.update_self]
  have hz : (u 0 : ℂ)+(u 1 : ℂ)*Complex.I = (p v 0 : ℂ)+(p v 1 : ℂ)*Complex.I := by
    simp only [u,axisPath_apply,Function.update_of_ne (by decide : (0 : Fin 3)≠2),
      Function.update_of_ne (by decide : (1 : Fin 3)≠2)]
  have hu : 0 < u 2 := by rw [hy]; exact mul_pos (hp v) (Real.exp_pos t)
  apply upperProductPoint_right_update K hζ p hp v _ u hu
  exact (sourceArchUpperPoint_diagonal _ _ t (hp v)).trans (upperPoint_congr hz.symm hy.symm)

end
end ArtinMatthews
