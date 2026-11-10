module

public import OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
public import ArtinMatthews.SourceArchHyperbolicEuclidean
public import ArtinMatthews.SourceArchPGLSurjectivity
public import ArtinMatthews.SourceHyperbolicLocalCalculus
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

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein Filter MeasureTheory
open scoped MatrixGroups Topology ContDiff
noncomputable section

def sourceArchEuclideanProjectiveAction (a : PGL(2,ℂ)) (p : EuclideanSpatial) : EuclideanSpatial :=
  sourceArchUpperEuclideanMap (sourceArchProjectiveUpperAction a (sourceArchEuclideanUpperMap p))

theorem sourceArchEuclideanProjectiveAction_preserving (a : PGL(2,ℂ)) :
    MeasurePreserving (sourceArchEuclideanProjectiveAction a)
      hyperbolicEuclideanVolume hyperbolicEuclideanVolume :=
  sourceArchUpperEuclideanMap_preserving.comp
    ((sourceArchHyperbolicMeasure_preserving a).comp sourceArchEuclideanUpperMap_preserving)

theorem sourceArchUpperEuclideanMap_coordinates (u : SourceArchUpperHalfSpace) :
    (sourceArchUpperEuclideanMap u).ofLp = hyperbolicSpatialCoordinates (sourceArchHyperbolicHomeomorph u) := by
  simp only [sourceArchUpperEuclideanMap,sourceArchSpatialCoordinates_symm_apply,
    WithLp.ofLp_toLp,sourceArchHyperbolicHomeomorph_apply,hyperbolicSpatialCoordinates,
    hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,sourceArchUpperEmbedding]

theorem sourceArchEuclideanProjectiveAction_specialLinear (s : SL(2,ℂ))
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchEuclideanProjectiveAction (ProjGenLinGroup.mk (s : GL (Fin 2) ℂ)) p =
      WithLp.toLp 2 (mobiusSpatial s p.ofLp) := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  rw [WithLp.equiv_apply,WithLp.ofLp_toLp]
  unfold sourceArchEuclideanProjectiveAction
  rw [sourceArchUpperEuclideanMap_coordinates]
  have ha : sourceArchProjectiveUpperAction (ProjGenLinGroup.mk (s : GL (Fin 2) ℂ))
      (sourceArchEuclideanUpperMap p) =
      sourceArchHyperbolicHomeomorph.symm (s • sourceArchHyperbolicHomeomorph (sourceArchEuclideanUpperMap p)) :=
    sourceArchGLUpperAction_specialLinear s (sourceArchEuclideanUpperMap p)
  rw [ha,Homeomorph.apply_symm_apply]
  rw [sourceArchEuclideanUpperMap,Homeomorph.apply_symm_apply]
  simpa only [WithLp.equiv_apply,WithLp.ofLp_toLp,euclideanToHyperbolic_positive p hp,
    spatialHorizontal,mul_comm] using
    mobiusSpatial_coordinates s p.ofLp hp

theorem sourceArchEuclideanProjectiveAction_contDiffAt (a : PGL(2,ℂ))
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt ℝ ∞ (sourceArchEuclideanProjectiveAction a) p := by
  obtain ⟨s,hs⟩ := sourceArchSpecialLinear_toPGL_surjective a
  rw [← hs]
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hd : ContDiffAt ℝ ∞ (fun q : EuclideanSpatial => WithLp.toLp 2 (mobiusSpatial s q.ofLp)) p :=
    e.symm.contDiff.contDiffAt.comp p
      ((mobiusSpatial_contDiffAt s p.ofLp hp).comp p e.contDiff.contDiffAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [SourceHyperbolicGreen.upperHalf_isOpen.mem_nhds hp] with q hq
  exact sourceArchEuclideanProjectiveAction_specialLinear s q hq

end
end ArtinMatthews.SourceArchJacquet
