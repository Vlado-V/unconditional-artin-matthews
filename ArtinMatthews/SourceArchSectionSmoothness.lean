module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceArchSectionFactorization
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
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups ContDiff
noncomputable section

theorem sourceArchSphericalGL_smooth_family {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℂ) (g : E → GL (Fin 2) ℂ)
    (hg : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun x => g x i j)) :
    ContDiff ℝ ∞ (fun x => sourceArchSphericalGL s (g x)) := by
  have hd : ContDiff ℝ ∞ (fun x => (GeneralLinearGroup.det (g x) : ℂ)) := by
    simpa only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two,
      Pi.mul_apply, Pi.sub_apply] using ((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))
  have hdn : ContDiff ℝ ∞ (fun x => ‖(GeneralLinearGroup.det (g x) : ℂ)‖) :=
    hd.norm ℂ (fun x => (GeneralLinearGroup.det (g x)).ne_zero)
  have hb : ContDiff ℝ ∞ (fun x => sourceArchBottomNorm (g x)) :=
    ((hg 1 0).norm_sq ℂ).add ((hg 1 1).norm_sq ℂ)
  have hh : ContDiff ℝ ∞ (fun x => sourceArchHeight (g x)) :=
    hdn.div hb (fun x => (sourceArchBottomNorm_pos (g x)).ne')
  have hl := hh.log (fun x => (sourceArchHeight_pos (g x)).ne')
  have he : (fun x => sourceArchSphericalGL s (g x)) =
      fun x => Complex.exp ((Real.log (sourceArchHeight (g x)) : ℂ)*(2*s+1)) := by
    funext x
    rw [sourceArchSphericalGL, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (sourceArchHeight_pos (g x)).ne'),
      ← Complex.ofReal_log (sourceArchHeight_pos (g x)).le]
  rw [he]
  exact ((Complex.ofRealCLM.contDiff.comp hl).mul contDiff_const).cexp

end
end ArtinMatthews.SourceArchJacquet

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchCompactScalar_smooth_family {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℂ) (g : E → GL (Fin 2) (InfiniteAdeleRing K))
    (hg : ∀ (v : InfinitePlace K) (i j : Fin 2),
      ContDiff (ℝ) (∞ : ℕ∞ω) (fun x => sourceKPArchComplexEquiv K hζ v (g x i j v)))
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    ContDiff (ℝ) (∞ : ℕ∞ω)
      (fun x => sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk (g x),qf)) := by
  have he : (fun x => sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk (g x),qf)) =
      fun x => (∏ v : InfinitePlace K, sourceArchSphericalGL s
        (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K (g x) v))) *
        sourceKPAdelicCompactScalar K hζ s (1,qf) := by
    funext x
    exact sourceArchCompactScalar_factor_matrix K hζ s (g x) qf
  rw [he]
  apply ContDiff.mul _ contDiff_const
  apply contDiff_prod
  intro v _
  apply sourceArchSphericalGL_smooth_family
  intro i j
  exact hg v i j

end
end ArtinMatthews
