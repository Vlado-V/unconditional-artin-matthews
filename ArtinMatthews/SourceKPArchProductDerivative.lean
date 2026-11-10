module

public import ArtinMatthews.SourceKPArchTranslatedProduct
public import ArtinMatthews.SourceKPArchTranslatedDerivativeBound
public import ArtinMatthews.SourceKPProductDerivativeBound
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

/-! A uniform relative first-derivative estimate for the literal
product of translated archimedean spherical factors. -/

namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein
open scoped MatrixGroups BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sourceArchTranslatedCoordinateProduct_fderiv_bound (s : ℂ)
    (g : ι → GL (Fin 2) ℂ) (p : ι → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    ‖fderiv ℝ (sourceArchTranslatedCoordinateProduct s g) p‖ ≤
      (∑ v, 3*‖2*s+1‖/(p v 2))*‖sourceArchTranslatedCoordinateProduct s g p‖ := by
  let f : ι → (ι → EuclideanSpatial) → ℂ :=
    fun v q => sourceArchTranslatedProfile s (g v) (q v)
  have hlocal (v : ι) : DifferentiableAt ℝ (sourceArchTranslatedProfile s (g v)) (p v) :=
    (sourceArchTranslatedProfile_contDiffAt s (g v) (p v) (hp v)).differentiableAt (by simp)
  have hf (v : ι) : DifferentiableAt ℝ (f v) p := by
    simpa only [f,Function.comp_def] using
      (hlocal v).comp p ((hasFDerivAt_apply (𝕜 := ℝ) v p).differentiableAt)
  have hbound (v : ι) :
      ‖fderiv ℝ (f v) p‖ ≤ (3*‖2*s+1‖/(p v 2))*‖f v p‖ := by
    simpa only [f] using sourceKPFinitePi_comp_fderiv_bound
      (ι := ι) (E := EuclideanSpatial) (sourceArchTranslatedProfile s (g v)) p v (hlocal v)
      (3*‖2*s+1‖/(p v 2)) (sourceArchTranslatedProfile_fderiv_bound s (g v) (p v) (hp v))
  change ‖fderiv ℝ (fun y : ι → EuclideanSpatial => ∏ v, f v y) p‖ ≤
    (∑ v, 3*‖2*s+1‖/(p v 2))*‖∏ v, f v p‖
  exact sourceKPFiniteProduct_fderiv_bound Finset.univ f
    (fun v => 3*‖2*s+1‖/(p v 2)) p (fun v _ => hf v) (fun v _ => hbound v)

end
end ArtinMatthews.SourceArchJacquet
