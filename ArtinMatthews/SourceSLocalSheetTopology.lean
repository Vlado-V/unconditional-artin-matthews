module

public import ArtinMatthews.SourceSLocalSheetNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Continuity of the literal retained coordinates, their product norm,
and the positive radius of the deleted complex coordinate. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

theorem continuous_sourceSheetOther : Continuous (sourceSheetOther S v) :=
  (continuous_pi fun w : {w : InfinitePlace K // w ≠ v} =>
    (continuous_apply w.val).comp continuous_fst).prodMk continuous_snd

theorem continuous_sourceSheetFill {X : Type*} [TopologicalSpace X]
    {u : X → v.Completionˣ} {y : X → SNormOneOtherUnits S v}
    (hu : Continuous u) (hy : Continuous y) :
    Continuous (fun x => sourceSheetFill S v (u x) (y x)) := by
  change Continuous (fun x => ((sourceSheetFill S v (u x) (y x)).1,(y x).2))
  refine (continuous_pi fun w => ?_).prodMk (continuous_snd.comp hy)
  by_cases hw : w = v
  · subst w
    exact hu.congr (fun x => (sourceSheetFill_chosen S v (u x) (y x)).symm)
  · let w' : {w : InfinitePlace K // w ≠ v} := ⟨w,hw⟩
    exact ((continuous_apply w').comp (continuous_fst.comp hy)).congr
      (fun x => (sourceSheetFill_other S v (u x) (y x) w').symm)

theorem continuous_sourceSheetOtherNorm : Continuous (sourceSheetOtherNorm S v) := by
  unfold sourceSheetOtherNorm
  apply Continuous.mul
  · apply continuous_finsetProd
    intro w _
    exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)).norm.pow _
  · apply continuous_finsetProd
    intro p _
    exact (Units.continuous_val.comp ((continuous_apply p).comp continuous_snd)).norm

theorem continuous_sourceSheetRadius : Continuous (sourceSheetRadius S v) := by
  have h := (continuous_sourceSheetOtherNorm S v).inv₀
    (fun y => (sourceSheetOtherNorm_pos S v y).ne')
  exact (Real.continuous_sqrt.comp h).congr (fun _ => rfl)

end
end ArtinMatthews.SourcePhysical
