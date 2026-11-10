module

public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

theorem completion_nondiscrete (F : Type) [Field F] [NumberField F] (v : ArchimedeanAdeles.Construction.Places F) :
    ¬ DiscreteTopology (ArchimedeanAdeles.Construction.Completion F v) := by
  intro h
  let : DiscreteTopology (ArchimedeanAdeles.Construction.Completion F v) := h
  cases v with
  | inl v =>
      rcases v.isReal_or_isComplex with hv | hv
      · let : DiscreteTopology ℝ :=
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.discreteTopology
        have : Subsingleton ℝ := subsingleton_of_preconnected_totallyDisconnected
        exact zero_ne_one (Subsingleton.elim (0 : ℝ) 1)
      · let : DiscreteTopology ℂ :=
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.discreteTopology
        have : Subsingleton ℂ := subsingleton_of_preconnected_totallyDisconnected
        exact zero_ne_one (Subsingleton.elim (0 : ℂ) 1)
  | inr v =>
      let : CharZero (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
      have he : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
          Metric.closedBall (0 : v.adicCompletion F) 1 := by
        ext x
        simp only [Metric.mem_closedBall, dist_zero_right,
          Valued.toNormedField.norm_le_one_iff]
        rfl
      have hc : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [he]
        exact isCompact_closedBall _ _
      have hf := hc.finite_of_discrete
      have hinf : Set.Infinite (Set.range (fun z : ℤ => (z : v.adicCompletion F))) :=
        Set.infinite_range_of_injective Int.cast_injective
      apply hinf
      apply hf.subset
      rintro _ ⟨z, rfl⟩
      exact intCast_mem (v.adicCompletionIntegers F).toSubring z

end

end ArtinMatthews.QuadraticWeil
