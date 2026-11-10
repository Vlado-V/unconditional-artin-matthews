module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.RepresentationTheory.Weil.Local.Coordinates


set_option backward.privateInPublic true
@[expose] public section

/-! # Archimedean Classification -/

namespace OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification.Construction

noncomputable section

/-! Archimedean local fields are topologically isomorphic to the real or complex field. -/

theorem localField_archimedean_classification
    (k : Type) [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) :
    (∃ e : k ≃+* ℝ, Continuous e ∧ Continuous e.symm) ∨
      (∃ e : k ≃+* ℂ, Continuous e ∧ Continuous e.symm) := by
  let : Algebra ℝ k := (Coordinates.Construction.realEmbeddingOfUnbounded k h).toAlgebra
  let : ContinuousSMul ℝ k := continuousSMul_of_algebraMap ℝ k
    (Coordinates.Construction.realEmbeddingOfUnbounded_continuous k h)
  let : FiniteDimensional ℝ k := FiniteDimensional.of_locallyCompactSpace ℝ
  rcases Real.nonempty_algEquiv_or k with hR | hC
  · obtain ⟨e⟩ := hR
    exact Or.inl ⟨e.toRingEquiv, e.toLinearEquiv.toContinuousLinearEquiv.continuous,
      e.toLinearEquiv.toContinuousLinearEquiv.symm.continuous⟩
  · obtain ⟨e⟩ := hC
    exact Or.inr ⟨e.toRingEquiv, e.toLinearEquiv.toContinuousLinearEquiv.continuous,
      e.toLinearEquiv.toContinuousLinearEquiv.symm.continuous⟩

end

end OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification.Construction
