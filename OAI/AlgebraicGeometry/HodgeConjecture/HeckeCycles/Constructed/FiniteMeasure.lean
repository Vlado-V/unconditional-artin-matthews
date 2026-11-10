module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! # Finite Measure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM

noncomputable section

/-! The finite adelic Haar measure normalized by the actual integral
lattice. This construction does not take Weil data as an input. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable (I : Type*) [Fintype I]

def integralCompact : TopologicalSpace.PositiveCompacts (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  ⟨⟨(RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)), RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isCompact⟩, by
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isOpen.interior_eq]
    exact ⟨0, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem⟩⟩

def measure : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) := Measure.addHaarMeasure (integralCompact I)

instance measure_haar : (measure I).IsAddHaarMeasure := inferInstanceAs
  (Measure.addHaarMeasure (integralCompact I)).IsAddHaarMeasure

theorem integral_volume :
    measure I (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = 1 :=
  Measure.addHaarMeasure_self

theorem integral_real_volume :
    (measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = 1 := by
  rw [Measure.real, integral_volume, ENNReal.toReal_one]

theorem lattice_volume_pos (q : ℚ) (hq : q ≠ 0) :
    0 < (measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  exact ENNReal.toReal_pos
    ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen q hq).measure_pos (measure I) ⟨0, (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq).zero_mem⟩).ne'
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact q hq).measure_lt_top.ne

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
