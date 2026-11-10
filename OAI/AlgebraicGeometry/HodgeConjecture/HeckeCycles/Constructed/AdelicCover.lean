module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairIntertwiner
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairUnitary


set_option backward.privateInPublic true
@[expose] public section

/-! # Adelic Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCover.CM

noncomputable section

/-! The actual adelic Schrödinger cover, with unitary genuine action,
Heisenberg covariance, and exact two-fold kernel all proved. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM

theorem project_negOne (n : ℕ) : ConstructedAdelicGroup.CM.projection n (ConstructedAdelicGroup.CM.negOne n) = 1 :=
  Adelic.PairDecomposition.CM.Kernel.project_negOne _ _

theorem unitary (n : ℕ) (a : ConstructedAdelicGroup.CM.AdelicGroup n) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) :
    (∫ x, (ConstructedAdelicGroup.CM.action n a f).val x * star ((ConstructedAdelicGroup.CM.action n a h).val x)
      ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (FiniteMeasure.CM.measure (Fin n))) =
    ∫ x, f.val x * star (h.val x) ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (FiniteMeasure.CM.measure (Fin n)) :=
  Adelic.PairUnitary.CM.unitary _ _ _ a f h

theorem intertwines (n : ℕ) (a : ConstructedAdelicGroup.CM.AdelicGroup n) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg AdelicCharacter.CM.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n))
      (ConstructedAdelicGroup.CM.projection n a) (ConstructedAdelicGroup.CM.action n a) := Adelic.PairIntertwiner.CM.intertwines n _ _ a

def adelicCover (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ AdelicCharacter.CM.character
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (FiniteMeasure.CM.measure (Fin n))) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (ConstructedAdelicGroup.CM.AdelicGroup n) where
  project := ConstructedAdelicGroup.CM.projection n
  action := ConstructedAdelicGroup.CM.action n
  surjective := ConstructedAdelicGroup.CM.projection_surjective n
  negOne := ConstructedAdelicGroup.CM.negOne n
  negOne_ne_one := ConstructedAdelicGroup.CM.negOne_ne_one n
  project_negOne := CM.project_negOne n
  kernel := ConstructedAdelicGroup.CM.kernel n
  genuine := ConstructedAdelicGroup.CM.genuine n
  faithful := ConstructedAdelicGroup.CM.faithful n
  intertwines := CM.intertwines n
  unitary := CM.unitary n

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCover.CM
