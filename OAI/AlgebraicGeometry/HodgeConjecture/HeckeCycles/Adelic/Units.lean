module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.AdelicSupport
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
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
public import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier


set_option backward.privateInPublic true
@[expose] public section

/-! # Units -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Units.CM

noncomputable section

/-! Construct a finite adelic unit from nonzero local coordinates and
integrality of their inverses at almost all places. -/

open Filter OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

def inverse (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hi : ∀ᶠ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace in cofinite, (a v)⁻¹ ∈ v.adicCompletionIntegers ℚ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  ⟨fun v => (a v)⁻¹, hi⟩

def unit (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hn : ∀ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, a v ≠ 0)
    (hi : ∀ᶠ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace in cofinite, (a v)⁻¹ ∈ v.adicCompletionIntegers ℚ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQfˣ where
  val := a
  inv := inverse a hi
  val_inv := by
    apply DFunLike.ext
    intro v
    exact mul_inv_cancel₀ (hn v)
  inv_val := by
    apply DFunLike.ext
    intro v
    exact inv_mul_cancel₀ (hn v)

theorem isUnit_of_local (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hn : ∀ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, a v ≠ 0)
    (hi : ∀ᶠ v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace in cofinite, (a v)⁻¹ ∈ v.adicCompletionIntegers ℚ) : IsUnit a :=
  ⟨unit a hn hi, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Units.CM
