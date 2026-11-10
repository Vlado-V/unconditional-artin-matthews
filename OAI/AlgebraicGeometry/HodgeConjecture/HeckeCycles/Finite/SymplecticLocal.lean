module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot
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
public import Mathlib.RingTheory.Henselian
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

/-! # Symplectic Local -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal.CM

noncomputable section

/-! Actual local and integral symplectic matrices obtained by evaluating
a finite-adelic symplectic matrix. Integrality holds at almost all places. -/

open scoped Classical RestrictedProduct _root_.Matrix
open Filter OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot.CM.SymplecticBigCell

def localEval (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf →+* v.adicCompletion ℚ :=
  RestrictedProduct.evalRingHom (fun w : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace => w.adicCompletion ℚ) v

variable {I : Type*} [Fintype I]

def localSymplectic (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I (v.adicCompletion ℚ) :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (localEval v) g

def IsIntegral (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Prop :=
  ∀ i j, g.val i j v ∈ v.adicCompletionIntegers ℚ

theorem eventually_integral (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : ∀ᶠ v in cofinite, IsIntegral g v := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  exact (g.val i j).property

def integralSymplectic (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : IsIntegral g v) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I (v.adicCompletionIntegers ℚ) :=
  Local.MatrixPivot.CM.SymplecticBigCell.subringSymplectic (v.adicCompletionIntegers ℚ).toSubring (localSymplectic g v) hg

theorem integralSymplectic_map (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : IsIntegral g v) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (v.adicCompletionIntegers ℚ).subtype (integralSymplectic g v hg) = localSymplectic g v :=
  Local.MatrixPivot.CM.SymplecticBigCell.subringSymplectic_map (v.adicCompletionIntegers ℚ).toSubring (localSymplectic g v) hg

theorem integral_big_cell (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : IsIntegral g v) :
    ∃ B : Matrix I I (v.adicCompletionIntegers ℚ), B.IsSymm ∧
      IsUnit ((integralSymplectic g v hg).val.toBlocks₁₁ +
        B * (integralSymplectic g v hg).val.toBlocks₂₁).det :=
  Local.MatrixPivot.CM.SymplecticBigCell.exists_symmetric (integralSymplectic g v hg)

theorem local_big_cell (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    ∃ B : Matrix I I (v.adicCompletion ℚ), B.IsSymm ∧
      IsUnit ((localSymplectic g v).val.toBlocks₁₁ +
        B * (localSymplectic g v).val.toBlocks₂₁).det :=
  Local.MatrixPivot.CM.SymplecticBigCell.exists_symmetric (localSymplectic g v)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal.CM
