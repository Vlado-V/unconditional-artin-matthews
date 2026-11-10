module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
public import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap
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

/-! # Symplectic Coordinate Lemmas -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticCoordinateLemmas.CM

noncomputable section

/-! Coordinate formulas with the ring and equality decisions kept
abstract, so concrete adelic applications do not unfold ring instances. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I K L : Type*} [Fintype I] [CommRing K] [CommRing L]

theorem reindex_refl_matrix (d₁ d₂ : DecidableEq I) (g : @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I _ d₁ K _) :
    (@RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex I I K _ _ d₁ d₂ _ (Equiv.refl I) g).val = g.val := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> rfl

theorem swap_matrix [DecidableEq I] (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) :
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g).val = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap := rfl

theorem map_matrix [DecidableEq I] (f : K →+* L) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp f g).val = g.val.map f := rfl

theorem reindex_map_swap_matrix (d₁ d₂ : DecidableEq I) (f : K →+* L) (g : @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I _ d₁ K _) :
    (@RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom I L _ d₂ _
      (@RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp I _ d₂ K L _ _ f (@RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex I I K _ _ d₁ d₂ _ (Equiv.refl I) g))).val =
    @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap I d₂ L _ * g.val.map f * @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap I d₂ L _ := by
  rw [swap_matrix, map_matrix, reindex_refl_matrix]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticCoordinateLemmas.CM
