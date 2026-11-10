module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! # Mask Insert -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MaskInsert.CM

noncomputable section

/-! Finite-place masks decompose by inserting a single actual p-adic
coordinate. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.Mask

theorem mask_empty (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : PlaceAt.CM.Mask.mask ∅ a = 0 := by
  apply DFunLike.ext
  intro v
  change PlaceAt.CM.Mask.mask ∅ a v = 0
  simp only [PlaceAt.CM.Mask.mask_eval, Set.mem_empty_iff_false, ite_false]

theorem mask_insert (S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hv : v ∉ S) (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    PlaceAt.CM.Mask.mask (↑(insert v S) : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) a = PlaceAt.CM.Mask.mask {v} a + PlaceAt.CM.Mask.mask (↑S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) a := by
  apply DFunLike.ext
  intro w
  change PlaceAt.CM.Mask.mask (↑(insert v S) : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) a w =
    SymplecticLocal.CM.localEval w (PlaceAt.CM.Mask.mask {v} a + PlaceAt.CM.Mask.mask (↑S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) a)
  rw [map_add]
  change PlaceAt.CM.Mask.mask (↑(insert v S) : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) a w = PlaceAt.CM.Mask.mask {v} a w + PlaceAt.CM.Mask.mask (↑S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) a w
  simp only [PlaceAt.CM.Mask.mask_eval, Finset.mem_coe, Finset.mem_insert, Set.mem_singleton_iff]
  by_cases hw : w = v
  · subst w
    simp only [true_or, ite_true, hv, ite_false, add_zero]
  · simp only [hw, false_or, ite_false, zero_add]

theorem inclusion_projection (q : ℕ) [Fact q.Prime] (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q a) = PlaceAt.CM.Mask.mask {RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q} a := by
  change RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeInclude (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q)
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv q ((RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv q).symm (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q) a))) = _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  apply DFunLike.ext
  intro v
  change RestrictedProduct.single (fun w : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace => w.adicCompletionIntegers ℚ)
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q) (a (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q)) v = PlaceAt.CM.Mask.mask {RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q} a v
  rw [PlaceAt.CM.Mask.mask_eval]
  by_cases hv : v = RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q
  · subst v
    rw [RestrictedProduct.single_eq_same]
    simp only [Set.mem_singleton_iff, ite_true]
  · rw [RestrictedProduct.single_eq_of_ne _ _ hv]
    simp only [Set.mem_singleton_iff, hv, ite_false]

variable {I : Type*}

theorem matrixMask_empty (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : PlaceAt.CM.Mask.matrixMask ∅ B = 0 := by
  apply Matrix.ext
  intro i j
  exact mask_empty (B i j)

theorem matrixMask_insert (S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hv : v ∉ S)
    (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    PlaceAt.CM.Mask.matrixMask (↑(insert v S) : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B =
      PlaceAt.CM.Mask.matrixMask {v} B + PlaceAt.CM.Mask.matrixMask (↑S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B := by
  apply Matrix.ext
  intro i j
  exact mask_insert S v hv (B i j)

theorem coefficients_apply (q n : ℕ) [Fact q.Prime] (B : Matrix (Fin n) (Fin n) ℚ_[q])
    (i j : Fin n) : PrimeQuadratic.CM.coefficients q n B i j = RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q (B i j) := rfl

theorem coefficients_projection (q n : ℕ) [Fact q.Prime] (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeQuadratic.CM.coefficients q n (B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q)) =
      PlaceAt.CM.Mask.matrixMask {RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q} B := by
  apply Matrix.ext
  intro i j
  rw [coefficients_apply, Matrix.map_apply]
  exact inclusion_projection q (B i j)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MaskInsert.CM
