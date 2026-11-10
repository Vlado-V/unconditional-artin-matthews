module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison
public import OAI.RepresentationTheory.Weil.Local.FourierEquivalence


set_option backward.privateInPublic true
@[expose] public section

/-! # Heisenberg -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Heisenberg.CM

noncomputable section

/-! Real Heisenberg operators on PoissonAutomorphy's actual Schwartz functions,
with stability supplied by the proved LocalWeil real test-space construction. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM
variable (n : ℕ)

theorem heisenberg_mem (p q : Fin n → ℝ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f.val ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) := by
  have h := RepresentationTheory.Weil.Local.FourierEquivalence.Construction.real_heisenberg_mem 1 (Sum.elim q p) (SchwartzComparison.CM.tests n f)
  have he : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f.val =
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
        (Sum.elim q p) (SchwartzComparison.CM.tests n f).val := funext (SchwartzComparison.CM.heisenberg_formula n p q f.val)
  rw [he]
  exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff _).mpr
    (RepresentationTheory.Weil.Local.RealTestSpace.Construction.schwartzBruhat_real_iff.mp h)

def operator (p q : Fin n → ℝ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) where
  toFun f := ⟨RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f.val, heisenberg_mem n p q f⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact mul_left_comm _ _ _

theorem operator_apply (p q : Fin n → ℝ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (x : Fin n → ℝ) :
    (operator n p q f).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f.val x := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Heisenberg.CM
