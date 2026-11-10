module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.Generators
public import OAI.RepresentationTheory.Theta.Convergence
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

/-! # Substitution -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Substitution.CM

noncomputable section

/-! Rational matrix substitution preserves the actual theta sum by
an explicit bijective relabeling of rational points. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def raw (A : (Matrix I I ℚ)ˣ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] ((I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) where
  toFun F x := F.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem diagonal_apply (A : (Matrix I I ℚ)ˣ) (x : I → ℚ) :
    (A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal (RepresentationTheory.Theta.Generators.PoissonAutomorphyConstruction.transposeMulEquiv A x) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) A.val.transpose x i).symm

theorem theta_invariant (A : (Matrix I I ℚ)ˣ) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    (∑' x : I → ℚ, raw A F (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)) = RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional F := by
  calc
    _ = ∑' x : I → ℚ, F.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal (RepresentationTheory.Theta.Generators.PoissonAutomorphyConstruction.transposeMulEquiv A x)) := by
      apply tsum_congr
      intro x
      change F.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x) = _
      rw [diagonal_apply]
    _ = _ := (RepresentationTheory.Theta.Generators.PoissonAutomorphyConstruction.transposeMulEquiv A).tsum_eq (fun x => F.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x))

omit [DecidableEq I] in
theorem phase_fst (A : Matrix I I ℚ) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (fun i => ((A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i).1) =
      A.map (algebraMap ℚ ℝ) *ᵥ (fun i => (x i).1) := by
  funext i
  change (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ((A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i) = _
  rw [RingHom.map_mulVec]
  rfl

omit [DecidableEq I] in
theorem phase_snd (A : Matrix I I ℚ) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (fun i => ((A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i).2) =
      A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ (fun i => (x i).2) := by
  funext i
  change (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ((A.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i) = _
  rw [RingHom.map_mulVec]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Substitution.CM
