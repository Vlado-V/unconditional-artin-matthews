module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Quadratic
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Fourier
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
public import Mathlib.Tactic.ENatToNat
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CoverFields


set_option backward.privateInPublic true
@[expose] public section

/-! # Lower -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Lower.CM

noncomputable section

/-! Actual adelic lower lifts are exact conjugates of the upper
quadratic action by the actual adelic Fourier automorphism. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
variable (n : ℕ)

def lower (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) : Constructed.ConstructedAdelicGroup.CM.AdelicGroup n :=
  AdelicPairGroup.CM.assemble (Constructed.RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))
    (Real.BareGenerators.CM.lower n ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩,
      Finite.IntegralVacuum.CM.LowerBare.lowerLift (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hB.map _))

theorem lower_projection_matrix (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) :
    (Constructed.ConstructedAdelicGroup.CM.projection n (lower n B hB)).val = Matrix.fromBlocks 1 0 B 1 := by
  change (AdelicPairGroup.CM.projection _ _ (AdelicPairGroup.CM.assemble _ _ _)).val = _
  rw [AdelicPairGroup.CM.projection_assemble]
  change SymplecticProduct.CM.pairMatrix
    (Real.SchrodingerAction.CM.projection n (Real.BareGenerators.CM.lower n
      ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩)).val
    (((Finite.ConstructedCover.CM.finiteCover (Fin n)).project
      (Finite.IntegralVacuum.CM.LowerBare.lowerLift (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hB.map _))).val) = _
  rw [Real.BareGenerators.CM.lower_projection, Finite.CoverFields.CM.projection_matrix,
    Finite.IntegralVacuum.CM.LowerBare.lowerLift_projection]
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hij : i = j <;> simp [SymplecticProduct.CM.pairMatrix, RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic,
        Finite.IntegralVacuum.CM.LowerBare.lower, hij]
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j =>
      by_cases hij : i = j <;> simp [SymplecticProduct.CM.pairMatrix, RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic,
        Finite.IntegralVacuum.CM.LowerBare.lower, hij]

theorem operator_conjugation
    (U A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n))
    (V B : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    ProductOperators.CM.operator (U⁻¹ * A * U, V⁻¹ * B * V) =
      (ProductOperators.CM.operator (U, V))⁻¹ *
        ProductOperators.CM.operator (A, B) * ProductOperators.CM.operator (U, V) := by
  change ProductOperators.CM.operator ((U, V)⁻¹ * (A, B) * (U, V)) = _
  rw [map_mul, map_mul, map_inv]

theorem matrix_map_neg {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (B : Matrix (Fin n) (Fin n) K) : (-B).map f = -(B.map f) := by
  apply Matrix.ext
  intro i j
  exact map_neg f (B i j)

theorem finite_lower_action {I : Type*} [Fintype I] (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    Finite.BareNe.CM.Group.bareAction (Finite.IntegralVacuum.CM.LowerBare.lowerLift B hB) =
      (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv (I := I))⁻¹ *
        Finite.Quadratic.CM.finiteQuadratic (-B) * Finite.FourierHeisenberg.CM.Equiv.fourierEquiv := rfl

theorem upper_action (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) :
    Constructed.ConstructedAdelicGroup.CM.action n (Quadratic.CM.upper n B hB) =
      ProductOperators.CM.operator
        (Real.SchrodingerAction.CM.action n (Real.BareGenerators.CM.upper n
          ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩),
        Finite.Quadratic.CM.finiteQuadratic (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))) := by
  change AdelicPairGroup.CM.action _ _ (AdelicPairGroup.CM.assemble _ _ _) = _
  rw [AdelicPairGroup.CM.action_assemble, Finite.CoverFields.CM.action,
    Finite.QuadraticBare.CM.quadraticLift_action]
  rfl

theorem lower_action (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) :
    Constructed.ConstructedAdelicGroup.CM.action n (lower n B hB) = (Fourier.CM.fourierEquiv n)⁻¹ *
      Constructed.ConstructedAdelicGroup.CM.action n (Quadratic.CM.upper n (-B) hB.neg) * Fourier.CM.fourierEquiv n := by
  change AdelicPairGroup.CM.action _ _ (AdelicPairGroup.CM.assemble _ _ _) = _
  rw [AdelicPairGroup.CM.action_assemble, Finite.CoverFields.CM.action, finite_lower_action]
  change ProductOperators.CM.operator
    (Real.SchrodingerAction.CM.action n (Real.BareGenerators.CM.lower n
      ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩),
    (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv (I := Fin n))⁻¹ *
      Finite.Quadratic.CM.finiteQuadratic (-(B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))) *
        Finite.FourierHeisenberg.CM.Equiv.fourierEquiv) = _
  rw [Real.BareGenerators.CM.lower_action, operator_conjugation, upper_action]
  simp only [matrix_map_neg]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Lower.CM
