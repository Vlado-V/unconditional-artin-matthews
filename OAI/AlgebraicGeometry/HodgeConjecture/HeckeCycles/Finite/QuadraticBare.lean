module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Doubling
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe
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

/-! # Quadratic Bare -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.QuadraticBare.CM

noncomputable section

/-! Every finite quadratic multiplier lies in the intrinsic bare
group: it is the actual commutator with the constructed doubling
oscillator. No chosen lift or scalar comparison is assumed. -/

open scoped Classical _root_.Matrix commutatorElement
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Doubling.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group

variable {I : Type*} [Fintype I]

theorem quadratic_doubling (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • x) =
      RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x + RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) x := by
  rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_smul_vector, RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_smul_matrix]
  have hc : (2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ^ 2 * algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) = 1 + algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) := by
    have h := congrArg (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
      (show (2 : ℚ) ^ 2 * (1 / 3) = 1 + 1 / 3 by norm_num)
    simpa only [map_mul, map_pow, map_add, map_one, map_ofNat] using h
  rw [← mul_assoc, hc, add_mul, one_mul]

theorem operator_commutator (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    ⁅(Doubling.CM.doubling (I := I)), Quadratic.CM.finiteQuadratic (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B)⁆ = Quadratic.CM.finiteQuadratic B := by
  have hrel : (Doubling.CM.doubling (I := I)) * Quadratic.CM.finiteQuadratic (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) =
      Quadratic.CM.finiteQuadratic B * Quadratic.CM.finiteQuadratic (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) * (Doubling.CM.doubling (I := I)) := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    change ((Doubling.CM.doubling (I := I)) (Quadratic.CM.finiteQuadratic (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) f)).val x =
      (Quadratic.CM.finiteQuadratic B (Quadratic.CM.finiteQuadratic (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) ((Doubling.CM.doubling (I := I)) f))).val x
    rw [Doubling.CM.doubling_apply, Quadratic.CM.finiteQuadratic_apply, Quadratic.CM.finiteQuadratic_apply,
      Quadratic.CM.finiteQuadratic_apply, Doubling.CM.doubling_apply, quadratic_doubling,
      Constructed.AdelicCharacter.CM.Finite.character.map_add_eq_mul]
    ring
  rw [commutatorElement_def, hrel]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem oscillator_commutator (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    ⁅(Doubling.CM.doublingOscillator (I := I)), Quadratic.CM.quadraticOscillator (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) (hB.smul _)⁆ =
      Quadratic.CM.quadraticOscillator B hB := by
  apply BareNe.CM.OscillatorKernel.faithful
  change (FiniteOscillator.CM.projection _, FiniteOscillator.CM.action _) = (FiniteOscillator.CM.projection _, FiniteOscillator.CM.action _)
  apply Prod.ext
  · change ⁅RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.rationalDoubleSymplectic (ι := I)),
        RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) (hB.smul _)⁆ = RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB
    exact RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.rationalDouble_upper_commutator B hB
  · change ⁅(Doubling.CM.doubling (I := I)), Quadratic.CM.finiteQuadratic (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B)⁆ = Quadratic.CM.finiteQuadratic B
    exact operator_commutator B

theorem quadratic_mem (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    Quadratic.CM.quadraticOscillator B hB ∈ BareNe.CM.Group.bareSubgroup := by
  rw [← oscillator_commutator B hB]
  exact Subgroup.subset_closure (Or.inl ⟨_, _, rfl⟩)

def quadraticLift (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) : BareNe.CM.Group.BareGroup (I := I) :=
  ⟨Quadratic.CM.quadraticOscillator B hB, quadratic_mem B hB⟩

theorem quadraticLift_projection (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    BareNe.CM.Group.bareProjection (quadraticLift B hB) = RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB := rfl

theorem quadraticLift_action (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    BareNe.CM.Group.bareAction (quadraticLift B hB) = Quadratic.CM.finiteQuadratic B := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.QuadraticBare.CM
