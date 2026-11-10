module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup
public import OAI.RepresentationTheory.Theta.Convergence
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Nonzero


set_option backward.privateInPublic true
@[expose] public section

/-! # Theta Graph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.ThetaGraph.CM

noncomputable section

/-! The actual rational theta-preserving graph. Its identity fiber is
trivial by the proved two-fold kernel and a nonzero actual theta value.
Projection surjectivity remains the generator realization obligation. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
variable (n : ℕ)

def graph : Subgroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ × Constructed.ConstructedAdelicGroup.CM.AdelicGroup n) where
  carrier := {a | Constructed.ConstructedAdelicGroup.CM.projection n a.2 = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) a.1 ∧
    ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n), RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n a.2 f) = RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional f}
  one_mem' := by
    constructor
    · exact (Constructed.ConstructedAdelicGroup.CM.projection n).map_one.trans (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)).map_one.symm
    · intro f
      rw [Prod.snd_one, map_one]
      rfl
  mul_mem' := by
    rintro ⟨γ, a⟩ ⟨δ, b⟩ ⟨ha, hθa⟩ ⟨hb, hθb⟩
    constructor
    · change Constructed.ConstructedAdelicGroup.CM.projection n (a * b) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (γ * δ)
      rw [map_mul, map_mul, ha, hb]
    · intro f
      change RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n (a * b) f) = _
      rw [map_mul]
      change RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n a (Constructed.ConstructedAdelicGroup.CM.action n b f)) = _
      rw [hθa, hθb]
  inv_mem' := by
    rintro ⟨γ, a⟩ ⟨ha, hθ⟩
    constructor
    · change Constructed.ConstructedAdelicGroup.CM.projection n a⁻¹ = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) γ⁻¹
      rw [map_inv, map_inv, ha]
    · intro f
      change RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n a⁻¹ f) = _
      have h := hθ (Constructed.ConstructedAdelicGroup.CM.action n a⁻¹ f)
      rw [map_inv] at h
      change RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n a ((Constructed.ConstructedAdelicGroup.CM.action n a).symm f)) = _ at h
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm

theorem identity_fiber (a : Constructed.ConstructedAdelicGroup.CM.AdelicGroup n) (ha : ((1, a) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ × Constructed.ConstructedAdelicGroup.CM.AdelicGroup n) ∈ graph n) : a = 1 := by
  have hp : Constructed.ConstructedAdelicGroup.CM.projection n a = 1 := ha.1.trans (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)).map_one
  rcases (Constructed.ConstructedAdelicGroup.CM.kernel n a).mp hp with h | rfl
  · exact h
  · have hθ := ha.2 (Theta.Nonzero.CM.test (Fin n))
    rw [Constructed.ConstructedAdelicGroup.CM.genuine] at hθ
    rw [map_neg] at hθ
    have hz : RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Theta.Nonzero.CM.test (Fin n)) = 0 := by
      have htwo : (2 : ℂ) * RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Theta.Nonzero.CM.test (Fin n)) = 0 := by
        linear_combination -hθ
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact False.elim (Theta.Nonzero.CM.theta_ne_zero (Fin n) hz)

def rationalProjection : graph n →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ := (MonoidHom.fst _ _).comp (graph n).subtype

theorem rationalProjection_injective : Function.Injective (rationalProjection n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hγ : a.val.1 = 1 := ha
  have hm : ((1, a.val.2) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ × Constructed.ConstructedAdelicGroup.CM.AdelicGroup n) ∈ graph n := by
    have hp : (1, a.val.2) = a.val := Prod.ext hγ.symm rfl
    rw [hp]
    exact a.property
  have he : a = 1 := by
    apply Subtype.ext
    exact Prod.ext hγ (identity_fiber n a.val.2 hm)
  exact he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.ThetaGraph.CM
