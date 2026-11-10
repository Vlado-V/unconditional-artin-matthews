module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LocalCharacter
public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
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
public import OAI.RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor


set_option backward.privateInPublic true
@[expose] public section

/-! # Padic Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter.CM

noncomputable section

/-! The constructed local character in concrete p-adic coordinates. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor.Realization
variable (q : ℕ) [Fact q.Prime]

def character : AddChar ℚ_[q] ℂ :=
  Constructed.AdelicCharacter.CM.Finite.character.compAddMonoidHom (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q).toAddMonoidHom

theorem character_apply (x : ℚ_[q]) :
    character q x = Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q x) := rfl

theorem character_local (x : ℚ_[q]) :
    character q x = Finite.LocalCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv q x) := rfl

theorem character_continuous : Continuous (character q) :=
  Constructed.AdelicCharacter.CM.Finite.character_continuous.comp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion_continuous q)

theorem character_unitary (x : ℚ_[q]) : ‖character q x‖ = 1 :=
  Constructed.AdelicCharacter.CM.Finite.character_unitary _

theorem character_eq_one_iff (x : ℚ_[q]) : character q x = 1 ↔ ‖x‖ ≤ 1 := by
  rw [character_apply, Constructed.AdelicCharacter.CM.Finite.character_eq_one_iff]
  constructor
  · intro hx
    have h := RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_integral_norm q _ hx
    rwa [RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_inclusion] at h
  · exact RepresentationTheory.Hecke.RadialDilation.LocalCharacterConductor.Realization.finitePadicInclusion_integral q x

theorem character_nontrivial : ∃ x : ℚ_[q], character q x ≠ 1 := by
  refine ⟨(q : ℚ_[q])⁻¹, ?_⟩
  intro h
  rw [character_apply] at h
  exact RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion_inverse_prime_not_integral q
    ((Constructed.AdelicCharacter.CM.Finite.character_eq_one_iff _).mp h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter.CM
