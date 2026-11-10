module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleClearing
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

/-! A canonical genuine proper-conductor Hecke completion. The chosen
coprime generator quotients depend only on the field, conductor, and fixed
ordinary ideal-class representatives, hence are shared by inverse characters. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hMt : M ≠ ⊤)

def primitiveClassGenerator (c : ClassGroup (𝓞 K)) : Ideal (𝓞 K) :=
  (exists_idealModule_generator_coprime_quotient (rayClassRepresentative K 1 c) M
    (rayClassRepresentative_ne_bot K 1 c) hM hMt).choose

theorem primitiveClassGenerator_ne_bot (c : ClassGroup (𝓞 K)) :
    primitiveClassGenerator K M hM hMt c ≠ ⊥ :=
  (exists_idealModule_generator_coprime_quotient (rayClassRepresentative K 1 c) M
    (rayClassRepresentative_ne_bot K 1 c) hM hMt).choose_spec.1

theorem primitiveClassGenerator_coprime (c : ClassGroup (𝓞 K)) :
    IsCoprime (primitiveClassGenerator K M hM hMt c) M :=
  (exists_idealModule_generator_coprime_quotient (rayClassRepresentative K 1 c) M
    (rayClassRepresentative_ne_bot K 1 c) hM hMt).choose_spec.2.1

theorem primitiveClassGenerator_product (c : ClassGroup (𝓞 K)) :
    Ideal.span {(idealModuleGenerator (rayClassRepresentative K 1 c) M
      (rayClassRepresentative_ne_bot K 1 c) hM)} =
      rayClassRepresentative K 1 c * primitiveClassGenerator K M hM hMt c :=
  (exists_idealModule_generator_coprime_quotient (rayClassRepresentative K 1 c) M
    (rayClassRepresentative_ne_bot K 1 c) hM hMt).choose_spec.2.2

namespace EvenIdealRayCharacter
variable {K M} (ψ : EvenIdealRayCharacter K M)

def properCompleted : ℂ → ℂ :=
  ψ.generatorCompletedHecke hM (primitiveClassGenerator K M hM hMt)
    (primitiveClassGenerator_ne_bot K M hM hMt)

theorem properCompleted_entire (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    Differentiable ℂ (ψ.properCompleted hM hMt) := by
  apply ψ.generatorCompletedHecke_entire
  exact fun h => hMt (idealConductor_top_of_primitive_residue_one ψ.residue hprim h)

theorem properCompleted_eq_gamma_dirichlet
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.properCompleted hM hMt s =
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s *
        mixedGammaFactor K s * ψ.dirichlet s := by
  unfold properCompleted generatorCompletedHecke
  rw [ψ.generatorCompletedMellin_eq_gamma_dirichlet hM _ _ hMt
    (primitiveClassGenerator_coprime K M hM hMt) (primitiveClassGenerator_product K M hM hMt)
    (fun h => hMt (idealConductor_top_of_primitive_residue_one ψ.residue hprim h)) hs]
  ring

theorem properCompleted_eq_gamma_primitive
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {s : ℂ} (hs : 1 < s.re) :
    ψ.properCompleted hM hMt s =
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s *
        mixedGammaFactor K s * ψ.primitiveContinued hM hprim s := by
  rw [ψ.properCompleted_eq_gamma_dirichlet hM hMt hprim hs,
    ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs]

theorem properCompleted_functionalEquation
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ s : ℂ,
      ψ.properCompleted hM hMt s = W * ψ.inverse.properCompleted hM hMt (1-s) :=
  ψ.generatorCompletedHecke_functionalEquation hM _ _ hMt
    (primitiveClassGenerator_coprime K M hM hMt) (primitiveClassGenerator_product K M hM hMt)
    (fun h => hMt (idealConductor_top_of_primitive_residue_one ψ.residue hprim h)) hprim

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
