module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletion
public import ArtinMatthews.VaryingKummerAnalyticGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaGrowth
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

/-! Genuine subquadratic growth of the canonical proper Hecke completion. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hMt : M ≠ ⊤)

theorem properCompleted_hasSubquadraticGrowth
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    HasSubquadraticGrowth (ψ.properCompleted hM hMt) :=
  ψ.scaledGeneratorCompletedMellin_hasSubquadraticGrowth hM
    (primitiveClassGenerator K M hM hMt) (primitiveClassGenerator_ne_bot K M hM hMt)
    (fun h => hMt (idealConductor_top_of_primitive_residue_one ψ.residue hprim h))
    (mixedConductorScale_pos K (integralIdealFractionalUnit M hM))

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
