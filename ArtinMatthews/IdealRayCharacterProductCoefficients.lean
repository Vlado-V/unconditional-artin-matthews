module

public import ArtinMatthews.IdealRayCharacterProduct
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Literal ideal coefficients of a product-modulus character, including
the bad-prime masks. Inversion is complex conjugation on finite-order
ideal values, so the fixed twist has coefficients η(I) conjugate(χ(I)). -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {M N : Ideal (𝓞 K)}

theorem multiplyAtProduct_allCoefficient (η : EvenIdealRayCharacter K M)
    (ψ : EvenIdealRayCharacter K N) (hM : M ≠ ⊥) (hN : N ≠ ⊥) (I : Ideal (𝓞 K)) :
    (η.multiplyAtProduct ψ hM hN).allCoefficient I = η.allCoefficient I * ψ.allCoefficient I := by
  by_cases hI : I = ⊥
  · subst I
    simp only [allCoefficient_bot,zero_mul]
  simp only [allCoefficient,dite_eq_left hI,IsCoprime.mul_right_iff]
  by_cases hcM : IsCoprime I M
  · by_cases hcN : IsCoprime I N
    · simp only [hcM,hcN,and_self,ite_true,multiplyAtProduct_idealHom,Units.val_mul]
    · simp only [hcM,hcN,and_false,ite_false,ite_true,mul_zero]
  · simp only [hcM,false_and,ite_false,zero_mul]

theorem inverse_allCoefficient_conj (ψ : EvenIdealRayCharacter K M) (I : Ideal (𝓞 K)) :
    ψ.inverse.allCoefficient I = starRingEnd ℂ (ψ.allCoefficient I) := by
  by_cases hI : I = ⊥
  · subst I
    simp only [allCoefficient_bot,map_zero]
  rw [ψ.inverse.allCoefficient_eq_coefficient I hI,ψ.allCoefficient_eq_coefficient I hI]
  exact ψ.inverse_coefficient_conj _

theorem twistInverseAtProduct_allCoefficient (η : EvenIdealRayCharacter K M)
    (ψ : EvenIdealRayCharacter K N) (hM : M ≠ ⊥) (hN : N ≠ ⊥) (I : Ideal (𝓞 K)) :
    (η.twistInverseAtProduct ψ hM hN).allCoefficient I =
      η.allCoefficient I * starRingEnd ℂ (ψ.allCoefficient I) := by
  rw [twistInverseAtProduct,multiplyAtProduct_allCoefficient,inverse_allCoefficient_conj]

end
end ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
