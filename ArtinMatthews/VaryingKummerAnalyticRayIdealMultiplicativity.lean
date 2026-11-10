module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine multiplicative coefficients for an arbitrary ideal conductor.
The generic RayEuler proof is specialized to the actual ideal modulus,
retaining the exact zero mask at all noncoprime ideals. -/
namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Set Module Filter Topology
open OAI.PrimeDegreePackets
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace EvenIdealRayCharacter
open EvenRayCharacter (underlyingIdeal underlyingIdeal_ne_bot underlyingIdeal_unit underlyingIdeal_coe)
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

def allCoefficient (I : Ideal (𝓞 K)) : ℂ :=
  if hI : I ≠ ⊥ then
    if IsCoprime I M then
      (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)
    else 0
  else 0

@[simp] lemma allCoefficient_bot : ψ.allCoefficient ⊥ = 0 := by
  simp [allCoefficient]

@[simp] lemma allCoefficient_zero : ψ.allCoefficient 0 = 0 := ψ.allCoefficient_bot

@[simp] lemma allCoefficient_one : ψ.allCoefficient 1 = 1 := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 K)) M :=
    by rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  have ht : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
  simp only [Ideal.one_eq_top, allCoefficient, dite_eq_left ht, hc,
    ite_true, integralIdealFractionalUnit_top, map_one, Units.val_one]

lemma integralUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    integralIdealFractionalUnit (I*J) (mul_ne_zero hI hJ) =
      integralIdealFractionalUnit I hI * integralIdealFractionalUnit J hJ := by
  apply Units.ext
  exact FractionalIdeal.coeIdeal_mul I J

lemma allCoefficient_mul (I J : Ideal (𝓞 K)) :
    ψ.allCoefficient (I*J) = ψ.allCoefficient I * ψ.allCoefficient J := by
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  change I ≠ ⊥ at hI
  change J ≠ ⊥ at hJ
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp only [allCoefficient, dite_eq_left hI, dite_eq_left hJ, dite_eq_left hIJ,
    IsCoprime.mul_left_iff]
  by_cases hcI : IsCoprime I M
  · by_cases hcJ : IsCoprime J M
    · simp only [hcI, hcJ, and_self, ite_true]
      have H := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
        (ψ.idealHom U : ℂ)) (integralUnit_mul I J hI hJ)
      simpa only [map_mul, Units.val_mul] using H
    · simp [hcI, hcJ]
  · simp [hcI]

 

def coefficientHom : Ideal (𝓞 K) →*₀ ℂ where
  toFun := ψ.allCoefficient
  map_zero' := ψ.allCoefficient_zero
  map_one' := ψ.allCoefficient_one
  map_mul' := ψ.allCoefficient_mul

lemma allCoefficient_norm_le_one (I : Ideal (𝓞 K)) :
    ‖ψ.allCoefficient I‖ ≤ 1 := by
  unfold allCoefficient
  split_ifs with hI hc
  · rw [ψ.idealHom_norm]
  · simp
  · simp

lemma allCoefficient_underlying (J : integralFractionalIdeals K) :
    ψ.allCoefficient (underlyingIdeal J) = ψ.coefficient J := by
  rw [allCoefficient, dite_eq_left (underlyingIdeal_ne_bot J)]
  simp only [underlyingIdeal_unit, coefficient]

lemma norm_underlying (J : integralFractionalIdeals K) :
    (Ideal.absNorm (underlyingIdeal J) : ℚ) = FractionalIdeal.absNorm J.val.val := by
  rw [← FractionalIdeal.coeIdeal_absNorm (K := K), underlyingIdeal_coe]



theorem allCoefficient_mul_of_coprime (G L : Ideal (𝓞 K))
    (hG : G ≠ ⊥) (hGM : IsCoprime G M) :
    ψ.allCoefficient (G*L) =
      (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) * ψ.allCoefficient L := by
  rw [ψ.allCoefficient_mul, allCoefficient, dite_eq_left hG, ite_eq_left hGM]

theorem allCoefficient_eq_coefficient (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    ψ.allCoefficient J = ψ.coefficient
      ⟨integralIdealFractionalUnit J hJ, FractionalIdeal.coeIdeal_le_one⟩ := by
  let U : integralFractionalIdeals K :=
    ⟨integralIdealFractionalUnit J hJ, FractionalIdeal.coeIdeal_le_one⟩
  have hU : underlyingIdeal U = J := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    exact EvenRayCharacter.underlyingIdeal_coe U
  exact (congrArg ψ.allCoefficient hU).symm.trans (ψ.allCoefficient_underlying U)

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
