module

public import ArtinMatthews.MarkedPhysicalPathArrays
public import ArtinMatthews.MarkedPhysicalJointPrimeDamping
public import ArtinMatthews.MarkedMemoryOrphanParameterBounds
public import ArtinMatthews.MarkedPhysicalPathUsedBudget
public import ArtinMatthews.MarkedRawRootArcGrowth
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
public import Mathlib.RingTheory.WittVector.IsPoly
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual used-prime modulus budget follows directly from every
literal ordered label path. Repeated prime labels are retained by the
input and counted once by the actual union of used primes. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedPhysicalActualUsedProduct_bound
    {J : Type*} [Fintype J] (e : J → ℝ) {x : ℝ}
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ))
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)) :
    ((∏ p∈markedPhysicalPathUsedPrimes Finset.univ a,p:ℕ):ℝ) ≤
      Real.exp (16*(Fintype.card J:ℝ)*(Real.log x)^(18/25:ℝ)) := by
  have hL : 0 < Real.log x := by linarith
  have hn := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hm := markedPadSlots_pow_le 1 hlog
  simp only [pow_one,Nat.cast_one,div_eq_mul_inv,one_mul] at hm
  have hNM := mul_le_mul hn hm (Nat.cast_nonneg _) (by positivity)
  have heq : (Real.log x)^(1/2:ℝ)*(Real.log x)^(1/100:ℝ)=(Real.log x)^(51/100:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hnm : ((markedMemoryMomentLength x:ℝ)+1)*(markedPadSlots x:ℝ) ≤
      8*(Real.log x)^(51/100:ℝ) := by nlinarith
  have hprime : (Real.log x)^(51/100:ℝ)*(Real.log x)^(1/5:ℝ)=(Real.log x)^(71/100:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hinc : (Real.log x)^(71/100:ℝ) ≤ (Real.log x)^(18/25:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hcost : ((markedMemoryMomentLength x:ℝ)+1)*(Fintype.card J:ℝ)*(markedPadSlots x:ℝ)*
      (2*(Real.log x)^(1/5:ℝ)) ≤ 16*(Fintype.card J:ℝ)*(Real.log x)^(18/25:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hnm
      (show 0 ≤ 2*(Fintype.card J:ℝ)*(Real.log x)^(1/5:ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hinc (show 0 ≤ 16*(Fintype.card J:ℝ) by positivity)
    nlinarith
  have hprod := markedPhysicalPathUsedPrimes_prod_le_exp Finset.univ a (2*(Real.log x)^(1/5:ℝ))
    (by positivity) (fun j p hp => markedRootArc_band_prime_le hlog (he j) hp)
  have hp : ((∏ p∈markedPhysicalPathUsedPrimes Finset.univ a,p:ℕ):ℝ) ≤
      Real.exp (((markedMemoryMomentLength x:ℝ)+1)*(Fintype.card J:ℝ)*(markedPadSlots x:ℝ)*
        (2*(Real.log x)^(1/5:ℝ))) := by
    simpa only [Nat.cast_prod,Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hprod
  exact hp.trans (Real.exp_le_exp.mpr hcost)

end
end ArtinMatthews
