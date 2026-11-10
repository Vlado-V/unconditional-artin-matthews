module

public import ArtinMatthews.MarkedPhysicalCoordinateRootPolynomial
public import ArtinMatthews.MarkedPhysicalIndexBonferroni
public import ArtinMatthews.MarkedPhysicalIndexPolynomialRootSum
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


set_option backward.privateInPublic true
@[expose] public section

/-! The positive source tail is the sum of its actual selected-modulus
monomials. This equality preserves the original complex coefficient. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalIndexTail_fixed_root_sum
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q : ℝ) {R : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) R) (hR : 1 ≤ R)
    (q U Vr : ℝ) (hU : 1 < U) (hVr : 1 < Vr) (S : ℕ) [NeZero S] (k : ℕ) :
    markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i *
      (∑ r : MarkedPhysicalCanonicalRoot S U (16*U) Vr (2*Vr),
        (markedPhysicalIndexTailWeight e x d₀ Y U Vr i hR q k r:ℂ))=
      if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0) then
        ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
          markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard k,
          markedPhysicalCoordinateSelectedRoot e x V ψ η d₀ Y Q i hR q U Vr T
      else 0 := by
  let C := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
  let E := markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
    markedPhysicalPathUsedPrimes Finset.univ i.1
  change C * (∑ r : MarkedPhysicalCanonicalRoot S U (16*U) Vr (2*Vr),
    (markedPhysicalIndexTailWeight e x d₀ Y U Vr i hR q k r:ℂ)) = _
  calc
    _ = ∑ T ∈ E.powersetCard k,C * ∑ r : MarkedPhysicalCanonicalRoot S U (16*U) Vr (2*Vr),
        markedPhysicalIndexMonomialWeight e x d₀ Y U Vr i hR q T r := by
      simp_rw [markedPhysicalIndexTailWeight_monomials]
      rw [Finset.sum_comm,Finset.mul_sum]
    _ = ∑ T ∈ E.powersetCard k,
        (if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0) then
          markedPhysicalCoordinateSelectedRoot e x V ψ η d₀ Y Q i hR q U Vr T else 0) := by
      apply Finset.sum_congr rfl
      intro T hT
      exact markedPhysicalIndexMonomial_fixed_root_sum e x V ψ η d₀ Y Q i hR q U Vr hU hVr S T
        (fun p hp => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1)
    _ = _ := by
      split_ifs <;> simp [E]

end
end ArtinMatthews
