module

public import ArtinMatthews.MarkedTypeIIDyadQuotient
public import ArtinMatthews.MarkedTypeIILabelDyads
public import ArtinMatthews.MarkedTypeIILabelDyadBudget
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite summation of the selected-label dyadic terms. The
actual quotient damping is unchanged by this partition. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Classical
noncomputable section

theorem markedTypeIISelectedLabelDyadSum_reassemble {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M N : Finset ℕ) (α β F : ℕ → ℂ)
    (hpartition : ∀ a∈markedMajorLabelSet P,
      (∑ j∈markedTypeIILabelDyadIndices (markedMajorLabelSet P),
        markedTypeIILabelCutoff ((a:ℝ)/(2:ℝ)^j))=1) :
    (∑ j∈markedTypeIILabelDyadIndices (markedMajorLabelSet P),
      markedTypeIISelectedLabelDyadSum P ((2:ℝ)^j) M N α β F) =
    ∑ a∈markedMajorLabelSet P,∑ m∈M,∑ n∈N,if a∣m*n-1 then
      markedTypeIIQuotientDampedCore P F ((m*n-1)/a)*(markedMajorLabelMass P:ℂ)*α m*β n else 0 := by
  unfold markedTypeIISelectedLabelDyadSum
  simp_rw [giantMarkedEndpoints_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp only [giantMarkedEndpoint,MarkedTypeIIEndpoint.value]
  by_cases hd : a∣m*n-1
  · let c := markedTypeIIQuotientDampedCore P F ((m*n-1)/a)*(markedMajorLabelMass P:ℂ)*α m*β n
    calc
      _ = c*∑ j∈markedTypeIILabelDyadIndices (markedMajorLabelSet P),
          markedTypeIILabelCutoff ((a:ℝ)/(2:ℝ)^j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        calc
          _ = markedTypeIIQuotientDampedCore P F ((m*n-1)/a)*
              markedTypeIILabelEndpointCoefficient P ((2:ℝ)^j) α β (giantMarkedEndpoint a m n) := ite_eq_left hd
          _ = _ := by
            unfold markedTypeIILabelEndpointCoefficient
            dsimp only [c,giantMarkedEndpoint]
            ring
      _ = c := by rw [hpartition a ha,mul_one]
      _ = _ := (ite_eq_left hd).symm
  · have hz : (∑ j∈markedTypeIILabelDyadIndices (markedMajorLabelSet P),
        if a∣m*n-1 then markedTypeIIQuotientDampedCore P F ((m*n-1)/a)*
          markedTypeIILabelEndpointCoefficient P ((2:ℝ)^j) α β (giantMarkedEndpoint a m n) else 0)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right hd
    exact hz.trans (ite_eq_right hd).symm

theorem markedTypeII_actual_label_dyad_reassembly {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (heUpper : ∀ j,e j≤(1/5:ℝ))
    (hgroups : 2≤Fintype.card J) :
    ∀ᶠ x : ℝ in atTop,∀ (M N : Finset ℕ) (α β F : ℕ → ℂ),
      let P := fun j => markedLogPowerBand (e j) x
      (∑ j∈markedTypeIILabelDyadIndices (markedMajorLabelSet P),
        markedTypeIISelectedLabelDyadSum P ((2:ℝ)^j) M N α β F) =
      ∑ a∈markedMajorLabelSet P,∑ m∈M,∑ n∈N,if a∣m*n-1 then
        markedTypeIIQuotientDampedCore P F ((m*n-1)/a)*(markedMajorLabelMass P:ℂ)*α m*β n else 0 := by
  filter_upwards [markedTypeII_actual_label_dyads e he heUpper hgroups] with x hx
  intro M N α β F
  exact markedTypeIISelectedLabelDyadSum_reassemble _ M N α β F hx.2.2

end
end ArtinMatthews
