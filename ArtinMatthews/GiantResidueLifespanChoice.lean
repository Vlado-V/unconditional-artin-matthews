module

public import ArtinMatthews.GiantSinglePrimeInterval
public import Mathlib.Algebra.Group.End
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! Finite active and absent/orphan choices for one numeric prime. -/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual active set selects the applicable endpoint family. -/
def GiantSignedResidueLifespanChoice {k : ℕ} (A : Finset (Fin k)) : Type :=
  if hA : A.Nonempty then GiantSignedPrimeActiveEndpointChoice A hA
  else Option (GiantSignedPrimeOrphanEndpointChoice k)

def giantSignedResidueLifespanActiveEquiv {k : ℕ} (A : Finset (Fin k)) (hA : A.Nonempty) :
    GiantSignedResidueLifespanChoice A ≃ GiantSignedPrimeActiveEndpointChoice A hA :=
  Equiv.cast (by simp only [GiantSignedResidueLifespanChoice, dite_eq_left hA])

def giantSignedResidueLifespanInactiveEquiv {k : ℕ} (A : Finset (Fin k)) (hA : ¬A.Nonempty) :
    GiantSignedResidueLifespanChoice A ≃ Option (GiantSignedPrimeOrphanEndpointChoice k) :=
  Equiv.cast (by simp only [GiantSignedResidueLifespanChoice, dite_eq_right hA])

instance giantSignedResidueLifespanChoice_fintype {k : ℕ} (A : Finset (Fin k)) :
    Fintype (GiantSignedResidueLifespanChoice A) :=
  if hA : A.Nonempty then
    Fintype.ofEquiv _ (giantSignedResidueLifespanActiveEquiv A hA).symm
  else
    Fintype.ofEquiv _ (giantSignedResidueLifespanInactiveEquiv A hA).symm

/-- A represented prime pays its reciprocal once; an absent prime pays its baseline. -/
def giantSignedResidueLifespanWeight (p : ℕ) {k : ℕ} (offset : Fin k → ℤ)
    (q : Fin k → ℝ) (A : Finset (Fin k)) (c : GiantSignedResidueLifespanChoice A) : ℝ :=
  if hA : A.Nonempty then
    (1 / (p : ℝ)) * giantSignedPrimeActiveEndpointWeight p offset q A hA
      (giantSignedResidueLifespanActiveEquiv A hA c)
  else
    (giantSignedResidueLifespanInactiveEquiv A hA c).elim
      (giantSignedPrimeResidueBaseline p q)
      (fun e => (1 / (p : ℝ)) * giantSignedPrimeOrphanEndpointWeight p offset q e)

theorem giantSignedPrimeResidueExpectation_choice_sum (p : ℕ) [NeZero p] {k : ℕ}
    (offset : Fin k → ℤ) (q : Fin k → ℝ) (A : Finset (Fin k)) :
    giantSignedPrimeResidueExpectation p offset q A =
      ∑ c : GiantSignedResidueLifespanChoice A, giantSignedResidueLifespanWeight p offset q A c := by
  by_cases hA : A.Nonempty
  · calc
      _ = ∑ e : GiantSignedPrimeActiveEndpointChoice A hA,
          (1 / (p : ℝ)) * giantSignedPrimeActiveEndpointWeight p offset q A hA e := by
            rw [giantSignedPrimeResidueExpectation_lifespans p offset q A hA, Finset.mul_sum]
      _ = ∑ c : GiantSignedResidueLifespanChoice A,
          (1 / (p : ℝ)) * giantSignedPrimeActiveEndpointWeight p offset q A hA
            (giantSignedResidueLifespanActiveEquiv A hA c) :=
              ((giantSignedResidueLifespanActiveEquiv A hA).sum_comp _).symm
      _ = _ := by simp only [giantSignedResidueLifespanWeight, dite_eq_left hA]
  · have hAE : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    calc
      _ = giantSignedPrimeResidueBaseline p q + (1 / (p : ℝ)) *
          ∑ e : GiantSignedPrimeOrphanEndpointChoice k, giantSignedPrimeOrphanEndpointWeight p offset q e := by
            rw [hAE, giantSignedPrimeResidueExpectation_orphan_lifespans]
      _ = ∑ e : Option (GiantSignedPrimeOrphanEndpointChoice k),
          e.elim (giantSignedPrimeResidueBaseline p q)
            (fun e => (1 / (p : ℝ)) * giantSignedPrimeOrphanEndpointWeight p offset q e) := by
              rw [Fintype.sum_option]
              simp only [Option.elim_none, Option.elim_some, Finset.mul_sum]
      _ = ∑ c : GiantSignedResidueLifespanChoice A,
          (giantSignedResidueLifespanInactiveEquiv A hA c).elim (giantSignedPrimeResidueBaseline p q)
            (fun e => (1 / (p : ℝ)) * giantSignedPrimeOrphanEndpointWeight p offset q e) :=
              ((giantSignedResidueLifespanInactiveEquiv A hA).sum_comp _).symm
      _ = _ := by simp only [giantSignedResidueLifespanWeight, dite_eq_right hA]

end
end ArtinMatthews
