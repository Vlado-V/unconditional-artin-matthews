module

public import ArtinMatthews.GiantSinglePrimeResidue
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Finite active runs and scalar row charges

A run starts at an active visit with no active immediate predecessor.
The literal tilted birth atom and local row coefficients give one
reciprocal-prime charge and one inverse volume per active run.
-/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def giantSignedActiveRunStarts {n : ℕ} (A : Finset (Fin n)) : Finset (Fin n) :=
  A.filter (fun i => ¬∃ j ∈ A, j.val + 1 = i.val)

def giantSignedActiveRunCount {n : ℕ} (A : Finset (Fin n)) : ℕ :=
  (giantSignedActiveRunStarts A).card

theorem giantSignedActiveRunStarts_first {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty) :
    A.min' hA ∈ giantSignedActiveRunStarts A := by
  apply Finset.mem_filter.mpr
  refine ⟨A.min'_mem hA, ?_⟩
  rintro ⟨j, hj, hpred⟩
  have hle := A.min'_le j hj
  change (A.min' hA).val ≤ j.val at hle
  omega

theorem giantSignedActiveRunCount_pos {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty) :
    0 < giantSignedActiveRunCount A :=
  Finset.card_pos.mpr ⟨A.min' hA, giantSignedActiveRunStarts_first A hA⟩

@[simp] theorem giantSignedActiveRunCount_empty {n : ℕ} :
    giantSignedActiveRunCount (∅ : Finset (Fin n)) = 0 := by
  simp only [giantSignedActiveRunCount, giantSignedActiveRunStarts, Finset.filter_empty, Finset.card_empty]

/-- The literal source tilted birth atom. -/
def giantSignedRowBirthAtom (V : ℝ) (p : ℕ) {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  1 / (V * (p : ℝ) * giantSignedPrimeResidueBaseline p q)

def giantSignedRowA (q ρ : ℝ) : ℝ := q / ρ ^ 2

def giantSignedRowC (q V ρ : ℝ) : ℝ := -(1 - q) * V / ρ

def giantSignedRowD (q ρ : ℝ) : ℝ := -(1 - q) / ρ

theorem giantSignedRowA_cancel (q ρ : ℝ) (hρ : ρ ≠ 0) :
    ρ * giantSignedRowA q ρ * ρ = q := by
  unfold giantSignedRowA
  field_simp

theorem giantSignedRowC_cancel (q V ρ : ℝ) (hρ : ρ ≠ 0) :
    giantSignedRowC q V ρ * ρ = -(1 - q) * V := by
  unfold giantSignedRowC
  field_simp

theorem giantSignedRowD_cancel (q ρ : ℝ) (hρ : ρ ≠ 0) :
    ρ * giantSignedRowD q ρ = -(1 - q) := by
  unfold giantSignedRowD
  field_simp

theorem giantSignedRowBirthAtom_factor (V : ℝ) (p : ℕ) {n : ℕ} (q : Fin n → ℝ) :
    giantSignedRowBirthAtom V p q = V⁻¹ * (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q)) := by
  simp only [giantSignedRowBirthAtom, one_div, mul_inv_rev]
  ring

/-- An active first birth pays the birth atom and the remaining run promotions. -/
theorem giantSignedActiveFirst_runCharge (V : ℝ) (p : ℕ) {n : ℕ} (q : Fin n → ℝ)
    (A : Finset (Fin n)) (hA : A.Nonempty) :
    giantSignedRowBirthAtom V p q * (V⁻¹) ^ (giantSignedActiveRunCount A - 1) =
      (V⁻¹) ^ giantSignedActiveRunCount A *
        (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q)) := by
  rw [giantSignedRowBirthAtom_factor]
  calc
    _ = ((V⁻¹) ^ (giantSignedActiveRunCount A - 1) * V⁻¹) *
        (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q)) := by ring
    _ = _ := by
      rw [← pow_succ, Nat.sub_add_cancel (giantSignedActiveRunCount_pos A hA)]

/-- A ghost first birth contributes the compensating volume and every active run promotion. -/
theorem giantSignedGhostFirst_runCharge (V : ℝ) (hV : V ≠ 0) (p : ℕ) {n : ℕ}
    (q : Fin n → ℝ) (A : Finset (Fin n)) :
    (V * giantSignedRowBirthAtom V p q) * (V⁻¹) ^ giantSignedActiveRunCount A =
      (V⁻¹) ^ giantSignedActiveRunCount A *
        (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q)) := by
  rw [giantSignedRowBirthAtom_factor]
  field_simp

/-- The first-birth flag selects the exact promotion count. -/
theorem giantSignedFlagged_runCharge (V : ℝ) (hV : V ≠ 0) (p : ℕ) {n : ℕ}
    (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty) (ghostBirth : Bool) :
    (if ghostBirth then
      (V * giantSignedRowBirthAtom V p q) * (V⁻¹) ^ giantSignedActiveRunCount A
    else
      giantSignedRowBirthAtom V p q * (V⁻¹) ^ (giantSignedActiveRunCount A - 1)) =
        (V⁻¹) ^ giantSignedActiveRunCount A *
          (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q)) := by
  cases ghostBirth
  · exact giantSignedActiveFirst_runCharge V p q A hA
  · exact giantSignedGhostFirst_runCharge V hV p q A

/-- A represented orphan has zero active runs and one ghost birth cost. -/
theorem giantSignedOrphan_runCharge (V : ℝ) (hV : V ≠ 0) (p : ℕ) {n : ℕ} (q : Fin n → ℝ) :
    (V * giantSignedRowBirthAtom V p q) * (V⁻¹) ^ giantSignedActiveRunCount (∅ : Finset (Fin n)) =
      1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q) := by
  simpa only [giantSignedActiveRunCount_empty, pow_zero, one_mul] using
    giantSignedGhostFirst_runCharge V hV p q (∅ : Finset (Fin n))

end
end ArtinMatthews
