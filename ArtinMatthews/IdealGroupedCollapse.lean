module

public import ArtinMatthews.IdealGroupedBudget
public import ArtinMatthews.IdealFiberCollapse


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary ordered-tuple tests collapse to numeric coefficients with
the actual factorial harmonic atom budget. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem idealGroupedCollapse_energy_le (P : G → Finset ℕ) (k : G → ℕ)
    (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hV : ∀ g, 0 < bandReciprocalMass (P g))
    (f : IdealGroupedLabels P k → ℂ) (S : Finset ℕ) {U : ℝ} (hU : 0 < U)
    (hS : ∀ n ∈ S, U ≤ (n : ℝ)) :
    (∑ n ∈ S, ‖idealFiberCoefficient (idealGroupedMass P k) idealGroupedProduct f n‖^2) ≤
      (idealGroupedAtomBudget P k / U) * idealFrameEnergy (idealGroupedMass P k) f := by
  have hbudget : 0 ≤ idealGroupedAtomBudget P k := by
    unfold idealGroupedAtomBudget
    exact prod_nonneg fun g _ => mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (inv_nonneg.mpr (hV g).le) _)
  apply idealFiberCoefficient_energy_le _ (idealGroupedMass_nonneg P k hV) _ f S
    (div_nonneg hbudget hU.le)
  intro n hn
  change idealGroupedProductMass P k n ≤ _
  exact (idealGroupedProductMass_le P k hP hdis hV n).trans
    (div_le_div_of_nonneg_left hbudget hU (hS n hn))

theorem idealGroupedCollapse_power (P : G → Finset ℕ) (k : G → ℕ)
    (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    {m : ℕ} {C₀ v₀ L U : ℝ} (hv₀ : 0 < v₀) (hL : 1 ≤ L) (hU : 0 < U)
    (hV : ∀ g, v₀ ≤ bandReciprocalMass (P g)) (hk : ∀ g, k g ≤ m)
    (hcard : (Fintype.card G : ℝ) ≤ C₀*Real.log L)
    (f : IdealGroupedLabels P k → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, U ≤ (n : ℝ)) :
    (∑ n ∈ S, ‖idealFiberCoefficient (idealGroupedMass P k) idealGroupedProduct f n‖^2) ≤
      (L^(idealGroupedBudgetExponent m C₀ v₀)/U) * idealFrameEnergy (idealGroupedMass P k) f := by
  have hVpos : ∀ g, 0 < bandReciprocalMass (P g) := fun g => hv₀.trans_le (hV g)
  exact (idealGroupedCollapse_energy_le P k hP hdis hVpos f S hU hS).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (idealGroupedAtomBudget_power P k hv₀ hL hV hk hcard) hU.le)
      (idealFrameEnergy_nonneg _ (idealGroupedMass_nonneg P k hVpos) f))

end
end ArtinMatthews
