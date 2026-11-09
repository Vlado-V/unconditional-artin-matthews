module

public import ArtinMatthews.IdealResidualFamily


set_option backward.privateInPublic true
@[expose] public section

/-! The full source family has a fixed exponential cost in the probe
count. The copied-list length does not occur in this bound. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealResidualPatterns_card_le {J : Type*} [DecidableEq J] {k : ℕ}
    (probes₁ probes₂ : Finset (J × Fin k)) :
    (idealResidualPatterns probes₁ probes₂).card ≤ 1+2^(probes₁.card+probes₂.card) := by
  have h₁ : (probes₁.powerset.erase ∅).card ≤ 2^probes₁.card :=
    card_erase_le.trans_eq (card_powerset probes₁)
  have h₂ : (probes₂.powerset.erase ∅).card ≤ 2^probes₂.card :=
    card_erase_le.trans_eq (card_powerset probes₂)
  unfold idealResidualPatterns
  calc
    _ ≤ ({none} : Finset (IdealResidualPattern J k)).card+
        ((probes₁.powerset.erase ∅ ×ˢ probes₂.powerset.erase ∅).image some).card := card_union_le _ _
    _ ≤ 1+(probes₁.powerset.erase ∅ ×ˢ probes₂.powerset.erase ∅).card := by
      rw [card_singleton]
      exact Nat.add_le_add_left (card_image_le) 1
    _ ≤ 1+2^(probes₁.card+probes₂.card) := by
      rw [card_product,pow_add]
      exact Nat.add_le_add_left (Nat.mul_le_mul h₁ h₂) 1

theorem idealResidualCoefficient_total_cost {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {k ell : ℕ} (probes₁ probes₂ : Finset (J × Fin k))
    (Q : ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (a b : IdealResidualPattern J k → MarkedPhysicalMarking P (k+ell))
    (aux : ∀ ν,GiantTwoSidedPatternAuxiliary P (idealResidualCopied ν)) :
    (∑ ν∈idealResidualPatterns probes₁ probes₂,‖idealResidualCoefficient P Q h ξ ν (a ν) (b ν) (aux ν)‖) ≤
      ((1+2^(probes₁.card+probes₂.card):ℕ):ℝ)*(1+((Q:ℝ)^2/ξ)^2) := by
  calc
    _ ≤ ∑ _ν∈idealResidualPatterns probes₁ probes₂,(1+((Q:ℝ)^2/ξ)^2) :=
      sum_le_sum fun ν _ => idealResidualCoefficient_norm P Q h hξ ν (a ν) (b ν) (aux ν)
    _ = ((idealResidualPatterns probes₁ probes₂).card:ℝ)*(1+((Q:ℝ)^2/ξ)^2) := by
      rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast idealResidualPatterns_card_le probes₁ probes₂) (by positivity)

end
end ArtinMatthews
