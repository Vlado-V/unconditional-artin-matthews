module

public import ArtinMatthews.GiantTwoSidedRawSymmetrization
public import ArtinMatthews.GiantTwoSidedPatternKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Average both ends of the actual finite physical matrix independently.
Uniform row and column bounds pass through the normalized slot laws. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedSlotAverage {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} {Z Z' : Finset ℕ}
    (K : GiantTwoSidedEndpointState P M Z → GiantTwoSidedEndpointState P M Z' → ℝ)
    (s : GiantTwoSidedEndpointState P M Z) (t : GiantTwoSidedEndpointState P M Z') : ℝ :=
  let Permutations := J → Equiv.Perm (Fin M)
  (∑ π : Permutations,∑ τ : Permutations,K (giantTwoSidedEndpointPermute π s)
    (giantTwoSidedEndpointPermute τ t))/(Fintype.card Permutations:ℝ)^2

theorem giantTwoSidedSlotAverage_row_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} {Z Z' : Finset ℕ}
    (K : GiantTwoSidedEndpointState P M Z → GiantTwoSidedEndpointState P M Z' → ℝ)
    {B : ℝ} (hK : ∀ s,∑ t,K s t ≤ B) (s : GiantTwoSidedEndpointState P M Z) :
    (∑ t,giantTwoSidedSlotAverage K s t) ≤ B := by
  let Permutations := J → Equiv.Perm (Fin M)
  let f (π τ : Permutations) (t : GiantTwoSidedEndpointState P M Z') :=
    K (giantTwoSidedEndpointPermute π s) (giantTwoSidedEndpointPermute τ t)
  have hp : 0 < Fintype.card Permutations := Fintype.card_pos_iff.mpr ⟨fun _ => Equiv.refl _⟩
  have hC : 0 < ((Fintype.card Permutations:ℝ)^2) := pow_pos (Nat.cast_pos.mpr hp) _
  have hs : (∑ t,∑ π : Permutations,∑ τ : Permutations,f π τ t) = ∑ π,∑ τ,∑ t,f π τ t := by
    rw [sum_comm]
    exact sum_congr rfl fun π _ => sum_comm
  change (∑ t, (∑ π : Permutations,∑ τ : Permutations,f π τ t)/(Fintype.card Permutations:ℝ)^2) ≤ B
  rw [← sum_div,hs]
  apply (div_le_iff₀ hC).mpr
  calc
    _ ≤ ∑ _π : Permutations,∑ _τ : Permutations,B := by
      apply sum_le_sum
      intro π _
      apply sum_le_sum
      intro τ _
      have h := (giantTwoSidedEndpointPermute (P:=P) (Z:=Z') τ).sum_comp
        (K (giantTwoSidedEndpointPermute π s))
      exact h.trans_le (hK _)
    _ = _ := by simp only [sum_const,nsmul_eq_mul,card_univ]; ring

theorem giantTwoSidedSlotAverage_column_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} {Z Z' : Finset ℕ}
    (K : GiantTwoSidedEndpointState P M Z → GiantTwoSidedEndpointState P M Z' → ℝ)
    {B : ℝ} (hK : ∀ t,∑ s,K s t ≤ B) (t : GiantTwoSidedEndpointState P M Z') :
    (∑ s,giantTwoSidedSlotAverage K s t) ≤ B := by
  have hs (s : GiantTwoSidedEndpointState P M Z) :
      giantTwoSidedSlotAverage K s t=giantTwoSidedSlotAverage (fun v u => K u v) t s := by
    unfold giantTwoSidedSlotAverage
    dsimp only
    rw [sum_comm]
  simp_rw [hs]
  exact giantTwoSidedSlotAverage_row_le (fun v u => K u v) hK t

def giantTwoSidedPatternAbsoluteEntry {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k+ell) Z) (t : GiantTwoSidedEndpointState P (k+ell) Z') : ℝ :=
  ∑ a : GiantTwoSidedPatternAuxiliary P C,‖giantTwoSidedPatternPhysicalCoefficient step q ζ K s t a‖

end
end ArtinMatthews
