module

public import ArtinMatthews.GiantTwoSidedEndpointMoment


set_option backward.privateInPublic true
@[expose] public section

/-! Summing the original list measures costs at most one. Both endpoint
norm exponents are consequently independent of the number of groups and
the full ordered list length. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedEndpointEnergy_le_of_per_list {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset ℕ) (q : ℝ) (F : ℕ → ℂ)
    (hV : ∀ j,0 < bandReciprocalMass (P j)) {B : ℝ} (hB : 0 ≤ B)
    (hlist : ∀ a : MarkedPhysicalMarking P M,MarkedPhysicalMarkingDistinct a →
      (∑ n : GiantTwoSidedEndpointPositions Z a,
        ‖(giantTwoSidedEndpointDamping P M q n.1.val:ℂ)*F n.1.val‖^2) ≤
          B*markedPhysicalReciprocalProduct a) :
    giantTwoSidedEndpointEnergy P M Z q F ≤ B := by
  classical
  let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) M
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ M (fun j => (hV j).le)
  rw [giantTwoSidedEndpointEnergy_eq_positions]
  calc
    _ ≤ ∑ a : MarkedPhysicalMarking P M,
      B*(if MarkedPhysicalMarkingDistinct a then σ*markedPhysicalReciprocalProduct a else 0) := by
        apply sum_le_sum
        intro a _
        by_cases ha : MarkedPhysicalMarkingDistinct a
        · rw [ite_eq_left ha]
          exact (mul_le_mul_of_nonneg_left (hlist a ha) hσ).trans_eq (by ring)
        · have : IsEmpty (GiantTwoSidedEndpointPositions Z a) := ⟨fun n => ha n.2.1⟩
          simp [ha]
    _ = B*(∑ a : MarkedPhysicalMarking P M,
      if MarkedPhysicalMarkingDistinct a then σ*markedPhysicalReciprocalProduct a else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ B*1 := mul_le_mul_of_nonneg_left (markedPhysicalMarking_distinct_normalized_sum_le_one P M hV) hB
    _ = B := mul_one _

theorem giantTwoSidedEndpointNorm_le_uniform {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hV : ∀ j,0 < bandReciprocalMass (P j))
    (M : ℕ) {N : ℕ} {Z : Finset ℕ} (hZ : Z ⊆ Ioc 0 N) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1)
    (F : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) (hF : ∀ n ∈ Z,‖F n‖ ≤ C) :
    giantTwoSidedEndpointNorm P M Z q F ≤ C*Real.sqrt (N:ℝ) := by
  have he : giantTwoSidedEndpointEnergy P M Z q F ≤ C^2*(N:ℝ) :=
    giantTwoSidedEndpointEnergy_le_of_per_list P M Z q F hV (by positivity)
      (fun a _ => giantTwoSidedEndpointPositions_energy_le_uniform hP hdis hZ hq a F hF)
  unfold giantTwoSidedEndpointNorm
  exact (Real.sqrt_le_sqrt he).trans_eq (by rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hC])

theorem giantTwoSidedEndpointNorm_le_fiber {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hV : ∀ j,0 < bandReciprocalMass (P j))
    (M : ℕ) {N : ℕ} {Z : Finset ℕ} (hZ : Z ⊆ Ioc 0 N) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1)
    (F : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) (r : ℕ) (hr : 0 < r)
    (hF : ∀ n ∈ Z,‖F n‖ ≤ C*((giantOrderedProductFiber r (giantCandidateStrip (univ.biUnion P) n)).card:ℝ)) :
    giantTwoSidedEndpointNorm P M Z q F ≤
      C*Real.sqrt (N:ℝ)*Real.sqrt ((1+Real.log ((N:ℝ)+1))^(r*r)) := by
  have hbase : 0 ≤ 1+Real.log ((N:ℝ)+1) :=
    add_nonneg zero_le_one (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg N)))
  have he : giantTwoSidedEndpointEnergy P M Z q F ≤ C^2*(N:ℝ)*(1+Real.log ((N:ℝ)+1))^(r*r) :=
    giantTwoSidedEndpointEnergy_le_of_per_list P M Z q F hV
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hbase _))
      (fun a _ => giantTwoSidedEndpointPositions_energy_le_fiber hP hdis hZ hq a F hC r hr hF)
  unfold giantTwoSidedEndpointNorm
  exact (Real.sqrt_le_sqrt he).trans_eq (by
    rw [Real.sqrt_mul (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)),
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hC])

end
end ArtinMatthews
