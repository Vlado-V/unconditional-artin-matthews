module

public import ArtinMatthews.GiantSignedCleanFourier
public import ArtinMatthews.GiantSignedMemoryState


set_option backward.privateInPublic true
@[expose] public section

/-! Literal product-density identities for the active and fresh laws. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset ℕ}

theorem giantSignedActiveMass_mul {M : ℕ} (μ r : ∀ j, P j → ℝ)
    (a : MarkedPhysicalMarking P M) :
    giantSignedActiveMass (fun j p => μ j p * r j p) a =
      giantSignedActiveMass μ a * giantSignedActiveMass r a := by
  unfold giantSignedActiveMass
  simp only [Finset.prod_mul_distrib]

theorem idealFreshTargetMass_mul {k ell : ℕ} (μ r : ∀ j, P j → ℝ)
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) :
    idealFreshTargetMass (fun j p => μ j p * r j p) C a =
      idealFreshTargetMass μ C a * idealFreshTargetMass r C a := by
  unfold idealFreshTargetMass
  simp only [Finset.prod_mul_distrib]

theorem giantSignedActiveMass_one_le {M : ℕ} (r : ∀ j, P j → ℝ)
    (hr : ∀ j p, 1 ≤ r j p) (a : MarkedPhysicalMarking P M) :
    1 ≤ giantSignedActiveMass r a := by
  unfold giantSignedActiveMass
  exact Finset.one_le_prod₀ (fun j _ => Finset.one_le_prod₀ (fun i _ => hr j (a j i)))

theorem idealFreshTargetMass_one_le {k ell : ℕ} (r : ∀ j, P j → ℝ)
    (hr : ∀ j p, 1 ≤ r j p) (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) :
    1 ≤ idealFreshTargetMass r C a := by
  unfold idealFreshTargetMass
  exact Finset.one_le_prod₀ (fun j _ => Finset.one_le_prod₀ (fun i _ => hr j (a j _)))

theorem giantSignedActiveMass_upper {M : ℕ} (r : ∀ j, P j → ℝ)
    (hr : ∀ j p, 0 ≤ r j p) (R : ℝ) (hR : ∀ j p, r j p ≤ R)
    (a : MarkedPhysicalMarking P M) :
    giantSignedActiveMass r a ≤ R ^ (Fintype.card J * M) := by
  unfold giantSignedActiveMass
  calc
    _ ≤ ∏ _j : J, R ^ M := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Finset.prod_nonneg fun i _ => hr j (a j i)
      · intro j _
        calc
          _ ≤ ∏ _i : Fin M, R := Finset.prod_le_prod₀ (fun i _ => hr j (a j i))
            (fun i _ => hR j (a j i))
          _ = _ := by simp
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

theorem idealFreshTargetMass_upper {k ell : ℕ} (r : ∀ j, P j → ℝ)
    (hr : ∀ j p, 0 ≤ r j p) (R : ℝ) (hR : ∀ j p, r j p ≤ R)
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) :
    idealFreshTargetMass r C a ≤ ∏ j, R ^ ((C j).card + ell) := by
  unfold idealFreshTargetMass
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.prod_nonneg fun i _ => hr j (a j _)
  · intro j _
    calc
      _ ≤ ∏ _i : GiantTwoSidedPatternFreeSlots (C j) ell, R :=
        Finset.prod_le_prod₀ (fun i _ => hr j (a j _)) (fun i _ => hR j (a j _))
      _ = _ := by simp [GiantTwoSidedPatternFreeSlots]

theorem giantSignedTilt_activeEnergy_le [DecidableEq J] {M : ℕ} (μ r : ∀ j, P j → ℝ)
    (hμ : ∀ j p, 0 ≤ μ j p) (hr : ∀ j p, 0 ≤ r j p)
    (R : ℝ) (hR : ∀ j p, r j p ≤ R) (f : MarkedPhysicalMarking P M → ℂ) :
    (∑ a, giantSignedActiveMass (fun j p => μ j p * r j p) a * ‖f a‖ ^ 2) ≤
      R ^ (Fintype.card J * M) * ∑ a, giantSignedActiveMass μ a * ‖f a‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [giantSignedActiveMass_mul]
  have hm : 0 ≤ giantSignedActiveMass μ a :=
    Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun i _ => hμ j (a j i)
  have h := mul_le_mul_of_nonneg_left (giantSignedActiveMass_upper r hr R hR a)
    (mul_nonneg hm (sq_nonneg ‖f a‖))
  nlinarith

end
end ArtinMatthews
