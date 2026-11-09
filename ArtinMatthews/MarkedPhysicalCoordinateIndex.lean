module

public import ArtinMatthews.MarkedPhysicalMomentTube
public import ArtinMatthews.MarkedPhysicalPathArrays
public import ArtinMatthews.MarkedPhysicalResidueBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite coordinate, ordered-label and two-permutation
copy carrier used in the relative physical path sum. Cardinal bounds
come from its actual factors, including both copied-slot decorations. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]

abbrev MarkedPhysicalCoordinateIndex (P : J → Finset ℕ) (M n R : ℕ) :=
  MarkedPhysicalLabelPath P M n ×
    ((Fin n → ↥(markedPrimitiveCoordinateTube R)) ×
      (Fin n → (J → Equiv.Perm (Fin M)) × (J → Equiv.Perm (Fin M))))

theorem markedPhysicalCoordinateIndex_card (P : J → Finset ℕ) (M n R : ℕ) :
    Fintype.card (MarkedPhysicalCoordinateIndex P M n R)=
      Fintype.card (MarkedPhysicalMarking P M)^(n+1) *
        ((markedPrimitiveCoordinateTube R).card^n *
          ((M.factorial^(Fintype.card J))*(M.factorial^(Fintype.card J)))^n) := by
  simp only [MarkedPhysicalCoordinateIndex,MarkedPhysicalLabelPath,Fintype.card_prod,
    Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Fintype.card_perm]

theorem markedPhysicalCoordinateIndex_card_le (P : J → Finset ℕ) (M n R : ℕ) :
    Fintype.card (MarkedPhysicalCoordinateIndex P M n R)≤
      Fintype.card (MarkedPhysicalMarking P M)^(n+1) *
        ((2*R+1)^(2*n) * ((M.factorial^(Fintype.card J))*(M.factorial^(Fintype.card J)))^n) := by
  rw [markedPhysicalCoordinateIndex_card]
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_right
  calc
    _ ≤ ((2*R+1)^2)^n := Nat.pow_le_pow_left (markedPrimitiveCoordinateTube_card_le R) n
    _ = _ := (pow_mul _ _ _).symm

theorem markedPhysical_factorial_le_exp_sq (M : ℕ) :
    (M.factorial:ℝ)≤Real.exp ((M:ℝ)^2) := by
  have hf : (M.factorial:ℝ)≤(M:ℝ)^M := by exact_mod_cast Nat.factorial_le_pow M
  have hm : (M:ℝ)≤Real.exp (M:ℝ) := by linarith [Real.add_one_le_exp (M:ℝ)]
  calc
    _ ≤ (M:ℝ)^M := hf
    _ ≤ (Real.exp (M:ℝ))^M := pow_le_pow_left₀ (Nat.cast_nonneg _) hm M
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem markedPhysicalCoordinateIndex_card_exp_bound
    (e : J → ℝ) {β x : ℝ} (hlog : 1≤Real.log x) (he : ∀ j,e j≤β) (M n R : ℕ) :
    (Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) M n R):ℝ)≤
      Real.exp (2*(Fintype.card J:ℝ)*M*(n+1)*(Real.log x)^β) *
        (2*(R:ℝ)+1)^(2*n) * Real.exp (2*(Fintype.card J:ℝ)*(M:ℝ)^2*n) := by
  have hc : (Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) M n R):ℝ)≤
      (Fintype.card (MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M):ℝ)^(n+1) *
        ((2*(R:ℝ)+1)^(2*n) * (((M.factorial:ℝ)^(Fintype.card J))*((M.factorial:ℝ)^(Fintype.card J)))^n) := by
    exact_mod_cast markedPhysicalCoordinateIndex_card_le (fun j => markedLogPowerBand (e j) x) M n R
  have hlabels := pow_le_pow_left₀ (Nat.cast_nonneg _)
    (markedPhysicalMarking_card_bound e hlog he M) (n+1)
  have hfac := pow_le_pow_left₀ (Nat.cast_nonneg M.factorial) (markedPhysical_factorial_le_exp_sq M) (Fintype.card J)
  have hcopies : ((((M.factorial:ℝ)^(Fintype.card J))*((M.factorial:ℝ)^(Fintype.card J)))^n)≤
      Real.exp (2*(Fintype.card J:ℝ)*(M:ℝ)^2*n) := by
    calc
      _ ≤ (((Real.exp ((M:ℝ)^2))^(Fintype.card J))*((Real.exp ((M:ℝ)^2))^(Fintype.card J)))^n :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul hfac hfac (by positivity) (by positivity)) n
      _ = _ := by rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_nat_mul]; congr 1; ring
  apply hc.trans
  have hlabels' : (Fintype.card (MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M):ℝ)^(n+1)≤
      Real.exp (2*(Fintype.card J:ℝ)*M*(n+1)*(Real.log x)^β) := by
    apply hlabels.trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    _ ≤ Real.exp (2*(Fintype.card J:ℝ)*M*(n+1)*(Real.log x)^β) *
        ((2*(R:ℝ)+1)^(2*n) * Real.exp (2*(Fintype.card J:ℝ)*(M:ℝ)^2*n)) :=
      mul_le_mul hlabels' (mul_le_mul_of_nonneg_left hcopies (by positivity)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by ring

end
end ArtinMatthews
