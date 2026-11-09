module

public import ArtinMatthews.GiantTwoSidedResiduePatternSchur


set_option backward.privateInPublic true
@[expose] public section

/-! A finite nonnegative path sum with a free terminal state is bounded
by its initial mass and the product of its row bounds. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def finiteAbsolutePathMass {S : Type*} [Fintype S] (n : ℕ)
    (initial : S → ℝ) (K : Fin n → S → S → ℝ) : ℝ :=
  ∑ s : Fin (n+1) → S,initial (s 0)*∏ i : Fin n,K i (s i.castSucc) (s i.succ)

theorem finiteAbsolutePathMass_nonneg {S : Type*} [Fintype S] (n : ℕ)
    (initial : S → ℝ) (hi : ∀ s,0 ≤ initial s) (K : Fin n → S → S → ℝ)
    (hK : ∀ i s t,0 ≤ K i s t) : 0 ≤ finiteAbsolutePathMass n initial K :=
  sum_nonneg fun s _ => mul_nonneg (hi (s 0))
    (prod_nonneg fun i _ => hK i (s i.castSucc) (s i.succ))

theorem finiteAbsolutePathMass_zero {S : Type*} [Fintype S]
    (initial : S → ℝ) (K : Fin 0 → S → S → ℝ) :
    finiteAbsolutePathMass 0 initial K=∑ s,initial s := by
  unfold finiteAbsolutePathMass
  have he := (Fin.consEquiv (fun _ : Fin 1 => S)).sum_comp
    (fun s : Fin 1 → S => initial (s 0)*∏ i : Fin 0,K i (s i.castSucc) (s i.succ))
  rw [← he,Fintype.sum_prod_type]
  simp [Fin.consEquiv]

theorem finiteAbsolutePathMass_succ {S : Type*} [Fintype S]
    (n : ℕ) (initial : S → ℝ) (K : Fin (n+1) → S → S → ℝ) :
    finiteAbsolutePathMass (n+1) initial K=
      ∑ s : Fin (n+1) → S,
        (initial (s 0)*∏ i : Fin n,K i.castSucc (s i.castSucc) (s i.succ))*
          ∑ t : S,K (Fin.last n) (s (Fin.last n)) t := by
  unfold finiteAbsolutePathMass
  have he := (Fin.snocEquiv (fun _ : Fin (n+2) => S)).sum_comp
    (fun s : Fin (n+2) → S => initial (s 0)*∏ i : Fin (n+1),K i (s i.castSucc) (s i.succ))
  rw [← he,Fintype.sum_prod_type,sum_comm]
  apply sum_congr rfl
  intro s _
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  simp only [Fin.snocEquiv,Equiv.coe_fn_mk,Fin.prod_univ_castSucc,Fin.succ_castSucc,
    Fin.snoc_castSucc,Fin.succ_last,Fin.snoc_last,Fin.snoc_apply_zero]
  ring

theorem finiteAbsolutePathMass_le {S : Type*} [Fintype S]
    (initial : S → ℝ) (hi : ∀ s,0 ≤ initial s) {B : ℝ} (hB : 0 ≤ B)
    (n : ℕ) (K : Fin n → S → S → ℝ) (hK : ∀ i s t,0 ≤ K i s t)
    (hrow : ∀ i s,∑ t,K i s t ≤ B) :
    finiteAbsolutePathMass n initial K ≤ (∑ s,initial s)*B^n := by
  induction n with
  | zero => rw [finiteAbsolutePathMass_zero,pow_zero,mul_one]
  | succ n ih =>
    rw [finiteAbsolutePathMass_succ]
    calc
      _ ≤ ∑ s : Fin (n+1) → S,
          (initial (s 0)*∏ i : Fin n,K i.castSucc (s i.castSucc) (s i.succ))*B := by
        apply sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (hrow _ _) (mul_nonneg (hi _) (prod_nonneg fun i _ => hK _ _ _))
      _ = finiteAbsolutePathMass n initial (fun i => K i.castSucc)*B := by
        rw [← sum_mul]
        rfl
      _ ≤ ((∑ s,initial s)*B^n)*B :=
        mul_le_mul_of_nonneg_right (ih (fun i => K i.castSucc) (fun i => hK i.castSucc)
          (fun i => hrow i.castSucc)) hB
      _ = _ := by rw [pow_succ,mul_assoc]

theorem finiteAbsolutePathMass_le_of_initial_le_one {S : Type*} [Fintype S]
    (initial : S → ℝ) (hi : ∀ s,0 ≤ initial s) (hmass : (∑ s,initial s) ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (n : ℕ) (K : Fin n → S → S → ℝ)
    (hK : ∀ i s t,0 ≤ K i s t) (hrow : ∀ i s,∑ t,K i s t ≤ B) :
    finiteAbsolutePathMass n initial K ≤ B^n :=
  (finiteAbsolutePathMass_le initial hi hB n K hK hrow).trans
    (by simpa using mul_le_mul_of_nonneg_right hmass (pow_nonneg hB n))

end
end ArtinMatthews
