module

public import ArtinMatthews.GiantMixedSlotCofactor


set_option backward.privateInPublic true
@[expose] public section

/-! Exact character factorization and the bilinear reindex of one
selected slot. The original hyperbola condition remains in the sum. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giant_mixed_slot_product_eq {k q : ℕ} (χ : DirichletCharacter ℂ q)
    (W z : ℝ) (i : Fin (k+1)) (t : Fin (k+1) → ℕ) :
    (∏ j : Fin (k+1) with j < i, χ (t j)*giantRoughSlotCoefficient W z (t j)) *
      (∏ j : Fin (k+1) with i < j, χ (t j)*giantPrimeSlotCoefficient z (t j)) =
      χ ((∏ j,i.removeNth t j) : ℕ) * ∏ j,giantMixedSlotWeight i W z j (i.removeNth t j) := by
  let f (j : Fin (k+1)) : ℂ := if j = i then 1 else χ (t j) *
    (if j < i then giantRoughSlotCoefficient W z (t j) else giantPrimeSlotCoefficient z (t j))
  calc
    _ = ∏ j,f j := by
      rw [prod_filter,prod_filter,← prod_mul_distrib]
      apply prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [f]
      · by_cases hji : j < i
        · have hij : ¬i < j := not_lt_of_ge hji.le
          simp [f,hj,hji,hij]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          simp [f,hj,hji,hij]
    _ = _ := by
      rw [Fin.prod_univ_succAbove f i]
      simp only [f,ite_true,one_mul,Fin.succAbove_ne,ite_false,Fin.removeNth_apply,
        giantMixedSlotWeight,prod_mul_distrib,Nat.cast_prod,map_prod]

theorem giant_slot_discrepancy_eq_bilinear {k q : ℕ} (χ : DirichletCharacter ℂ q)
    (X : ℕ) (W z : ℝ) (i : Fin (k+1)) (w : ℕ → ℂ) :
    (∑ t ∈ giantOrderedProductTuples (k+1) X,w (∏ j,t j) *
      (if z < (t i:ℝ) then giantFixedCharacterReplacementCoefficient χ W 0 (t i) else 0) *
      (∏ j : Fin (k+1) with j < i, χ (t j)*giantRoughSlotCoefficient W z (t j)) *
      ∏ j : Fin (k+1) with i < j, χ (t j)*giantPrimeSlotCoefficient z (t j)) =
    ∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),
      w (mn.1*mn.2) * χ (mn.1*mn.2) *
        (if z < (mn.1:ℝ) then markedMajorCenteredCoefficient W 0 mn.1 else 0) *
        giantMixedCofactorCoefficient i W z mn.2 := by
  let F (m : ℕ) (u : Fin k → ℕ) :=
    w (m*(∏ j,u j)) * (if z < (m:ℝ) then giantFixedCharacterReplacementCoefficient χ W 0 m else 0) *
      (χ ((∏ j,u j) : ℕ)*∏ j,giantMixedSlotWeight i W z j (u j))
  calc
    _ = ∑ t ∈ giantOrderedProductTuples (k+1) X,F (t i) (i.removeNth t) := by
      apply sum_congr rfl
      intro t _
      rw [mul_assoc (w (∏ j,t j) * _),giant_mixed_slot_product_eq χ W z i t]
      rw [← Fin.mul_prod_removeNth i t]
    _ = ∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),
        ∑ u ∈ giantOrderedProductFiber k mn.2,F mn.1 u :=
      giant_ordered_product_tuple_sum_split k X i F
    _ = _ := by
      apply sum_congr rfl
      intro mn _
      rw [giantMixedCofactorCoefficient,mul_sum]
      apply sum_congr rfl
      intro u hu
      have hprod := (mem_giantOrderedProductFiber.mp hu).2
      dsimp only [F]
      rw [hprod]
      by_cases hm : z < (mn.1:ℝ)
      · simp only [hm,ite_true,giantFixedCharacterReplacementCoefficient,map_mul]
        ring
      · simp only [hm,ite_false,mul_zero,zero_mul]

end
end ArtinMatthews
