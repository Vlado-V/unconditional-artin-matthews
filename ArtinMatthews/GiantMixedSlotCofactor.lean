module

public import ArtinMatthews.GiantOrderedProductTuples
public import ArtinMatthews.GiantPrimeSlotTelescoping


set_option backward.privateInPublic true
@[expose] public section

/-! The cofactor coefficient in one actual prime-slot discrepancy.
The slots before the selected one carry the rough proxy, and the slots
after it still carry the prime indicator. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantMixedSlotWeight {k : ℕ} (i : Fin (k+1)) (W z : ℝ) (j : Fin k) (m : ℕ) : ℂ :=
  if i.succAbove j < i then giantRoughSlotCoefficient W z m else giantPrimeSlotCoefficient z m

def giantMixedCofactorCoefficient {k : ℕ} (i : Fin (k+1)) (W z : ℝ) (n : ℕ) : ℂ :=
  ∑ u ∈ giantOrderedProductFiber k n, ∏ j,giantMixedSlotWeight i W z j (u j)

theorem giantMixedSlotWeight_support {k : ℕ} (i : Fin (k+1)) {W z : ℝ} (hWz : W ≤ z)
    (j : Fin k) {m : ℕ} (hm : giantMixedSlotWeight i W z j m ≠ 0) :
    z < (m:ℝ) ∧ MarkedRoughAbove W m := by
  classical
  by_cases h : i.succAbove j < i
  · rw [giantMixedSlotWeight,ite_eq_left h,giantRoughSlotCoefficient] at hm
    have hz : z < (m:ℝ) := by
      by_contra hz
      exact hm (ite_eq_right hz)
    have hrough : ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m := by
      by_contra hr
      simp only [hz,hr,ite_true,ite_false,mul_zero] at hm
      exact hm rfl
    refine ⟨hz,fun p hp hd => ?_⟩
    by_contra! hpW
    exact hrough p (Nat.mem_primesLE.mpr ⟨Nat.le_floor hpW,hp⟩) hd
  · rw [giantMixedSlotWeight,ite_eq_right h,giantPrimeSlotCoefficient] at hm
    have hz : z < (m:ℝ) := by
      by_contra hz
      exact hm (ite_eq_right hz)
    have hp : m.Prime := by
      by_contra hp
      simp only [hz,hp,ite_true,ite_false] at hm
      exact hm rfl
    refine ⟨hz,fun p hp' hd => ?_⟩
    have he : p=m := (Nat.dvd_prime hp).mp hd |>.resolve_left hp'.ne_one
    exact he ▸ hWz.trans_lt hz

theorem giantMixedCofactorCoefficient_support {k : ℕ} (hk : 0 < k) (i : Fin (k+1))
    {W z : ℝ} (hWz : W ≤ z) {n : ℕ} (hn : giantMixedCofactorCoefficient i W z n ≠ 0) :
    z < (n:ℝ) ∧ MarkedRoughAbove W n := by
  obtain ⟨u,hu,hweight⟩ := exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨hu₀,hprod⟩ := mem_giantOrderedProductFiber.mp hu
  have hs (j : Fin k) : z < (u j:ℝ) ∧ MarkedRoughAbove W (u j) :=
    giantMixedSlotWeight_support i hWz j ((prod_ne_zero_iff.mp hweight) j (mem_univ j))
  let j₀ : Fin k := ⟨0,hk⟩
  have hn₀ : 0 < n := hprod ▸ prod_pos (fun j _ => hu₀ j)
  have hd₀ : u j₀ ∣ n := hprod ▸ dvd_prod_of_mem u (mem_univ j₀)
  refine ⟨(hs j₀).1.trans_le (Nat.cast_le.mpr (Nat.le_of_dvd hn₀ hd₀)),fun p hp hd => ?_⟩
  obtain ⟨j,_,hpd⟩ := (hp.prime.dvd_finsetProd_iff u).mp (hprod.symm ▸ hd)
  exact (hs j).2 p hp hpd

theorem giantMixedCofactorCoefficient_norm_le {k : ℕ} (i : Fin (k+1)) (W z : ℝ) (n : ℕ)
    (C : ℝ) (hprime : ∀ m, ‖giantPrimeSlotCoefficient z m‖ ≤ C)
    (hrough : ∀ m, ‖giantRoughSlotCoefficient W z m‖ ≤ C) :
    ‖giantMixedCofactorCoefficient i W z n‖ ≤ ((giantOrderedProductFiber k n).card:ℝ)*C^k := by
  unfold giantMixedCofactorCoefficient
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _u ∈ giantOrderedProductFiber k n, C^k := by
      apply sum_le_sum
      intro u _
      rw [norm_prod]
      calc
        _ ≤ ∏ _j : Fin k, C := by
          apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro j _
          by_cases h : i.succAbove j < i
          · rw [giantMixedSlotWeight,ite_eq_left h]
            exact hrough _
          · rw [giantMixedSlotWeight,ite_eq_right h]
            exact hprime _
        _ = _ := by simp only [prod_const,card_univ,Fintype.card_fin]
    _ = _ := by simp only [sum_const,nsmul_eq_mul]

end
end ArtinMatthews
