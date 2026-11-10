module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import ArtinMatthews.GiantSignedPromotionDamping
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded


set_option backward.privateInPublic true
@[expose] public section

/-! The finite source-store and target-promotion slot sums depend only on
the number of free slots, independently of the copied slots and memory. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedEdgeUniformConstant (ρ v rateMax massMax : ℝ) (tmax : ℕ) : ℝ :=
  (2 : ℝ) ^ tmax * (2 : ℝ) ^ tmax *
    (v ^ tmax * (max 1 rateMax) ^ tmax * (max 1 massMax) ^ tmax *
      ((tmax.factorial : ℝ) / (1 - ρ) ^ (tmax + 1)))

theorem giantSignedFreeSubsetFamily_card_le {J : Type*} [Fintype J] [DecidableEq J]
    (t : J → ℕ) (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) :
    (Fintype.card ((j : J) → Finset (Fin (t j))) : ℝ) ≤
      ((2 : ℝ) ^ tmax) ^ Fintype.card J := by
  classical
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _j : J, (2 : ℝ) ^ tmax := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Nat.cast_nonneg _
      · intro j _
        simp only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
        exact pow_le_pow_right₀ (by norm_num) (ht j)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

theorem giantSignedEdgeUniformConstant_nonneg {ρ v rateMax massMax : ℝ} {tmax : ℕ}
    (hρ1 : ρ < 1) (hv : 0 ≤ v) :
    0 ≤ giantSignedEdgeUniformConstant ρ v rateMax massMax tmax := by
  unfold giantSignedEdgeUniformConstant
  positivity

theorem giantSignedEdgeSlotBudget {J : Type*} [Fintype J] [DecidableEq J]
    (t : J → ℕ) (tmax : ℕ) (ht : ∀ j, t j ≤ tmax)
    (rate mass : J → ℝ) (rateMax massMax ρ v : ℝ)
    (hRate : ∀ j, 0 ≤ rate j) (hMass : ∀ j, 0 ≤ mass j)
    (hRateMax : ∀ j, rate j ≤ rateMax) (hMassMax : ∀ j, mass j ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) :
    (∑ S : (j : J) → Finset (Fin (t j)),
      ∑ T : (j : J) → Finset (Fin (t j)),
        ∏ j, v ^ (S j).card * rate j ^ (T j).card * mass j ^ ((T j)ᶜ).card *
          (((T j).card.factorial : ℝ) / (1 - ρ) ^ ((T j).card + 1))) ≤
      (giantSignedEdgeUniformConstant ρ v rateMax massMax tmax) ^ Fintype.card J := by
  classical
  let A := v ^ tmax * (max 1 rateMax) ^ tmax * (max 1 massMax) ^ tmax *
    ((tmax.factorial : ℝ) / (1 - ρ) ^ (tmax + 1))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hterm (S T : (j : J) → Finset (Fin (t j))) :
      (∏ j, v ^ (S j).card * rate j ^ (T j).card * mass j ^ ((T j)ᶜ).card *
        (((T j).card.factorial : ℝ) / (1 - ρ) ^ ((T j).card + 1))) ≤
          A ^ Fintype.card J := by
    calc
      _ ≤ ∏ _j : J, A := by
        apply Finset.prod_le_prod₀
        · intro j _
          exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (le_trans zero_le_one hv) _)
            (pow_nonneg (hRate j) _)) (pow_nonneg (hMass j) _))
            (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_pos.mpr hρ1).le _))
        · intro j _
          have hS : (S j).card ≤ tmax := (show (S j).card ≤ t j by
            simpa only [Finset.card_univ, Fintype.card_fin] using
              Finset.card_le_card (Finset.subset_univ (S j))).trans (ht j)
          have hT : (T j).card ≤ tmax := (show (T j).card ≤ t j by
            simpa only [Finset.card_univ, Fintype.card_fin] using
              Finset.card_le_card (Finset.subset_univ (T j))).trans (ht j)
          have hC : ((T j)ᶜ).card ≤ tmax := (show ((T j)ᶜ).card ≤ t j by
            simpa only [Finset.card_univ, Fintype.card_fin] using
              Finset.card_le_card (Finset.subset_univ ((T j)ᶜ))).trans (ht j)
          have hV := pow_le_pow_right₀ hv hS
          have hR : rate j ^ (T j).card ≤ (max 1 rateMax) ^ tmax :=
            (pow_le_pow_left₀ (hRate j) ((hRateMax j).trans (le_max_right _ _)) _).trans
              (pow_le_pow_right₀ (le_max_left _ _) hT)
          have hM : mass j ^ ((T j)ᶜ).card ≤ (max 1 massMax) ^ tmax :=
            (pow_le_pow_left₀ (hMass j) ((hMassMax j).trans (le_max_right _ _)) _).trans
              (pow_le_pow_right₀ (le_max_left _ _) hC)
          have hF := giantSignedPromotionFactor_mono (T j).card tmax hT hρ hρ1
          dsimp [A]
          exact mul_le_mul (mul_le_mul (mul_le_mul hV hR
            (pow_nonneg (hRate j) _) (pow_nonneg (le_trans zero_le_one hv) _)) hM
            (pow_nonneg (hMass j) _) (by positivity)) hF
            (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_pos.mpr hρ1).le _))
            (by positivity)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
  have hc := giantSignedFreeSubsetFamily_card_le t tmax ht
  calc
    _ ≤ ∑ _S : (j : J) → Finset (Fin (t j)),
        ∑ _T : (j : J) → Finset (Fin (t j)), A ^ Fintype.card J :=
      Finset.sum_le_sum (fun S _ => Finset.sum_le_sum (fun T _ => hterm S T))
    _ = (Fintype.card ((j : J) → Finset (Fin (t j))) : ℝ) *
        (Fintype.card ((j : J) → Finset (Fin (t j))) : ℝ) * A ^ Fintype.card J := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ (((2 : ℝ) ^ tmax) ^ Fintype.card J) *
        (((2 : ℝ) ^ tmax) ^ Fintype.card J) * A ^ Fintype.card J := by
      gcongr
    _ = _ := by simp only [giantSignedEdgeUniformConstant, A, mul_pow]

end
end ArtinMatthews
