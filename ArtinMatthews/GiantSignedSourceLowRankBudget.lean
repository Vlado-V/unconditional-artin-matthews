module

public import ArtinMatthews.GiantSignedSourceRankCutoff
public import ArtinMatthews.GiantSignedSourceBirthAddressBudget
public import ArtinMatthews.MarkedBirthRankSums
public import Mathlib.Data.Fintype.Perm


set_option backward.privateInPublic true
@[expose] public section

/-! Sum the actual source frame's low ranks while retaining the signed
edge saving on every operation outside the affected set. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

local instance sourceBirthPermutationFintype {B : Type*} [Fintype B] {M n H : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M n H)
    (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance inferInstance inferInstance

theorem giantSignedSourceBirth_low_rank_sum_eventually
    (C₀ Cv G Ca E c scale : ℝ) (M : ℕ)
    (hC₀ : 0 ≤ C₀) (hCv : 0 ≤ Cv) (hCa : 0 ≤ Ca) (hE : 0 ≤ E)
    (hG : E+Cv+3 < G) (hc : 0 < c) (hscale : 0 ≤ scale) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (B : Type*) [Fintype B],
        let L := Real.log x
        let n := giantTwoSidedSourceMomentLength x
        let R := giantSignedSourceMemoryLimit L
        let r₀ := giantSignedSourceRankCutoff c scale x
        let A := GiantSignedUniformBirthAddress B M n R
        (Fintype.card B : ℝ) ≤ C₀ * Real.log L →
        ∀ F : Equiv.Perm A → ℂ,
          (∀ σ, markedBirthPermutationRank σ < r₀ →
            let r := markedBirthPermutationRank σ
            ‖F σ‖ ≤ 2 * (L^(Cv/2))^(n+1) * (L^(-G))^(n-2*r) * (L^Ca)^(2*r)) →
          (∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R),
            if markedBirthPermutationRank σ < r₀ then ‖F σ‖ else 0) ≤
            (L^(-E))^n := by
  let K := 2 + 30 + 2*(G+Ca)
  have hG0 : 0 ≤ G := by linarith
  have hK2 : 2 ≤ K := by dsimp only [K]; linarith
  have hK : 0 < K := by linarith
  filter_upwards [
    giantSignedSourceRankCutoff_le_fraction hc hscale (one_div_pos.mpr hK),
    giantSignedSourceBirthAddress_budget_eventually C₀ hC₀ M,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (5 : ℝ)),
    giantSignedSourceMomentLength_tendsto.eventually (eventually_ge_atTop (Cv/2+3))]
      with x hcut haddress hlog hnLarge
  intro B _
  dsimp only
  intro hB F hF
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let R := giantSignedSourceMemoryLimit L
  let r₀ := giantSignedSourceRankCutoff c scale x
  let A := GiantSignedUniformBirthAddress B M n R
  let T (r : ℕ) := 2 * (L^(Cv/2))^(n+1) * (L^(-G))^(n-2*r) * (L^Ca)^(2*r)
  have hL5 : 5 ≤ L := hlog
  have hL2 : 2 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hn : (n : ℝ) ≤ L^2 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hL1 (show (13/25 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at hp
    have hlen := giantTwoSidedSourceMomentLength_le (x := x) hL1
    change (n : ℝ) ≤ 4 * L^(13/25 : ℝ) at hlen
    nlinarith [mul_le_mul_of_nonneg_right hL5 hL.le]
  have hr₀K : (r₀ : ℝ)*K ≤ (n : ℝ) :=
    (le_div_iff₀ hK).mp (hcut.trans_eq (by ring))
  have hr₀ : (r₀ : ℝ) ≤ (n : ℝ) :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith : 1 ≤ K)).trans hr₀K
  have hA : ((Fintype.card A : ℝ)^2+1)^2 ≤ L^(30 : ℕ) := haddress B hB
  have hT (r : ℕ) : 0 ≤ T r := by dsimp only [T]; positivity
  have hsum := markedBirthRank_low_sum_le (A := A) r₀ (fun σ => ‖F σ‖) T
    (fun r _ => hT r) hF
  refine hsum.trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range r₀, L^(-E*(n : ℝ)-2) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrR : (r : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast (Finset.mem_range.mp hr).le
      have hrK : (r : ℝ)*K ≤ (n : ℝ) := (mul_le_mul_of_nonneg_right hrR hK.le).trans hr₀K
      have hrn : 2*r ≤ n := by
        have h := (mul_le_mul_of_nonneg_left hK2 (Nat.cast_nonneg r : (0 : ℝ) ≤ r)).trans hrK
        rw [mul_comm (r : ℝ)] at h
        exact_mod_cast h
      let a := 30*(r : ℝ) + Cv/2*((n+1 : ℕ) : ℝ) +
        (-G)*((n-2*r : ℕ) : ℝ) + Ca*((2*r : ℕ) : ℝ)
      have hpow : ((Fintype.card A : ℝ)^2+1)^(2*r) ≤ (L^(30 : ℕ))^r := by
        rw [pow_mul]
        exact pow_le_pow_left₀ (sq_nonneg _) hA _
      have ha : a+1 ≤ -E*(n : ℝ)-2 := by
        dsimp only [a]
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hrn, Nat.cast_mul, Nat.cast_ofNat]
        dsimp only [K] at hrK
        have hh := mul_le_mul_of_nonneg_right
          (show E+Cv/2+2 ≤ G by linarith) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        change Cv/2+3 ≤ (n : ℝ) at hnLarge
        nlinarith only [hrK, hnLarge, hh, (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
      calc
        _ ≤ (L^(30 : ℕ))^r * T r := mul_le_mul_of_nonneg_right hpow (hT r)
        _ = 2*L^a := by
          dsimp only [T, a]
          rw [← Real.rpow_natCast L 30]
          simp only [← Real.rpow_mul_natCast hL.le, Nat.cast_ofNat]
          have hmul :
              L^(30*(r : ℝ)) * (2 * L^(Cv/2*((n+1 : ℕ) : ℝ)) *
                L^((-G)*((n-2*r : ℕ) : ℝ)) * L^(Ca*((2*r : ℕ) : ℝ))) =
              2 * (L^(30*(r : ℝ)) * L^(Cv/2*((n+1 : ℕ) : ℝ)) *
                L^((-G)*((n-2*r : ℕ) : ℝ)) * L^(Ca*((2*r : ℕ) : ℝ))) := by ring
          rw [hmul]
          rw [← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
        _ ≤ L^(a+1) := by
          rw [Real.rpow_add hL a 1, Real.rpow_one, mul_comm (L^a)]
          exact mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hL.le _)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 ha
    _ = (r₀ : ℝ) * L^(-E*(n : ℝ)-2) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ L^2 * L^(-E*(n : ℝ)-2) :=
      mul_le_mul_of_nonneg_right (hr₀.trans hn) (Real.rpow_nonneg hL.le _)
    _ = _ := by
      rw [← Real.rpow_two, ← Real.rpow_add hL, ← Real.rpow_mul_natCast hL.le]
      congr 1
      ring

end
end ArtinMatthews
