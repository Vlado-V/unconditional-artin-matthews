module

public import ArtinMatthews.PrimeExtractionDyadicPartition


set_option backward.privateInPublic true
@[expose] public section

/-! A one-coordinate strip at the actual threshold meets only a
sublinear number of dyadic indices in the logarithmic scale. -/

namespace ArtinMatthews
noncomputable section
open Finset

def giantCandidateThresholdDyadIndices (A R : ℝ) : Finset ℕ :=
  Icc ⌊A/Real.log 2⌋₊ ⌊(A+R)/Real.log 2⌋₊

theorem giantCandidateThresholdDyad_mem {A R : ℝ} (hA : 0 ≤ A)
    {N k m : ℕ} (hm : m ∈ primeExtractionDyadicBlock N k)
    (hlo : A < Real.log (m:ℝ)) (hhi : Real.log (m:ℝ) ≤ A+R) :
    k ∈ giantCandidateThresholdDyadIndices A R := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨hmlo,hmhi⟩ := primeExtractionDyadicBlock_bounds hm
  have hmp : (0:ℝ) < m := Nat.cast_pos.mpr (mem_Ioc.mp (mem_filter.mp hm).1).1
  have hloglo : (k:ℝ)*Real.log 2 ≤ Real.log (m:ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hmlo)
  have hloghi : Real.log (m:ℝ) < ((k:ℝ)+1)*Real.log 2 := by
    rw [← Nat.cast_one,← Nat.cast_add,← Real.log_pow,pow_succ']
    exact Real.log_lt_log hmp (by exact_mod_cast hmhi)
  have h₁ : A/Real.log 2 < (k:ℝ)+1 :=
    (div_lt_iff₀ hl2).mpr (hlo.trans hloghi)
  have h₂ : (k:ℝ) ≤ (A+R)/Real.log 2 :=
    (le_div_iff₀ hl2).mpr (hloglo.trans hhi)
  apply mem_Icc.mpr
  constructor
  · exact Nat.le_of_lt_succ ((Nat.floor_lt (div_nonneg hA hl2.le)).mpr
      (by simpa only [Nat.cast_succ] using h₁))
  · exact Nat.le_floor h₂

theorem giantCandidateThresholdDyad_card_le {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ((giantCandidateThresholdDyadIndices A R).card:ℝ) ≤ 2+R/Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a := A/Real.log 2
  let b := (A+R)/Real.log 2
  have ha : 0 ≤ a := div_nonneg hA hl2.le
  have hab : a ≤ b := div_le_div_of_nonneg_right (by linarith only [hR]) hl2.le
  change ((Icc ⌊a⌋₊ ⌊b⌋₊).card:ℝ) ≤ _
  rw [Nat.card_Icc,Nat.cast_sub (Nat.le_succ_of_le (Nat.floor_mono hab)),Nat.cast_succ]
  have h₁ := Nat.sub_one_lt_floor a
  have h₂ := Nat.floor_le (ha.trans hab)
  have hb : b=a+R/Real.log 2 := add_div _ _ _
  linarith only [h₁,h₂,hb]

theorem giantCandidateThresholdDyad_card_actual_le {γ L : ℝ}
    (hγ : 0 ≤ γ) (hL : 1 ≤ L) :
    ((giantCandidateThresholdDyadIndices (γ*L) (L^(9/10:ℝ))).card:ℝ) ≤
      (2+1/Real.log 2)*L^(9/10:ℝ) := by
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hR := Real.one_le_rpow hL (by norm_num : (0:ℝ)≤9/10)
  calc
    _ ≤ 2+L^(9/10:ℝ)/Real.log 2 :=
      giantCandidateThresholdDyad_card_le (mul_nonneg hγ hL₀) (Real.rpow_nonneg hL₀ _)
    _ ≤ 2*L^(9/10:ℝ)+L^(9/10:ℝ)/Real.log 2 := by linarith only [hR]
    _ = _ := by ring

end
end ArtinMatthews
