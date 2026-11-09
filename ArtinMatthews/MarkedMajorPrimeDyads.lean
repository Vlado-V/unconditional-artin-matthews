module

public import ArtinMatthews.MarkedMajorLabelPolynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log


set_option backward.privateInPublic true
@[expose] public section

/-! Exact ordinary dyads for an arbitrary finite prime band. The finite
partition and its logarithmic number of pieces are proved from Nat.log. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

noncomputable def markedMajorPrimeDyadIndices (P : Finset ℕ) : Finset ℕ := P.image (Nat.log 2)

def markedMajorPrimeDyad (P : Finset ℕ) (j : ℕ) : Finset ℕ := P.filter (fun p => Nat.log 2 p=j)

 theorem markedMajorPrimeDyad_sum (P : Finset ℕ) (f : ℕ → ℂ) :
    (∑ p ∈ P, f p) = ∑ j ∈ markedMajorPrimeDyadIndices P, ∑ p ∈ markedMajorPrimeDyad P j, f p := by
  classical
  exact (sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem (Nat.log 2) hp) f).symm

 theorem markedMajorPrimeDyad_bounds (P : Finset ℕ) (j p : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hp : p ∈ markedMajorPrimeDyad P j) :
    p.Prime ∧ (2:ℕ)^j ≤ p ∧ p < 2*(2:ℕ)^j := by
  have hmem := mem_filter.mp hp
  have hprime := hP p hmem.1
  refine ⟨hprime,?_,?_⟩
  · simpa only [hmem.2] using Nat.pow_log_le_self 2 hprime.ne_zero
  · simpa only [hmem.2,Nat.succ_eq_add_one,pow_succ,mul_comm] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) p

 theorem markedMajorPrimeDyadIndices_card (P : Finset ℕ) (Z : ℝ) (hZ : 1 ≤ Z)
    (hcap : ∀ p ∈ P, (p:ℝ) ≤ Z) :
    ((markedMajorPrimeDyadIndices P).card:ℝ) ≤ 1+Real.log Z/Real.log 2 := by
  classical
  have hsub : markedMajorPrimeDyadIndices P ⊆ range (Nat.log 2 ⌊Z⌋₊+1) := by
    intro j hj
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
    apply mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.log_mono_right ((Nat.le_floor_iff (by linarith)).mpr (hcap p hp)))
  have hc : ((markedMajorPrimeDyadIndices P).card:ℝ) ≤ (Nat.log 2 ⌊Z⌋₊:ℝ)+1 := by
    exact_mod_cast (card_le_card hsub).trans_eq (card_range _)
  have hf : (0:ℝ) < ⌊Z⌋₊ := by
    have hn : 1 ≤ ⌊Z⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hZ)
    exact_mod_cast hn
  have hh : (Nat.log 2 ⌊Z⌋₊:ℝ) ≤ Real.log Z/Real.log 2 := by
    calc
      _ ≤ Real.logb 2 (⌊Z⌋₊:ℝ) := Real.natLog_le_logb _ _
      _ ≤ _ := div_le_div_of_nonneg_right (Real.log_le_log hf (Nat.floor_le (by linarith)))
        (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  linarith

 theorem markedMajorPrimeDyad_log_bounds (P : Finset ℕ) (j : ℕ) (a b : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hlo : ∀ p ∈ P, a ≤ Real.log p)
    (hhi : ∀ p ∈ P, Real.log p ≤ b) (hj : j ∈ markedMajorPrimeDyadIndices P) :
    1 < ((2:ℕ)^j:ℝ) ∧ a-Real.log 2 ≤ Real.log (((2:ℕ)^j:ℝ)) ∧
      Real.log (((2:ℕ)^j:ℝ)) ≤ b := by
  classical
  obtain ⟨p,hp,hpj⟩ := mem_image.mp hj
  have hpd : p ∈ markedMajorPrimeDyad P j := mem_filter.mpr ⟨hp,hpj⟩
  obtain ⟨hprime,hpl,hpu⟩ := markedMajorPrimeDyad_bounds P j p hP hpd
  have hj0 : 0 < j := by
    by_contra h
    have hjz : j=0 := by omega
    rw [hjz] at hpu
    norm_num at hpu
    have := hprime.two_le
    omega
  have hY : 1 < ((2:ℕ)^j:ℝ) := by
    exact_mod_cast Nat.one_lt_pow hj0.ne' (by norm_num : 1 < (2:ℕ))
  have hpp : (0:ℝ) < p := by exact_mod_cast hprime.pos
  have hlow : (2:ℝ)*((2:ℕ)^j:ℝ) > p := by exact_mod_cast hpu
  have hlog : Real.log p ≤ Real.log 2+Real.log (((2:ℕ)^j:ℝ)) := by
    rw [← Real.log_mul (by norm_num) (by linarith : (0:ℝ)<((2:ℕ)^j:ℝ)).ne']
    exact Real.log_le_log hpp hlow.le
  refine ⟨hY,by linarith [hlo p hp],?_⟩
  exact (Real.log_le_log (by linarith) (by exact_mod_cast hpl)).trans (hhi p hp)

end ArtinMatthews
