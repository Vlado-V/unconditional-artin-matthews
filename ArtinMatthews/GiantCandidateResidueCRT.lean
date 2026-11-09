module

public import ArtinMatthews.MarkedProgressionCounting
public import ArtinMatthews.RoughCharacterDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Each small-prime divisor condition meets an arbitrary candidate
residue class in a single CRT class, with a unit endpoint error. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateRoughResidueIoc (P : Finset ℕ) (M N Q a : ℕ) : Finset ℕ :=
  ((Ioc M N).filter (fun n => Nat.ModEq Q n a)).filter (fun n => ∀ p ∈ P, ¬p ∣ n)

theorem giantCandidateSubsetDivisor_coprime {P S : Finset ℕ} {Q : ℕ}
    (hS : S ⊆ P) (hcop : ∀ p ∈ P,p.Coprime Q) :
    (roughSubsetDivisor S).Coprime Q :=
  Nat.Coprime.prod_left (fun p hp => hcop p (hS hp))

theorem giantCandidate_divisor_residue_interval_error (M N d Q a : ℕ) (hMN : M ≤ N)
    (hd : 0 < d) (hQ : 0 < Q) (hcop : d.Coprime Q) :
    |(∑ n ∈ (Ioc M N).filter (fun n => Nat.ModEq Q n a),if d ∣ n then (1:ℝ) else 0) -
      ((N-M:ℕ):ℝ)/(Q:ℝ)/(d:ℝ)| ≤ 1 := by
  classical
  let b := Nat.chineseRemainder hcop 0 a
  have he (n : ℕ) : (Nat.ModEq Q n a ∧ d ∣ n) ↔ Nat.ModEq (d*Q) n b := by
    constructor
    · rintro ⟨hn,hdn⟩
      exact Nat.chineseRemainder_modEq_unique hcop (Nat.modEq_zero_iff_dvd.mpr hdn) hn
    · intro hn
      obtain ⟨hn₁,hn₂⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mpr hn
      exact ⟨hn₂.trans b.property.2,Nat.modEq_zero_iff_dvd.mp (hn₁.trans b.property.1)⟩
  have hset : (((Ioc M N).filter (fun n => Nat.ModEq Q n a)).filter (fun n => d ∣ n)) =
      (Ioc M N).filter (fun n => Nat.ModEq (d*Q) n b) := by
    ext n
    simp only [mem_filter, and_assoc, he]
  rw [← sum_filter,hset,sum_const,nsmul_eq_mul,mul_one,Nat.cast_sub hMN]
  have hden : ((N:ℝ)-(M:ℝ))/(Q:ℝ)/(d:ℝ) = ((N:ℝ)-(M:ℝ))/((d*Q:ℕ):ℝ) := by
    push_cast
    ring
  rw [hden]
  exact marked_interval_residue_error M N (d*Q) b hMN (Nat.mul_pos hd hQ)

theorem giantCandidate_divisor_residue_interval_le (M N d Q a : ℕ) (hMN : M ≤ N)
    (hd : 0 < d) (hQ : 0 < Q) (hcop : d.Coprime Q) :
    (∑ n ∈ (Ioc M N).filter (fun n => Nat.ModEq Q n a),if d ∣ n then (1:ℝ) else 0) ≤
      ((N-M:ℕ):ℝ)/(Q:ℝ)/(d:ℝ)+1 := by
  have h := (abs_le.mp (giantCandidate_divisor_residue_interval_error M N d Q a hMN hd hQ hcop)).2
  linarith only [h]

end
end ArtinMatthews
