module

public import ArtinMatthews.ShiftedArithmeticSum
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Int.Lemmas
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Reindexing the actual off-diagonal source pairs by their gcd and full
common-prime part. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def shiftedSourcePairs (B : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter (fun p => p.1≠p.2)

theorem shiftedSourcePairs_parameters {B : ℕ} {p : ℕ×ℕ}
    (hp : p ∈ shiftedSourcePairs B) :
    p.1.gcd p.2 ∈ Finset.Icc 1 B ∧
      shiftedCommonPrimePart p.1 p.2 ∈ shiftedAdmissibleParts B (p.1.gcd p.2) := by
  obtain ⟨hm,hne⟩ := Finset.mem_filter.mp hp
  obtain ⟨hm₁,hm₂⟩ := Finset.mem_product.mp hm
  obtain ⟨hpos₁,hB₁⟩ := Finset.mem_Icc.mp hm₁
  obtain ⟨_hpos₂,hB₂⟩ := Finset.mem_Icc.mp hm₂
  let d := p.1.gcd p.2
  let n := ((p.1 : ℤ)-p.2).natAbs
  have hd : 0<d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hpos₁
  have hn : n≠0 := by
    apply Int.natAbs_ne_zero.mpr
    exact sub_ne_zero.mpr (by exact_mod_cast hne)
  have hdn : d∣n := by
    apply Int.natCast_dvd.mp
    apply dvd_sub
    · exact_mod_cast (show d∣p.1 from Nat.gcd_dvd_left _ _)
    · exact_mod_cast (show d∣p.2 from Nat.gcd_dvd_right _ _)
  have hdD : d ∣ commonPrimePart n d := by
    obtain ⟨k,hk⟩ := hdn
    have hk0 : k≠0 := by intro h; apply hn; simp [hk,h]
    rw [hk,commonPrimePart_mul hd.ne' hk0,commonPrimePart_self hd.ne']
    exact dvd_mul_right _ _
  have hD0 : commonPrimePart n d≠0 := commonPrimePart_ne_zero hn d
  refine ⟨Finset.mem_Icc.mpr ⟨hd,(Nat.le_of_dvd hpos₁ (Nat.gcd_dvd_left _ _)).trans hB₁⟩,?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_,hdD⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hD0,?_⟩,?_⟩
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (commonPrimePart_dvd n d)).trans
      (Int.natAbs_coe_sub_coe_le_of_le hB₁ hB₂)
  · apply Nat.mem_factoredNumbers_of_primeFactors_subset hD0
    intro q hq
    obtain ⟨hqprime,hqD,_⟩ := Nat.mem_primeFactors.mp hq
    exact Nat.mem_primeFactors.mpr ⟨hqprime,
      ((prime_dvd_commonPrimePart_iff hn hqprime d).mp hqD).2,hd.ne'⟩

theorem shiftedSourcePairs_sum_grouped (B : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ shiftedSourcePairs B, f (p.1.gcd p.2) (shiftedCommonPrimePart p.1 p.2)) =
    ∑ d ∈ Finset.Icc 1 B, ∑ D ∈ shiftedAdmissibleParts B d,
      ((shiftedActualPairs B d D).card : ℝ) * f d D := by
  classical
  have hfirst := Finset.sum_fiberwise_of_maps_to
    (s:=shiftedSourcePairs B) (t:=Finset.Icc 1 B) (g:=fun p : ℕ×ℕ => p.1.gcd p.2)
    (fun p hp => (shiftedSourcePairs_parameters hp).1)
    (fun p : ℕ×ℕ => f (p.1.gcd p.2) (shiftedCommonPrimePart p.1 p.2))
  rw [← hfirst]
  apply Finset.sum_congr rfl
  intro d _hd
  let S := (shiftedSourcePairs B).filter (fun p => p.1.gcd p.2=d)
  have hsecond := Finset.sum_fiberwise_of_maps_to
    (s:=S) (t:=shiftedAdmissibleParts B d)
    (g:=fun p : ℕ×ℕ => shiftedCommonPrimePart p.1 p.2)
    (fun p hp => by
      obtain ⟨hp,hg⟩ := Finset.mem_filter.mp hp
      simpa only [hg] using (shiftedSourcePairs_parameters hp).2)
    (fun p : ℕ×ℕ => f (p.1.gcd p.2) (shiftedCommonPrimePart p.1 p.2))
  change (∑ p∈S,_) = _
  rw [← hsecond]
  apply Finset.sum_congr rfl
  intro D _hD
  have hset : S.filter (fun p => shiftedCommonPrimePart p.1 p.2=D) =
      shiftedActualPairs B d D := by
    ext p
    simp only [S,shiftedSourcePairs,shiftedActualPairs,Finset.mem_filter]
    tauto
  rw [hset]
  calc
    _ = ∑ _p∈shiftedActualPairs B d D, f d D := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨_,_,hg,hpart⟩ := Finset.mem_filter.mp hp
      rw [hg,hpart]
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end ArtinMatthews
