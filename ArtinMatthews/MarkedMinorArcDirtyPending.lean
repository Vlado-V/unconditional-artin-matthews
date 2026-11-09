module

public import ArtinMatthews.MarkedMinorArcRawState
public import ArtinMatthews.MarkedMinorArcDirtyDamping


set_option backward.privateInPublic true
@[expose] public section

/-! Literal indexed pending hits and promotion/removal damping. Numeric
prime and anchor repetitions are retained by the actual finite indices. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Actual eligible old indices in one group at the fixed target position. -/
def markedRawGroupHitIndices {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (j : J) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    Finset (Fin (m.1.1 j:ℕ)) := by
  classical
  exact Finset.univ.filter (fun k => MarkedRawParticleHits (P j) z hz (m.2 j k))

theorem markedRawGroupHitIndices_card_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (j : J) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    (markedRawGroupHitIndices m j z hz).card ≤ (m.1.1 j:ℕ) := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem markedRawMemory_group_size_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (j : J) : (m.1.1 j:ℕ) ≤ B :=
  (Finset.single_le_sum (fun i _ => Nat.zero_le (m.1.1 i:ℕ)) (Finset.mem_univ j)).trans m.1.2

theorem markedRawPendingHits_eq_sum_card {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedRawPendingHits m z hz=∑ j, (markedRawGroupHitIndices m j z hz).card := by
  classical
  unfold markedRawPendingHits markedRawGroupHitIndices
  simp only [Finset.sum_boole,Nat.cast_id]

/-- The surviving actual hit indices after promoting k are exactly H.erase k. -/
def markedRawPromotionRemainingHits {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (j : J) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (k : Fin (m.1.1 j:ℕ)) : Finset (Fin (m.1.1 j:ℕ)) :=
  (markedRawGroupHitIndices m j z hz).erase k

theorem markedRawPromotionRemainingHits_card {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (j : J) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (k : Fin (m.1.1 j:ℕ)) (hk : k ∈ markedRawGroupHitIndices m j z hz) :
    (markedRawPromotionRemainingHits m j z hz k).card=(markedRawGroupHitIndices m j z hz).card-1 :=
  Finset.card_erase_of_mem hk

/-- Exact literal promotion sum, including newly stored hits. -/
theorem markedRawPromotion_damping_sum {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (j : J) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (ρ : ℝ) (newHits : ℕ) :
    (∑ k ∈ markedRawGroupHitIndices m j z hz,
      ρ^((markedRawPromotionRemainingHits m j z hz k).card+newHits)) =
      ((markedRawGroupHitIndices m j z hz).card:ℝ)*
        ρ^((markedRawGroupHitIndices m j z hz).card-1+newHits) := by
  classical
  calc
    _ = ∑ _k ∈ markedRawGroupHitIndices m j z hz,
        ρ^((markedRawGroupHitIndices m j z hz).card-1+newHits) :=
      Finset.sum_congr rfl (fun k hk => by rw [markedRawPromotionRemainingHits_card m j z hz k hk])
    _ = _ := by simp

theorem markedRawPromotion_damping_sum_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (j : J) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (newHits : ℕ) :
    (∑ k ∈ markedRawGroupHitIndices m j z hz,
      ρ^((markedRawPromotionRemainingHits m j z hz k).card+newHits)) ≤ 1/(1-ρ)^2 := by
  rw [markedRawPromotion_damping_sum]
  simpa only [Finset.sum_const,nsmul_eq_mul] using
    markedMinorDirty_pending_choices_extra (markedRawGroupHitIndices m j z hz) hρ₀ hρ₁ newHits

set_option backward.isDefEq.respectTransparency false in
/-- The ordered removeNth operation has the same actual remaining-hit count. -/
theorem markedRawParticleList_removeNth_hit_count {P : Finset Nat.Primes} {n : ℕ}
    (a : Fin (n+1) → MarkedRawParticle P) (k : Fin (n+1))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (hk : MarkedRawParticleHits P z hz (a k)) :
    (∑ l : Fin n, if MarkedRawParticleHits P z hz (Fin.removeNth k a l) then (1:ℕ) else 0) =
      (∑ l : Fin (n+1), if MarkedRawParticleHits P z hz (a l) then (1:ℕ) else 0)-1 := by
  classical
  have hh := Fin.sum_univ_succAbove (fun l => if MarkedRawParticleHits P z hz (a l) then (1:ℕ) else 0) k
  simp only [hk,ite_true] at hh
  simpa only [Fin.removeNth,Nat.add_sub_cancel_left] using congrArg (fun n : ℕ => n-1) hh.symm

end ArtinMatthews
