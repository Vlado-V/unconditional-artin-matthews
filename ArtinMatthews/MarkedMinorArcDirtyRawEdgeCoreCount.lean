module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFiniteSums
public import ArtinMatthews.MarkedMinorArcDirtyGoodRow


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite coding of the source-omission/old-index/target row into
the literal counted dirty choices. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev MarkedDirtyRawCountedChoice {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) :=
  Σ k : ↥(markedRawDirtyDistinguishedIndices source memory jstar),
    Σ c : ↥(markedRawDirtyTargetChoices source (memory.2 jstar k.1)
      (markedRawPromotionProductSupport memory I) V hV z T Q),
      {t : MarkedRawPromotionTuple memory I // markedRawPromotionTuplePrimeProduct memory I t=c.1.1.2}

instance markedDirtyRawCountedChoice_fintype {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) :
    Fintype (MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q) := by
  classical
  unfold MarkedDirtyRawCountedChoice
  infer_instance

def markedDirtyRawCountedWeight {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (ρ : ℝ)
    (c : MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q) : ℝ :=
  markedUniformOmissionWeight M c.2.1.1.1.1 *
    markedRawPromotionTupleDamping memory I c.2.1.1.2.1 (hV _ c.2.1.1.2.2) ρ (fun _ => 0) c.2.2.1

theorem markedDirtyRawCountedWeight_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (ρ : ℝ) :
    (∑ c : MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q,
      markedDirtyRawCountedWeight source memory jstar I V hV z T Q ρ c) =
      markedRawDirtyGoodChoiceMass source memory jstar I V hV z T Q ρ (fun _ _ _ => 0) := by
  classical
  rw [Fintype.sum_sigma]
  unfold markedRawDirtyGoodChoiceMass
  rw [← Finset.sum_coe_sort (markedRawDirtyDistinguishedIndices source memory jstar)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fintype.sum_sigma]
  rw [← Finset.sum_coe_sort (markedRawDirtyTargetChoices source (memory.2 jstar k.1)
    (markedRawPromotionProductSupport memory I) V hV z T Q)]
  apply Finset.sum_congr rfl
  intro c _
  unfold markedDirtyRawCountedWeight
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_subtype (Finset.univ.filter (fun t : MarkedRawPromotionTuple memory I =>
    markedRawPromotionTuplePrimeProduct memory I t=c.1.1.2)) (by simp)
    (fun t => markedRawPromotionTupleDamping memory I c.1.2.1 (hV _ c.1.2.2) ρ (fun _ => 0) t)).symm

end ArtinMatthews
