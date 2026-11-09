module

public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import ArtinMatthews.MarkedMinorArcRawGoodFirst
public import ArtinMatthews.MarkedMinorArcBanRawCollision


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source product and ban invariance under the actual slot action. -/
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyRawStateSlot_full_product {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) :
    markedSourceFullProduct (markedRawNumericActive (markedRawSlotEquiv σ s).2.1)=
      markedSourceFullProduct (markedRawNumericActive s.2.1) := by
  change (∏ j, ∏ k, ((s.2.1 j (σ j k)).1:ℕ))=∏ j, ∏ k, ((s.2.1 j k).1:ℕ)
  apply Finset.prod_congr rfl
  intro j _
  exact Equiv.prod_comp (σ j) (fun k => ((s.2.1 j k).1:ℕ))

theorem markedDirtyRawStateSlot_crossBan_iff {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) (target : (j : J) → ↥(P j)) :
    MarkedRawFullCrossBan (markedRawSlotEquiv σ s).2.1 target ↔ MarkedRawFullCrossBan s.2.1 target := by
  constructor
  · rintro ⟨i,j,k,hk⟩
    exact ⟨i,j,σ j k,hk⟩
  · rintro ⟨i,j,k,hk⟩
    refine ⟨i,j,(σ j).symm k,?_⟩
    change (target i).1=(s.2.1 j (σ j ((σ j).symm k))).1
    simpa only [Equiv.apply_symm_apply] using hk

theorem markedDirtyRawStateSlot_distinct_iff {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) :
    (∀ j, Function.Injective ((markedRawSlotEquiv σ s).2.1 j)) ↔ (∀ j, Function.Injective (s.2.1 j)) := by
  constructor
  · intro h j k l hkl
    have he : (markedRawSlotEquiv σ s).2.1 j ((σ j).symm k)=
        (markedRawSlotEquiv σ s).2.1 j ((σ j).symm l) := by
      change s.2.1 j (σ j ((σ j).symm k))=s.2.1 j (σ j ((σ j).symm l))
      simpa only [Equiv.apply_symm_apply] using hkl
    exact (σ j).symm.injective (h j he)
  · intro h j
    exact (h j).comp (σ j).injective

end ArtinMatthews
