module

public import ArtinMatthews.GiantSignedBirthConditionalValues


set_option backward.privateInPublic true
@[expose] public section

/-! Each actual dependent draw costs one tilted prime atom, including
earlier pivots in its own ordered local batch. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantSignedUniformBirthConditional_mass
    {B I : Type*} {M n H : ℕ} [Fintype B] [Fintype I]
    {PB : B → Finset ℕ} (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 1 ≤ N)
    (hatom : ∀ g p, ν g p ≤ Δ) (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ N)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H))
    (o : GiantSignedBirthOperation n) (e : I ↪ GiantSignedUniformBirthAddress B M n H)
    (old : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes)
    (hold : ∀ a, giantSignedUniformBirthOperation M n H a = o → old a = none) :
    (∑ t : (i : I) → PB (giantSignedUniformBirthGroup (e i)),
      if GiantSignedUniformBirthConditionalGate σ o
          (giantSignedUniformBirthConditionalValues hPB e old t)
      then ∏ i, ν (giantSignedUniformBirthGroup (e i)) (t i) else 0) ≤
      Δ^(giantSignedUniformBirthStageNonpivots σ o).card * N^(Fintype.card I) := by
  let A := GiantSignedUniformBirthAddress B M n H
  letI : LinearOrder A := giantSignedUniformBirthChronologicalOrder
  let P (a : A) := giantSignedTypedPrimeBand (PB (giantSignedUniformBirthGroup a))
    (hPB (giantSignedUniformBirthGroup a))
  let E (a : A) : ↥(PB (giantSignedUniformBirthGroup a)) ≃ ↥(P a) :=
    giantSignedTypedPrimeBandEquiv _ _
  let ν' (a : A) (p : P a) := ν (giantSignedUniformBirthGroup a) ((E a).symm p)
  let S := giantSignedUniformBirthStageNonpivots σ o
  have hmass (a : A) : (∑ p : P a, ν' a p) ≤ N := by
    rw [← (E a).sum_comp (ν' a)]
    simpa only [ν', Equiv.symm_apply_apply] using hMass (giantSignedUniformBirthGroup a)
  have hearlier (a : A) (ha : a ∈ S) : giantSignedUniformBirthPivot σ a < a :=
    giantSignedUniformBirthPivot_earlier σ (Finset.mem_filter.mp ha).1
  have habsent (a : A) (ha : a ∈ S) (_ : a ∉ markedBirthDrawSet e) : old a = none :=
    hold a (Finset.mem_filter.mp ha).2
  have hb := markedInjectedBirth_sum_le (P := P) ν' (fun a p => hν _ _) hΔ hN
    (fun a p => hatom _ _) hmass e e.injective S (giantSignedUniformBirthPivot σ) old hearlier habsent
  let T : ((i : I) → PB (giantSignedUniformBirthGroup (e i))) ≃ ((i : I) → P (e i)) :=
    Equiv.piCongrRight (fun i => E (e i))
  let f (t : (i : I) → P (e i)) : ℝ :=
    if MarkedConditionalBirthGate S (giantSignedUniformBirthPivot σ) old (markedBirthDrawSet e)
      (markedBirthDrawTupleEquiv P e e.injective t) then ∏ i, ν' (e i) (t i) else 0
  have hbound : (∑ t, f (T t)) ≤ Δ^S.card * N^(Fintype.card I) :=
    (T.sum_comp f).le.trans hb
  refine (Finset.sum_congr rfl (fun t _ => ?_)).le.trans hbound
  have hgate : GiantSignedUniformBirthConditionalGate σ o
      (giantSignedUniformBirthConditionalValues hPB e old t) ↔
      MarkedConditionalBirthGate S (giantSignedUniformBirthPivot σ) old (markedBirthDrawSet e)
        (markedBirthDrawTupleEquiv P e e.injective (T t)) := Iff.rfl
  unfold f
  rw [hgate]
  simp only [ν', T, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply]

end
end ArtinMatthews
