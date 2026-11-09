module

public import ArtinMatthews.GiantSignedBirthPivots
public import ArtinMatthews.GiantSignedBirthTypedBand


set_option backward.privateInPublic true
@[expose] public section

/-! Extend the retained prime memo by precisely the performed local
draws, leaving absent addresses unchanged. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B I : Type*} {M n H : ℕ} [Fintype I]
    {PB : B → Finset ℕ} (hPB : ∀ g p, p ∈ PB g → p.Prime)

def giantSignedUniformBirthConditionalValues
    (e : I ↪ GiantSignedUniformBirthAddress B M n H)
    (old : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes)
    (t : (i : I) → PB (giantSignedUniformBirthGroup (e i))) :
    GiantSignedUniformBirthAddress B M n H → Option Nat.Primes :=
  let P (a : GiantSignedUniformBirthAddress B M n H) :=
    giantSignedTypedPrimeBand (PB (giantSignedUniformBirthGroup a)) (hPB (giantSignedUniformBirthGroup a))
  markedConditionalBirthValues (P := P) old (markedBirthDrawSet e)
    (markedBirthDrawTupleEquiv P e e.injective (fun i =>
      giantSignedTypedPrimeBandEquiv (PB (giantSignedUniformBirthGroup (e i)))
        (hPB (giantSignedUniformBirthGroup (e i))) (t i)))

theorem giantSignedUniformBirthConditionalValues_draw
    (e : I ↪ GiantSignedUniformBirthAddress B M n H)
    (old : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes)
    (t : (i : I) → PB (giantSignedUniformBirthGroup (e i))) (i : I) :
    giantSignedUniformBirthConditionalValues hPB e old t (e i) =
      some (⟨(t i).val,hPB (giantSignedUniformBirthGroup (e i)) (t i).val (t i).property⟩ : Nat.Primes) := by
  unfold giantSignedUniformBirthConditionalValues
  dsimp only
  rw [markedBirthDrawValues_apply, giantSignedTypedPrimeBandEquiv_value] <;> rfl

theorem giantSignedUniformBirthConditionalValues_outside
    (e : I ↪ GiantSignedUniformBirthAddress B M n H)
    (old : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes)
    (t : (i : I) → PB (giantSignedUniformBirthGroup (e i)))
    (a : GiantSignedUniformBirthAddress B M n H) (ha : a ∉ Set.range e) :
    giantSignedUniformBirthConditionalValues hPB e old t a = old a := by
  have hdraw : a ∉ markedBirthDrawSet e := by
    intro h
    obtain ⟨i,hi⟩ := (markedBirthDrawEquiv e e.injective).surjective ⟨a,h⟩
    exact ha ⟨i,congrArg Subtype.val hi⟩
  unfold giantSignedUniformBirthConditionalValues markedConditionalBirthValues
  rw [dite_eq_right hdraw]

def GiantSignedUniformBirthConditionalGate [Fintype B]
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) (o : GiantSignedBirthOperation n)
    (values : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes) : Prop :=
  ∀ a ∈ giantSignedUniformBirthStageNonpivots σ o,
    values a ≠ none ∧ values a = values (giantSignedUniformBirthPivot σ a)

end
end ArtinMatthews
