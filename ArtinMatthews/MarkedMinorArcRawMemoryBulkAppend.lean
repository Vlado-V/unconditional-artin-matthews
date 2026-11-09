module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! Normalizing actual old-deletion subset coordinates to fixed deleted and
surviving degrees, in the literal survivor-then-birth append order. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The canonical reassembly is exactly the source ordered append, after
only the necessary degree equality cast. -/
theorem markedRawSubsetCanonicalTuple_append {X : Type*} {k : ℕ} (S : Finset (Fin k))
    (deleted : Fin S.card → X) (survivors : Fin (Sᶜ).card → X)
    (hk : (Sᶜ).card+S.card=k) :
    markedRawSubsetCanonicalTuple S deleted survivors=
      fun i => Fin.addCases survivors deleted (Fin.cast hk.symm i) := by
  have hcancel (a : Fin ((Sᶜ).card+S.card)) : Fin.cast hk.symm (Fin.cast hk a)=a := Fin.ext rfl
  funext i
  obtain ⟨a,rfl⟩ := (markedRawSubsetCanonicalIndex S).surjective i
  cases a with
  | inl d =>
    simp only [markedRawSubsetCanonicalTuple,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
    change deleted d=Fin.addCases survivors deleted
      (Fin.cast hk.symm (Fin.cast hk (Fin.natAdd (Sᶜ).card d)))
    simp only [hcancel,Fin.addCases_right]
  | inr r =>
    simp only [markedRawSubsetCanonicalTuple,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    change survivors r=Fin.addCases survivors deleted
      (Fin.cast hk.symm (Fin.cast hk (Fin.castAdd S.card r)))
    simp only [hcancel,Fin.addCases_left]

/-- Deleted coordinates expressed in a fixed actual deleted degree. -/
def markedRawDeletedTupleCast {X : Type*} {k d : ℕ} (S : Finset (Fin k)) (hd : S.card=d)
    (a : Fin k → X) : Fin d → X :=
  fun i => (markedRawSubsetTupleEquiv S a).1 (Fin.cast hd.symm i)

/-- Surviving coordinates expressed in a fixed actual surviving degree. -/
def markedRawSurvivorTupleCast {X : Type*} {k n : ℕ} (S : Finset (Fin k)) (hn : (Sᶜ).card=n)
    (a : Fin k → X) : Fin n → X :=
  fun i => (markedRawSubsetTupleEquiv S a).2 (Fin.cast hn.symm i)

/-- Every actual old subset with the same deleted/surviving degrees has the
same finite symmetric-Fock integration formula. No conclusion of the ghost
operator or any row bound is supplied as an assumption. -/
theorem markedRawMemory_subset_fixed_degree_integral {X : Type*} [Fintype X]
    {k n d : ℕ} (hk : n+d=k) (S : Finset (Fin k)) (hd : S.card=d) (hn : (Sᶜ).card=n)
    (μ : X → ℂ) (g : (Fin k → X) → ℂ) (hg : MarkedRawTupleSymmetric k g)
    (f : (Fin d → X) → (Fin n → X) → ℂ) :
    (∑ a : Fin k → X, (∏ i, μ (a i))*g a*
      f (markedRawDeletedTupleCast S hd a) (markedRawSurvivorTupleCast S hn a))=
      ∑ deleted : Fin d → X, ∑ survivors : Fin n → X,
        (∏ i, μ (deleted i))*(∏ i, μ (survivors i))*
          g (fun i => Fin.addCases survivors deleted (Fin.cast hk.symm i))*f deleted survivors := by
  cases hd
  cases hn
  change (∑ a : Fin k → X, (∏ i, μ (a i))*g a*
    f (markedRawSubsetTupleEquiv S a).1 (markedRawSubsetTupleEquiv S a).2)=_
  simpa only [markedRawSubsetCanonicalTuple_append S _ _ hk] using
    markedRawMemory_subset_symmetric_integral S μ g hg f

end ArtinMatthews
