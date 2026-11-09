module

public import ArtinMatthews.GiantSignedGhostRow


set_option backward.privateInPublic true
@[expose] public section

/-! Literal zero-residue counting and the factorial joint measure for
indexed ghost deletion. No prime-cardinality factor is inserted. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedZeroTuple {P : Finset ℕ} {n : ℕ} (p : Fin n → P) :
    Fin n → GiantSignedParticle P := fun i => ⟨p i, 0⟩

theorem giantSignedGhost_zeroTuple_sum {P : Finset ℕ} [∀ p : P, NeZero p.val]
    (ν : P → ℂ) (n : ℕ) (F : (Fin n → GiantSignedParticle P) → ℂ) :
    (∑ a : Fin n → GiantSignedParticle P,
      if ∀ i, (a i).2 = 0 then (∏ i, ν (a i).1) * F a else 0) =
        ∑ p : Fin n → P, (∏ i, ν (p i)) * F (giantSignedZeroTuple p) := by
  classical
  let good := (Finset.univ : Finset (Fin n → GiantSignedParticle P)).filter
    (fun a => ∀ i, (a i).2 = 0)
  have ha (a : Fin n → GiantSignedParticle P) (h : a ∈ good) :
      a = giantSignedZeroTuple (fun i => (a i).1) := by
    have hz := (Finset.mem_filter.mp h).2
    funext i
    change a i = ⟨(a i).1, 0⟩
    exact (Sigma.eta (a i)).symm.trans
      (congrArg (fun r : ZMod (a i).1.val => (⟨(a i).1, r⟩ : GiantSignedParticle P)) (hz i))
  rw [← Finset.sum_filter]
  change (∑ a ∈ good, _) = _
  apply Finset.sum_bij (fun a _ => fun i => (a i).1)
  · intro a h
    exact Finset.mem_univ _
  · intro a ha' b hb' hab
    calc
      a = giantSignedZeroTuple (fun i => (a i).1) := ha a ha'
      _ = giantSignedZeroTuple (fun i => (b i).1) := congrArg giantSignedZeroTuple hab
      _ = b := (ha b hb').symm
  · intro p _
    refine ⟨giantSignedZeroTuple p, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => rfl⟩
  · intro a h
    rw [ha a h]
    simp only [giantSignedZeroTuple]

theorem giantSignedGhost_fixed_joint {P : Finset ℕ} [∀ p : P, NeZero p.val]
    (ν : P → ℂ) (n t : ℕ)
    (g : (Fin (n+t) → GiantSignedParticle P) → ℂ)
    (hg : MarkedRawTupleSymmetric (n+t) g)
    (H : (Fin t → P) → (Fin n → GiantSignedParticle P) → ℂ) :
    (∑ a : Fin (n+t) → GiantSignedParticle P,
      ((∏ i, ν (a i).1) / (Nat.factorial (n+t) : ℂ)) * g a *
        ∑ S : MarkedRawDeletionBatch (n+t) t,
          let deleted := markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) a
          let survivors := markedRawSurvivorTupleCast S.1
            (markedRawDeletionBatch_survivor_card rfl S) a
          if ∀ i, (deleted i).2 = 0 then H (fun i => (deleted i).1) survivors else 0) =
      ∑ p : Fin t → P, ∑ survivors : Fin n → GiantSignedParticle P,
        ((∏ i, ν (p i)) * (∏ i, ν (survivors i).1)) /
          ((Nat.factorial t : ℂ) * (Nat.factorial n : ℂ)) *
          g (Fin.append survivors (giantSignedZeroTuple p)) * H p survivors := by
  classical
  rw [markedRawMemory_factorial_batch_delete rfl (fun z : GiantSignedParticle P => ν z.1) g hg
    (fun deleted survivors =>
      if ∀ i, (deleted i).2 = 0 then H (fun i => (deleted i).1) survivors else 0)]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro survivors _
  have he := giantSignedGhost_zeroTuple_sum ν t (fun deleted =>
    (∏ i, ν (survivors i).1) / ((Nat.factorial t : ℂ) * (Nat.factorial n : ℂ)) *
      g (Fin.append survivors deleted) * H (fun i => (deleted i).1) survivors)
  calc
    _ = ∑ deleted : Fin t → GiantSignedParticle P,
        if ∀ i, (deleted i).2 = 0 then
          (∏ i, ν (deleted i).1) *
            ((∏ i, ν (survivors i).1) / ((Nat.factorial t : ℂ) * (Nat.factorial n : ℂ)) *
              g (Fin.append survivors deleted) * H (fun i => (deleted i).1) survivors)
        else 0 := by
      apply Finset.sum_congr rfl
      intro deleted _
      by_cases hz : ∀ i, (deleted i).2 = 0
      · simp only [Fin.cast_refl, ite_eq_left hz]
        change _ * g (Fin.append survivors deleted) * _ = _
        ring
      · simp only [hz, ite_false, mul_zero]
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro p _
      simp only [giantSignedZeroTuple]
      ring

end
end ArtinMatthews
