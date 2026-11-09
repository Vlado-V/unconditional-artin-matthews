module

public import ArtinMatthews.MarkedMinorArcDirtyTargetChoices


set_option backward.privateInPublic true
@[expose] public section

/-! Exact actual target-neighbor count in the charged dirty row. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedRawDirtyTargetChoices_card_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hdist : ∀ j, Function.Injective (source j))
    {Pstar : Finset Nat.Primes} (a : MarkedRawParticle Pstar)
    (hban : ∀ j k, (source j k).1 ≠ a.1.1)
    (Zs : Finset ℕ) (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z w : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : ∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16)
    {ε : ℝ} (hε : 0 < ε) (hp : 1/(a.1.1:ℕ) ≤ ε)
    (hg : ((markedMinorIntegerTau r w/markedMinorIntegerTau r z:ℝ):AddCircle (1:ℝ)) ∉
      markedPairBadRoots Q T (100*ε)) :
    (markedRawDirtyTargetChoices source a Zs V hV z T Q).card ≤ 33 := by
  classical
  let F := markedRawDirtyTargetChoices source a Zs V hV z T Q
  change F.card ≤ 33
  by_cases hF : F.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hF
    have hnum (c) (hc : c ∈ F) : c.1=c₀.1 :=
      markedRawDirtyTargetChoices_numeric_unique source hdis hdist a hban Zs V hV z w T Q r
        hd hz hbox hε hp hg c c₀ hc hc₀
    let W := F.image (fun c => c.2.1)
    have hcard : F.card=W.card := by
      symm
      apply Finset.card_image_iff.mpr
      intro c hc d hdd he
      apply Prod.ext ((hnum c hc).trans (hnum d hdd).symm)
      exact Subtype.ext he
    rw [hcard]
    apply markedBan_targets_card_le r z w (markedMinorIntegerDet z c₀.2.1) hd hz W
    intro v hv
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
    refine ⟨?_,hbox _ c.2.2⟩
    have hjc := (Finset.mem_filter.mp hc).2.2.2.1
    have hj₀ := (Finset.mem_filter.mp hc₀).2.2.2.1
    rw [hjc,hj₀,hnum c hc]
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    rw [he]
    norm_num

theorem markedRawDirtyTargetChoices_weight_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hdist : ∀ j, Function.Injective (source j))
    {Pstar : Finset Nat.Primes} (a : MarkedRawParticle Pstar)
    (hban : ∀ j k, (source j k).1 ≠ a.1.1)
    (Zs : Finset ℕ) (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z w : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : ∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16)
    {ε : ℝ} (hε : 0 < ε) (hp : 1/(a.1.1:ℕ) ≤ ε)
    (hg : ((markedMinorIntegerTau r w/markedMinorIntegerTau r z:ℝ):AddCircle (1:ℝ)) ∉
      markedPairBadRoots Q T (100*ε)) :
    (∑ c ∈ markedRawDirtyTargetChoices source a Zs V hV z T Q,
      markedUniformOmissionWeight M c.1.1) ≤ 33*(M:ℝ)⁻¹^(Fintype.card J) := by
  have hc := markedRawDirtyTargetChoices_card_le source hdis hdist a hban Zs V hV z w T Q r
    hd hz hbox hε hp hg
  simp only [markedUniformOmissionWeight_eq,Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

end ArtinMatthews
