module

public import ArtinMatthews.MarkedSparseIntervals
public import Mathlib.Topology.Order.Compact


set_option backward.privateInPublic true
@[expose] public section

/-! A separated-sample energy estimate controls the sum of the actual
maxima on closed unit intervals. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem unitInterval_sum_at_points_le (I : Finset ℤ) (Q : ℝ → Prop)
    (f : ℝ → ℝ) (point : ℤ → ℝ) {C : ℝ}
    (hp : ∀ z ∈ I, point z ∈ Set.Icc (z : ℝ) ((z : ℝ)+1))
    (hQ : ∀ z ∈ I, Q (point z))
    (hsamples : ∀ S : Finset ℝ, S.card ≤ I.card → (∀ t ∈ S, Q t) →
      (∀ t ∈ S, ∀ s ∈ S, t ≠ s → 1 ≤ |t-s|) → (∑ t ∈ S, f t) ≤ C) :
    (∑ z ∈ I, f (point z)) ≤ 3*C := by
  classical
  have hclass (j : ℤ) : (∑ z ∈ I.filter (fun z => z%3=j), f (point z)) ≤ C := by
    let J := I.filter (fun z => z%3=j)
    have hJ (z : ℤ) (hz : z ∈ J) : z ∈ I ∧ z%3=j := Finset.mem_filter.mp hz
    have hinj : Set.InjOn point (J : Set ℤ) := by
      intro z hz w hw heq
      by_contra hne
      have hs := unitInterval_mod_three_separated (hp z (hJ z hz).1)
        (hp w (hJ w hw).1) ((hJ z hz).2.trans (hJ w hw).2.symm) hne
      rw [heq, sub_self, abs_zero] at hs
      norm_num at hs
    have hcard : (J.image point).card ≤ I.card :=
      (Finset.card_image_le).trans (Finset.card_filter_le _ _)
    have hc := hsamples (J.image point) hcard (by
      intro t ht
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
      exact hQ z (hJ z hz).1) (by
      intro t ht s hs hne
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hs
      exact unitInterval_mod_three_separated (hp z (hJ z hz).1)
        (hp w (hJ w hw).1) ((hJ z hz).2.trans (hJ w hw).2.symm)
        (fun h => hne (congrArg point h)))
    rwa [Finset.sum_image hinj] at hc
  have hmap : ∀ z ∈ I, z%3 ∈ Finset.Ico (0 : ℤ) 3 := by
    intro z hz
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg z (by norm_num), Int.emod_lt_of_pos z (by norm_num)⟩
  calc
    _ = ∑ j ∈ Finset.Ico (0 : ℤ) 3, ∑ z ∈ I.filter (fun z => z%3=j), f (point z) :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ _j ∈ Finset.Ico (0 : ℤ) 3, C := Finset.sum_le_sum (fun j _ => hclass j)
    _ = 3*C := by norm_num

/-- Actual suprema, rather than a preselected sampling surrogate. -/
theorem unitInterval_sum_sup_le (I : Finset ℤ) (Q : ℝ → Prop)
    (f : ℝ → ℝ) (hf : Continuous f) {C : ℝ}
    (hQ : ∀ z ∈ I, ∀ t ∈ Set.Icc (z : ℝ) ((z : ℝ)+1), Q t)
    (hsamples : ∀ S : Finset ℝ, S.card ≤ I.card → (∀ t ∈ S, Q t) →
      (∀ t ∈ S, ∀ s ∈ S, t ≠ s → 1 ≤ |t-s|) → (∑ t ∈ S, f t) ≤ C) :
    (∑ z ∈ I, sSup (f '' Set.Icc (z : ℝ) ((z : ℝ)+1))) ≤ 3*C := by
  classical
  have hmax (z : ℤ) : ∃ t ∈ Set.Icc (z : ℝ) ((z : ℝ)+1),
      IsMaxOn f (Set.Icc (z : ℝ) ((z : ℝ)+1)) t :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by linarith)) hf.continuousOn
  choose point hp hmax using hmax
  have heq (z : ℤ) : sSup (f '' Set.Icc (z : ℝ) ((z : ℝ)+1)) = f (point z) := by
    apply le_antisymm
    · apply csSup_le ⟨f (point z), Set.mem_image_of_mem f (hp z)⟩
      rintro _ ⟨t,ht,rfl⟩
      exact hmax z ht
    · apply le_csSup _ (Set.mem_image_of_mem f (hp z))
      refine ⟨f (point z), ?_⟩
      rintro _ ⟨t,ht,rfl⟩
      exact hmax z ht
  simp_rw [heq]
  exact unitInterval_sum_at_points_le I Q f point (fun z _ => hp z)
    (fun z hz => hQ z hz (point z) (hp z)) hsamples

end
end ArtinMatthews
