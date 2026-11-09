module

public import ArtinMatthews.GiantComparisonCellScale
public import ArtinMatthews.GiantComparisonAuxiliaryLaw


set_option backward.privateInPublic true
@[expose] public section

/-! Source big bands and the actual occupied character cells obey the
minor-arc product scale, uniformly in every performed subset. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantCandidateComparisonBig_card_le {x : ℝ} (S : Finset (GiantCandidateGroupIndex x)) :
    Fintype.card (GiantCandidatePerformedBig S) ≤ Fintype.card (GiantCandidateGroupIndex x) :=
  Fintype.card_le_of_injective (fun g : GiantCandidatePerformedBig S => Sum.inr g.val)
    (fun _ _ he => Subtype.ext (Sum.inr.inj he))

theorem giantComparisonCopied_cap {G : Type*} [DecidableEq G] {k m : ℕ}
    (A B : Finset (G × Fin k)) (h : ∀ g, (idealResidualCopied (some (A,B)) g).card ≤ m) :
    (∀ g, (idealResidualFreeSlots A g).card ≤ m) ∧
      (∀ g, (idealResidualFreeSlots B g).card ≤ m) := by
  constructor
  · intro g
    refine (card_le_card ?_).trans (h g)
    intro i hi
    exact (mem_idealResidualFreeSlots (A ∪ B) g i).mpr
      (mem_union_left B ((mem_idealResidualFreeSlots A g i).mp hi))
  · intro g
    refine (card_le_card ?_).trans (h g)
    intro i hi
    exact (mem_idealResidualFreeSlots (A ∪ B) g i).mpr
      (mem_union_right A ((mem_idealResidualFreeSlots B g i).mp hi))

theorem giantCandidateComparisonPerformedMark_cap {x : ℝ} (S : Finset (GiantCandidateGroupIndex x))
    {k m : ℕ} (A B : Finset (GiantCandidatePerformedBig S × Fin k))
    (h : ∀ g, (idealResidualCopied (some (A,B)) g).card ≤ m) :
    ∀ g : S, 1+(giantCandidatePerformedPattern S (idealResidualCopied (some (A,B))) g).card ≤ m+1 := by
  rintro ⟨i | i, hi⟩
  · simp [giantCandidatePerformedPattern]
  · exact Nat.add_comm m 1 ▸ Nat.add_le_add_left (h ⟨i,hi⟩) 1

theorem giantCandidateComparisonOccupiedCell_eventually (m : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)) {k : ℕ}
      (A : Finset (GiantCandidatePerformedBig S × Fin k)), A.Nonempty →
      (∀ g, (idealResidualFreeSlots A g).card ≤ m) →
      ∀ h : ℝ, 0 < h → Real.exp h ≤ 2 →
      let PA := idealResidualBands (giantCandidatePerformedBigBand S) A
      ∀ j ∈ idealLogCells PA h,
        let L := Real.log x
        let U := giantComparisonCellOrigin h j
        0 < U ∧ Real.exp (L^(40/100:ℝ))/4 ≤ (U:ℝ) ∧
          (U:ℝ) ≤ Real.exp (((m:ℝ)*giantCandidateGroupLogRate)*Real.log L*L^(45/100:ℝ)) ∧
          Real.log ((4*U:ℕ):ℝ) ≤ L^(45/100+2:ℝ) ∧
          ∀ (Q : ℕ) (χ : IdealPrimitiveCharacters Q) (u : IdealSelectedLabels PA),
            idealSelectedProduct u ∉ Ico U (U+4*U) → giantComparisonCellFreeTest PA h j χ u = 0 := by
  let C₀ := (m:ℝ)*giantCandidateGroupLogRate
  have hC₀ : 0 ≤ C₀ := by unfold C₀ giantCandidateGroupLogRate; positivity
  have he := (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<40/100))).eventually_ge_atTop 4
  filter_upwards [Real.tendsto_log_atTop.eventually
      (giantComparisonCellOrigin_source_geometry (40/100) (45/100) C₀ (by norm_num) (by norm_num) hC₀),
    Real.tendsto_log_atTop.eventually he, giantCandidateGroup_total_count_eventually,
    eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hgeom hExp hCount hx hL
  intro S k A hA hcap h hh hhexp PA j hj
  let L := Real.log x
  obtain ⟨i, hi⟩ := hA
  have hpr (v : ↥A) (p : ℕ) (hp : p ∈ PA v) :
      p.Prime ∧ Real.exp (L^(40/100:ℝ)) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^(45/100:ℝ)) := by
    have h := giantCandidateBigGroup_range hx hL hp
    exact ⟨h.1,h.2.1,h.2.2.le⟩
  have hcard : (Fintype.card ↥A:ℝ) ≤ C₀*Real.log L := by
    calc
      _ ≤ ((m * Fintype.card (GiantCandidatePerformedBig S) : ℕ):ℝ) :=
        Nat.cast_le.mpr (giantComparisonSelected_card_le A m hcap)
      _ = (m:ℝ)*(Fintype.card (GiantCandidatePerformedBig S):ℝ) := Nat.cast_mul _ _
      _ ≤ (m:ℝ)*(giantCandidateGroupLogRate*Real.log L) :=
        mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (giantCandidateComparisonBig_card_le S)).trans hCount)
          (Nat.cast_nonneg _)
      _ = C₀*Real.log L := by dsimp only [C₀]; ring
  obtain ⟨hU,hUlo,hUhi,hUlog⟩ := hgeom PA ⟨i,hi⟩ (fun v p hp => (hpr v p hp).1)
    (fun v p hp => (hpr v p hp).2) hcard h hh hhexp j hj
  refine ⟨hU,hUlo,hUhi,hUlog,?_⟩
  intro Q χ u hu
  exact giantComparisonCellOrigin_support PA hh hhexp j hExp
    (giantComparisonSelected_product_lower (giantCandidatePerformedBigBand S) A ⟨i,hi⟩
      (fun g p hp => (giantCandidateBigGroup_range hx hL hp).1) _
      (fun g p hp => (giantCandidateBigGroup_range hx hL hp).2.1)) χ u hu

end
end ArtinMatthews
