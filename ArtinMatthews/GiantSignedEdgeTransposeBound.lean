module

public import ArtinMatthews.GiantSignedEdgeRowBound
public import ArtinMatthews.GiantSignedEdgeReverseBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The transposed positive edge has the original ban on its source
labels and the exact ratio between its two promotion normalizations. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

def giantSignedEdgePositiveFixedApply (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (m : GiantSignedMemory P) (S T : (j : J) → Finset (Fin (t j))) : ℝ :=
  ∑ target : GiantSignedPrimeTuple P t,
    (∏ j, (V j)⁻¹ ^ (T j).card) * giantSignedFreshPrimeRealMass ν T target *
      ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
        if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
          giantSignedPendingDamping ρ m *
            giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) *
            f target (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
        else 0

theorem giantSignedEdgePositiveApply_eq_sum_fixed (ν : (j : J) → P j → ℝ)
    (V : J → ℝ) (ρ : ℝ) (d : ℤ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ) (m : GiantSignedMemory P) :
    giantSignedEdgePositiveApply ν V ρ d source f m =
      ∑ S, ∑ T, giantSignedEdgePositiveFixedApply ν V ρ d source f m S T := rfl

theorem giantSignedEdgePositiveFixedApply_nonneg (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out) (m : GiantSignedMemory P)
    (S T : (j : J) → Finset (Fin (t j))) :
    0 ≤ giantSignedEdgePositiveFixedApply ν V ρ d source f m S T := by
  unfold giantSignedEdgePositiveFixedApply
  apply Finset.sum_nonneg
  intro target _
  apply mul_nonneg
  · exact mul_nonneg
      (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j)) _))
      (giantSignedFreshPrimeRealMass_nonneg ν hν T target)
  · apply Finset.sum_nonneg
    intro e _
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (giantSignedPendingDamping_nonneg hρ _)
          (giantSignedPendingDamping_nonneg hρ _)) (hf _ _)
    · exact le_rfl

def giantSignedEdgeTransposePositiveApply (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (m : GiantSignedMemory P) : ℝ :=
  ∑ S : (j : J) → Finset (Fin (t j)),
    ∑ T : (j : J) → Finset (Fin (t j)),
      if GiantSignedEdgePromotionBan D S source then
        (∏ j, (V j) ^ (T j).card / (V j) ^ (S j).card) *
          giantSignedEdgePositiveFixedApply ν V ρ d source f m S T
      else 0

theorem giantSignedEdgeTransposePositiveApply_le (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) {vmin vmax ρ : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (hρ : 0 ≤ ρ) (tmax : ℕ) (ht : ∀ j, t j ≤ tmax)
    (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out) (m : GiantSignedMemory P) :
    giantSignedEdgeTransposePositiveApply ν V ρ d D source f m ≤
      (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J *
        giantSignedEdgePositiveApply ν V ρ d source f m := by
  classical
  let R := (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J
  have hR : 0 ≤ R := pow_nonneg (giantSignedEdgeReverseConstant_nonneg _ _ _) _
  have hc (S : (j : J) → Finset (Fin (t j))) (j : J) : (S j).card ≤ tmax :=
    (show (S j).card ≤ t j from by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (S j))).trans (ht j)
  unfold giantSignedEdgeTransposePositiveApply
  rw [giantSignedEdgePositiveApply_eq_sum_fixed, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  have hF := giantSignedEdgePositiveFixedApply_nonneg ν hν V
    (fun j => (lt_of_lt_of_le hvmin (hVmin j)).le) hρ d source f hf m S T
  split_ifs
  · exact mul_le_mul_of_nonneg_right
      (giantSignedEdgeReverseFactor_bound V hvmin hVmin hVmax
        (fun j => (S j).card) (fun j => (T j).card) tmax (hc S) (hc T)) hF
  · exact mul_nonneg hR hF

theorem giantSignedEdgeTransposePositiveApply_bound (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) {vmin vmax massMax ρ v B : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hB : 0 ≤ B)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) (d : ℤ) (D : ℕ)
    (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hfn : ∀ target out, 0 ≤ f target out)
    (hf : ∀ target out, f target out ≤ B * v ^ (∑ j, out.1 j))
    (m : GiantSignedMemory P) :
    giantSignedEdgeTransposePositiveApply ν V ρ d D source f m ≤
      B * v ^ (∑ j, m.1 j) *
        (giantSignedEdgeReverseConstant vmin vmax tmax *
          giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J := by
  have hVp (j : J) : 0 < V j := lt_of_lt_of_le hvmin (hVmin j)
  have hRate (j : J) : (V j)⁻¹ ≤ vmin⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hvmin (hVmin j)
  calc
    _ ≤ (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J *
        giantSignedEdgePositiveApply ν V ρ d source f m :=
      giantSignedEdgeTransposePositiveApply_le ν hν V hvmin hVmin hVmax hρ
        tmax ht d D source f hfn m
    _ ≤ (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J *
        (B * v ^ (∑ j, m.1 j) *
          (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J) :=
      mul_le_mul_of_nonneg_left
        (giantSignedEdgePositiveApply_bound ν hν V hVp hρ hρ1 hv hB hRate hMass
          tmax ht d source f hf m)
        (pow_nonneg (giantSignedEdgeReverseConstant_nonneg _ _ _) _)
    _ = _ := by rw [mul_pow]; ring

end
end ArtinMatthews
