module

public import ArtinMatthews.GiantSignedEdgeFreshMass


set_option backward.privateInPublic true
@[expose] public section

/-! The positive edge row retains every store and promotion multiplicity.
Dropping the original promotion ban gives an absolute majorant. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

def giantSignedEdgePositiveApply (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (m : GiantSignedMemory P) : ℝ :=
  ∑ S : (j : J) → Finset (Fin (t j)),
    ∑ T : (j : J) → Finset (Fin (t j)),
      ∑ target : GiantSignedPrimeTuple P t,
        (∏ j, (V j)⁻¹ ^ (T j).card) * giantSignedFreshPrimeRealMass ν T target *
          ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
            if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
              giantSignedPendingDamping ρ m *
                giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) *
                f target (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
            else 0

theorem giantSignedEdgePositiveApply_nonneg (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out) (m : GiantSignedMemory P) :
    0 ≤ giantSignedEdgePositiveApply ν V ρ d source f m := by
  unfold giantSignedEdgePositiveApply
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro T _
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

theorem giantSignedEdgeApply_norm_le_positive (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 < V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (m : GiantSignedMemory P) :
    ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source f m‖ ≤
      giantSignedEdgePositiveApply ν V ρ d source (fun target out => ‖f target out‖) m := by
  unfold giantSignedEdgeApply giantSignedEdgePositiveApply
  apply norm_sum_le_of_le
  intro S _
  apply norm_sum_le_of_le
  intro T _
  apply norm_sum_le_of_le
  intro target _
  rw [norm_mul, norm_mul, giantSignedPromotionCharge_norm V hV,
    giantSignedFreshPrimeMass_norm ν hν]
  apply mul_le_mul_of_nonneg_left
  · apply norm_sum_le_of_le
    intro e _
    have hIn := giantSignedPendingDamping_nonneg hρ m
    have hOut := giantSignedPendingDamping_nonneg hρ
      (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
    by_cases h : GiantSignedEdgeHits d m target ⟨S, T, e⟩ ∧
        GiantSignedEdgePromotionBan D T target
    · simp only [ite_eq_left h, ite_eq_left h.1, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hIn, Real.norm_of_nonneg hOut, le_refl]
    · simp only [ite_eq_right h, norm_zero]
      split_ifs
      · exact mul_nonneg (mul_nonneg hIn hOut) (norm_nonneg _)
      · exact le_rfl
  · exact mul_nonneg
      (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _))
      (giantSignedFreshPrimeRealMass_nonneg ν hν T target)

end
end ArtinMatthews
