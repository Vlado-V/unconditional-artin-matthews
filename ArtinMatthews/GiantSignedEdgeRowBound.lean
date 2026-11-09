module

public import ArtinMatthews.GiantSignedEdgeSectorBound
public import ArtinMatthews.GiantSignedEdgeSlotBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform absolute bounds for the literal unrestricted store/promote
row. The constant depends on free-slot count and leaves copied slots out. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

theorem giantSignedEdgePositiveApply_bound (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 < V j)
    {ρ v B rateMax massMax : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hv : 1 ≤ v) (hB : 0 ≤ B)
    (hRate : ∀ j, (V j)⁻¹ ≤ rateMax) (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax)
    (d : ℤ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, f target out ≤ B * v ^ (∑ j, out.1 j))
    (m : GiantSignedMemory P) :
    giantSignedEdgePositiveApply ν V ρ d source f m ≤
      B * v ^ (∑ j, m.1 j) *
        (giantSignedEdgeUniformConstant ρ v rateMax massMax tmax) ^ Fintype.card J := by
  classical
  have hsector (S T : (j : J) → Finset (Fin (t j))) :
      (∑ target : GiantSignedPrimeTuple P t,
        (∏ j, (V j)⁻¹ ^ (T j).card) * giantSignedFreshPrimeRealMass ν T target *
          ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
            if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
              giantSignedPendingDamping ρ m *
                giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) *
                f target (giantSignedEdgeTarget d m source ⟨S, T, e⟩) else 0) ≤
        (∏ j, (V j)⁻¹ ^ (T j).card) *
          (B * v ^ (∑ j, m.1 j) * (∏ j, v ^ (S j).card) *
            (∏ j, (∑ p : P j, ν j p) ^ ((T j)ᶜ).card) *
            (∏ j, ((T j).card.factorial : ℝ) / (1 - ρ) ^ ((T j).card + 1))) := by
    calc
      _ = (∏ j, (V j)⁻¹ ^ (T j).card) *
          (∑ target : GiantSignedPrimeTuple P t,
            giantSignedFreshPrimeRealMass ν T target *
              ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
                if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
                  giantSignedPendingDamping ρ m *
                    giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) *
                    f target (giantSignedEdgeTarget d m source ⟨S, T, e⟩) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (giantSignedEdgeSector_bound ν hν hρ hρ1 hv hB d source f hf m S T)
        (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _))
  calc
    _ ≤ ∑ S : (j : J) → Finset (Fin (t j)),
        ∑ T : (j : J) → Finset (Fin (t j)),
          (∏ j, (V j)⁻¹ ^ (T j).card) *
            (B * v ^ (∑ j, m.1 j) * (∏ j, v ^ (S j).card) *
              (∏ j, (∑ p : P j, ν j p) ^ ((T j)ᶜ).card) *
              (∏ j, ((T j).card.factorial : ℝ) / (1 - ρ) ^ ((T j).card + 1))) :=
      Finset.sum_le_sum (fun S _ => Finset.sum_le_sum (fun T _ => hsector S T))
    _ = B * v ^ (∑ j, m.1 j) *
        (∑ S : (j : J) → Finset (Fin (t j)),
          ∑ T : (j : J) → Finset (Fin (t j)),
            ∏ j, v ^ (S j).card * (V j)⁻¹ ^ (T j).card *
              (∑ p : P j, ν j p) ^ ((T j)ᶜ).card *
              (((T j).card.factorial : ℝ) / (1 - ρ) ^ ((T j).card + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      simp only [Finset.prod_mul_distrib]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (giantSignedEdgeSlotBudget t tmax ht (fun j => (V j)⁻¹)
        (fun j => ∑ p : P j, ν j p) rateMax massMax ρ v
        (fun j => inv_nonneg.mpr (hV j).le)
        (fun _ => Finset.sum_nonneg (fun _ _ => hν _ _)) hRate hMass hρ hρ1 hv)
      (mul_nonneg hB (pow_nonneg (le_trans zero_le_one hv) _))

theorem giantSignedEdgeApply_row_bound (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) {vmin massMax ρ v B : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ j, vmin ≤ V j)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hB : 0 ≤ B)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) (d : ℤ) (D : ℕ)
    (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (hf : ∀ target out, ‖f target out‖ ≤ B * v ^ (∑ j, out.1 j))
    (m : GiantSignedMemory P) :
    ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source f m‖ ≤
      B * v ^ (∑ j, m.1 j) *
        (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J := by
  have hVp (j : J) : 0 < V j := lt_of_lt_of_le hvmin (hV j)
  have hRate (j : J) : (V j)⁻¹ ≤ vmin⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hvmin (hV j)
  exact (giantSignedEdgeApply_norm_le_positive ν hν V hVp hρ d D source f m).trans
    (giantSignedEdgePositiveApply_bound ν hν V hVp hρ hρ1 hv hB hRate hMass
      tmax ht d source (fun target out => ‖f target out‖) hf m)

theorem giantSignedPatternFreeRow_bound (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) {vmin massMax ρ v B : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ j, vmin ≤ V j)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hB : 0 ≤ B)
    {kCopy ell budget : ℕ} (C : J → Finset (Fin kCopy))
    (hC : ∀ j, (C j).card ≤ budget) (d : ℤ) (D : ℕ)
    (source : (j : J) → Fin (kCopy + ell) → P j)
    (f : GiantSignedPrimeTuple P (fun j => ell + (C j).card) → GiantSignedMemory P → ℂ)
    (hf : ∀ target out, ‖f target out‖ ≤ B * v ^ (∑ j, out.1 j))
    (m : GiantSignedMemory P) :
    ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D
        (giantSignedPatternFreeLabels C source) f m‖ ≤
      B * v ^ (∑ j, m.1 j) *
        (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell + budget)) ^
          Fintype.card J :=
  giantSignedEdgeApply_row_bound ν hν V hvmin hV hMass hρ hρ1 hv hB
    (ell + budget) (fun j => Nat.add_le_add_left (hC j) ell) d D
    (giantSignedPatternFreeLabels C source) f hf m

end
end ArtinMatthews
