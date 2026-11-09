module

public import ArtinMatthews.GiantSignedEdgePositive
public import ArtinMatthews.GiantSignedPromotionCount
public import ArtinMatthews.GiantSignedPromotionDamping


set_option backward.privateInPublic true
@[expose] public section

/-! The actual fixed store/promotion sector has a degree-independent
bound. Translated old zero residues provide the ordered retrieval count. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

theorem giantSignedEdgeSector_bound (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) {ρ v B : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hB : 0 ≤ B)
    (d : ℤ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, f target out ≤ B * v ^ (∑ j, out.1 j))
    (m : GiantSignedMemory P) (S T : (j : J) → Finset (Fin (t j))) :
    (∑ target : GiantSignedPrimeTuple P t,
      giantSignedFreshPrimeRealMass ν T target *
        ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
          if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
            giantSignedPendingDamping ρ m *
              giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) *
              f target (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
          else 0) ≤
      B * v ^ (∑ j, m.1 j) * (∏ j, v ^ (S j).card) *
        (∏ j, (∑ p : P j, ν j p) ^ ((T j)ᶜ).card) *
        ∏ j, ((T j).card.factorial : ℝ) / (1 - ρ) ^ ((T j).card + 1) := by
  classical
  let E := giantSignedEdgeHitIndices d m
  let G := v ^ (∑ j, m.1 j) * ∏ j, v ^ (S j).card
  let H := ∏ j, ρ ^ ((E j).card - (T j).card)
  let W := ∏ j, (∑ p : P j, ν j p) ^ ((T j)ᶜ).card
  let K := (B * G) * H
  have hG : 0 ≤ G := mul_nonneg (pow_nonneg (le_trans zero_le_one hv) _)
    (Finset.prod_nonneg (fun _ _ => pow_nonneg (le_trans zero_le_one hv) _))
  have hH : 0 ≤ H := Finset.prod_nonneg (fun _ _ => pow_nonneg hρ _)
  have hW : 0 ≤ W := Finset.prod_nonneg
    (fun _ _ => pow_nonneg (Finset.sum_nonneg (fun _ _ => hν _ _)) _)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hB hG) hH
  have hterm (target : GiantSignedPrimeTuple P t)
      (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
      (if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
        giantSignedPendingDamping ρ m *
          giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) *
          f target (giantSignedEdgeTarget d m source ⟨S, T, e⟩) else 0) ≤
        (if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then (1 : ℝ) else 0) * K := by
    by_cases hh : GiantSignedEdgeHits d m target ⟨S, T, e⟩
    · simp only [ite_eq_left hh, one_mul]
      have he := ((giantSignedEdgeHits_indices_labels d m target S T e).mp hh).1
      have hout := giantSignedEdgeTarget_damping_le hρ hρ1.le d m source S T e he
      have hin := giantSignedPendingDamping_le_one hρ hρ1.le m
      have hd : giantSignedPendingDamping ρ m *
          giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) ≤ H := by
        simpa only [one_mul] using mul_le_mul hin hout
          (giantSignedPendingDamping_nonneg hρ _) zero_le_one
      have hfg : f target (giantSignedEdgeTarget d m source ⟨S, T, e⟩) ≤ B * G :=
        (hf target _).trans (mul_le_mul_of_nonneg_left
          (giantSignedEdgeTarget_degree_gauge hv d m source S T e) hB)
      calc
        _ ≤ (giantSignedPendingDamping ρ m *
            giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩)) *
            (B * G) := mul_le_mul_of_nonneg_left hfg
              (mul_nonneg (giantSignedPendingDamping_nonneg hρ _)
                (giantSignedPendingDamping_nonneg hρ _))
        _ ≤ H * (B * G) := mul_le_mul_of_nonneg_right hd (mul_nonneg hB hG)
        _ = K := by dsimp [K]; ring
    · simp only [ite_eq_right hh, zero_mul, le_refl]
  have hsum :
      (∑ target : GiantSignedPrimeTuple P t,
        giantSignedFreshPrimeRealMass ν T target *
          ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
            (if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then (1 : ℝ) else 0) * K) =
        ((∏ j, ((E j).card.descFactorial (T j).card : ℝ)) * W) * K := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    simp_rw [giantSignedEdgeTargetMass_eq]
    rw [← Finset.sum_mul, giantSignedPromotionFamilyIntoFinsets_sum]
  have hprod : (∏ j, ((E j).card.descFactorial (T j).card : ℝ)) * H ≤
      ∏ j, ((T j).card.factorial : ℝ) / (1 - ρ) ^ ((T j).card + 1) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ _))
      (fun j _ => giantSignedPromotionDamping_bound (T j).card (E j).card hρ hρ1)
  calc
    _ ≤ ∑ target : GiantSignedPrimeTuple P t,
        giantSignedFreshPrimeRealMass ν T target *
          ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
            (if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then (1 : ℝ) else 0) * K := by
      apply Finset.sum_le_sum
      intro target _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e _ => hterm target e))
        (giantSignedFreshPrimeRealMass_nonneg ν hν T target)
    _ = (B * G) * W * ((∏ j, ((E j).card.descFactorial (T j).card : ℝ)) * H) := by
      rw [hsum]
      dsimp [K]
      ring
    _ ≤ (B * G) * W *
        (∏ j, ((T j).card.factorial : ℝ) / (1 - ρ) ^ ((T j).card + 1)) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg (mul_nonneg hB hG) hW)
    _ = _ := by dsimp [G, W]; ring

end
end ArtinMatthews
