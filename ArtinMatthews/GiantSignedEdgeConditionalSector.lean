module

public import ArtinMatthews.GiantSignedEdgeMoveExpansion
public import ArtinMatthews.GiantSignedEdgeFreshMass


set_option backward.privateInPublic true
@[expose] public section

/-! After the actual ordered retrieval choice is fixed, its coefficient
depends on free target labels only through their fresh product law.
The original promotion tests and both pending dampings are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ} {t : B → ℕ}

theorem giantSignedEdgeConditionalSector_le
    (ν μ : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (hμ : ∀ g p, 0 ≤ μ g p)
    (V : B → ℝ) (ρ : ℝ) (d : ℤ) (D : ℕ)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (c : GiantSignedEdgeChoice t m.1)
    (Gate : GiantSignedPrimeTuple P (fun g => ((c.2.1 g)ᶜ).card) → Prop)
    (F : ℝ)
    (hGate :
      (∑ fresh : GiantSignedPrimeTuple P (fun g => ((c.2.1 g)ᶜ).card),
        if Gate fresh then ∏ g, ∏ i, ν g (fresh g i) else 0) ≤
        F * (∏ g, (∑ p : P g, μ g p)^((c.2.1 g)ᶜ).card)) :
    (∑ target : GiantSignedPrimeTuple P t,
      if Gate ((giantSignedEdgeTargetLabelEquiv c.2.1) target).2 then
        ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ d D source target m c‖
      else 0) ≤
      F * ∑ target : GiantSignedPrimeTuple P t,
        ‖giantSignedEdgeMoveCoefficient (fun g p => (μ g p : ℂ)) V ρ d D source target m c‖ := by
  classical
  obtain ⟨S,T,e⟩ := c
  let Promoted := GiantSignedPrimeTuple P (fun g => (T g).card)
  let Fresh := GiantSignedPrimeTuple P (fun g => ((T g)ᶜ).card)
  let E := giantSignedEdgeTargetLabelEquiv (P := P) T
  let cond (u : Promoted) :=
    ((∀ g i, e g i ∈ giantSignedEdgeHitIndices d m g) ∧
      (∀ g, u g = giantSignedEdgePromotionPrimes m e g)) ∧
        (∀ g i, ¬ (u g i).val ∣ D)
  let R (u : Promoted) : ℝ := ‖giantSignedPromotionCharge V (fun g => (T g).card)‖ *
    ‖if cond u then (giantSignedPendingDamping ρ m : ℂ) *
      (giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S,T,e⟩) : ℂ) else 0‖
  have hR (u : Promoted) : 0 ≤ R u := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcoeff (law : ∀ g, P g → ℝ) (hlaw : ∀ g p, 0 ≤ law g p)
      (u : Promoted) (f : Fresh) :
      ‖giantSignedEdgeMoveCoefficient (fun g p => (law g p : ℂ)) V ρ d D source
          (E.symm (u,f)) m ⟨S,T,e⟩‖ =
        R u * ∏ g, ∏ i, law g (f g i) := by
    have he := E.apply_symm_apply (u,f)
    have hp (g : B) :
        giantSignedEdgeSelected (T g) (E.symm (u,f) g) = u g :=
      congrFun (congrArg Prod.fst he) g
    have hf : giantSignedFreshPrimeRealMass law T (E.symm (u,f)) =
        ∏ g, ∏ i, law g (f g i) :=
      congrArg (fun f : Fresh => ∏ g, ∏ i, law g (f g i)) (congrArg Prod.snd he)
    have hc : GiantSignedEdgeHits d m (E.symm (u,f)) ⟨S,T,e⟩ ∧
        GiantSignedEdgePromotionBan D T (E.symm (u,f)) ↔ cond u := by
      rw [giantSignedEdgeHits_indices_labels]
      simp only [GiantSignedEdgePromotionBan, cond, hp]
    unfold giantSignedEdgeMoveCoefficient
    rw [norm_mul, norm_mul, giantSignedFreshPrimeMass_norm law hlaw, hf]
    simp only [R, hc]
    ring
  have hleft :
      (∑ target : GiantSignedPrimeTuple P t, if Gate (E target).2 then
          ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ d D source target m ⟨S,T,e⟩‖
        else 0) =
        (∑ u : Promoted, R u) *
          (∑ f : Fresh, if Gate f then ∏ g, ∏ i, ν g (f g i) else 0) := by
    rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun f _ => by
      rw [E.apply_symm_apply, hcoeff ν hν]
      by_cases hf : Gate f <;> simp only [hf, ite_true, ite_false, mul_zero])
  have hright :
      (∑ target : GiantSignedPrimeTuple P t,
        ‖giantSignedEdgeMoveCoefficient (fun g p => (μ g p : ℂ)) V ρ d D source target m ⟨S,T,e⟩‖) =
        (∑ u : Promoted, R u) * (∏ g, (∑ p : P g, μ g p)^((T g)ᶜ).card) := by
    rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [← giantSignedPrimeTuple_mass_sum μ (fun g => ((T g)ᶜ).card), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun f _ => hcoeff μ hμ u f)
  change (∑ target : GiantSignedPrimeTuple P t, if Gate (E target).2 then _ else 0) ≤ _
  rw [hleft, hright]
  exact (mul_le_mul_of_nonneg_left hGate (Finset.sum_nonneg (fun u _ => hR u))).trans_eq (by ring)

end
end ArtinMatthews
