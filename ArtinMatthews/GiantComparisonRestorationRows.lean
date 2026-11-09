module

public import ArtinMatthews.GiantComparisonListRestoration
public import ArtinMatthews.GiantComparisonRowWeights
public import ArtinMatthews.SourceComparisonFreeHitAuxiliary


set_option backward.privateInPublic true
@[expose] public section

/-! On the actual comparison rows the restored error is bounded by
the same two fourth moments as the original source coefficient. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateComparisonRestorationRows_le {x : ℝ}
    (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    (S : Finset (GiantCandidateGroupIndex x)) {k m : ℕ} [NeZero m]
    (CB : GiantCandidatePerformedBig S → Finset (Fin k))
    (aux : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S CB))
    (hV : ∀ g : S, 0 < bandReciprocalMass (giantCandidateGroup x g.val))
    {q : ℝ} (hq : 0 < q) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n)
    {a b B η : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hΨ : ∀ y ∉ Set.Icc a b, Ψ y = 0) (hB : ∀ y, ‖Ψ y‖ ≤ B) :
    let d := giantTwoSidedPatternAuxiliaryProduct aux
    let Y := x*(d:ℝ)
    let U (n : ℕ) := F n*(W n:ℂ)
    let V (n : ℕ) := (χ n*G n)*(W n:ℂ)
    ∀ (T : Finset ℕ), T ⊆ Ioc 0 ⌊b*Y⌋₊ →
      (∀ w ∈ T, ((q⁻¹)^(2*(k*Fintype.card S))+1)*
        giantComparisonSharedBadMass aux w (w+d) ≤ η) →
      (∑ w ∈ T, ‖giantComparisonPositionKernel x Ψ χ F G d w‖*W w*W (w+d)*
          giantComparisonRestorationLoss aux q w (w+d)) ≤
        (B*Real.sqrt b/a)*Y^(-(1/2:ℝ))*
          (sourceComparisonFourthMass ⌊b*Y⌋₊ U)^(1/4:ℝ)*
          (sourceComparisonFourthMass ⌊b*Y+(d:ℝ)⌋₊ V)^(1/4:ℝ)*
          (η+(Fintype.card (Σ g : S, ↥(giantCandidatePerformedPattern S CB g)):ℝ)*
            Real.exp (-(Real.log x)^(39/100:ℝ)/2)) := by
  dsimp only
  intro T hT hshared
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  let Y := x*(d:ℝ)
  let U (n : ℕ) := F n*(W n:ℂ)
  let V (n : ℕ) := (χ n*G n)*(W n:ℂ)
  let v (w : ℕ) := sourceComparisonFreeHitWeight Ψ U V Y d w
  let Q (w : ℕ) := ((q⁻¹)^(2*(k*Fintype.card S))+1)*giantComparisonSharedBadMass aux w (w+d)
  let H (w : ℕ) := GiantComparisonAuxiliaryHits aux w (w+d)
  let E := (B*Real.sqrt b/a)*Y^(-(1/2:ℝ))*(sourceComparisonFourthMass ⌊b*Y⌋₊ U)^(1/4:ℝ)*
    (sourceComparisonFourthMass ⌊b*Y+(d:ℝ)⌋₊ V)^(1/4:ℝ)
  let C := giantCandidatePerformedPattern S CB
  let R := (Fintype.card (Σ g : S, ↥(C g)):ℝ)*Real.exp (-(Real.log x)^(39/100:ℝ)/2)
  have hP (g : S) (p : ℕ) (hp : p ∈ giantCandidateGroup x g.val) : p.Prime :=
    (giantCandidateFullPrimes_range hx hlog (mem_giantCandidateFullPrimes.mpr ⟨g.val,hp⟩)).1
  have hd : 0 < d := prod_pos fun g _ => prod_pos fun i _ => (hP g _ (aux g i).property).pos
  have hY : 0 < Y := mul_pos (zero_lt_one.trans hx) (Nat.cast_pos.mpr hd)
  have hv (w : ℕ) : 0 ≤ v w := sourceComparisonFreeHitWeight_nonneg Ψ U V Y d w
  have hQ (w : ℕ) : 0 ≤ Q w := by
    unfold Q
    apply mul_nonneg (by positivity)
    unfold giantComparisonSharedBadMass
    apply sum_nonneg
    intro c _
    split_ifs
    · exact le_rfl
    · exact giantTwoSidedPatternAuxiliaryMass_nonneg hV c
  have hfull : (∑ w ∈ T, v w) ≤ E := by
    have h := sourceComparison_freeHit_le_of_subset Ψ U V hY ha hb hΨ hB d 1 Nat.one_pos
      (one_dvd d) hT
    simpa [E,v] using h
  have hrows : T.filter H = sourceComparisonAuxiliaryHitRows T aux := by
    ext w
    rw [mem_filter,sourceComparisonAuxiliaryHitRows,mem_sourceComparisonAuxHitRows]
    constructor
    · rintro ⟨hw, g,i,hi⟩
      exact ⟨hw,⟨g,i⟩,mem_univ _,hi⟩
    · rintro ⟨hw,⟨g,i⟩,_,hi⟩
      exact ⟨hw,g,i,hi⟩
  have hhit : (∑ w ∈ T, v w*(if H w then (1:ℝ) else 0)) ≤ E*R := by
    have he : (∑ w ∈ T, v w*(if H w then (1:ℝ) else 0)) = ∑ w ∈ T.filter H, v w := by
      rw [sum_filter]
      apply sum_congr rfl
      intro w _
      by_cases hw : GiantComparisonAuxiliaryHits aux w (w+d) <;> simp [H, hw]
    rw [he,hrows]
    exact sourceComparison_performed_freeHit_le hx hlog S CB aux Ψ U V ha hb hΨ hB T hT
  change (∑ w ∈ T, ‖giantComparisonPositionKernel x Ψ χ F G d w‖*W w*W (w+d)*
      giantComparisonRestorationLoss aux q w (w+d)) ≤ E*(η+R)
  calc
    _ ≤ ∑ w ∈ T, v w*(Q w+(if H w then 1 else 0)) := by
      apply sum_le_sum
      intro w _
      apply mul_le_mul_of_nonneg_right (giantComparisonPositionKernel_weight_norm_le x Ψ χ F G W hW d w)
      exact add_nonneg (hQ w) (by split_ifs <;> norm_num)
    _ = (∑ w ∈ T, v w*Q w)+(∑ w ∈ T, v w*(if H w then 1 else 0)) := by
      simp only [mul_add, sum_add_distrib]
    _ ≤ η*(∑ w ∈ T, v w)+E*R := by
      apply add_le_add _ hhit
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro w hw
      rw [mul_comm η]
      exact mul_le_mul_of_nonneg_left (hshared w hw) (hv w)
    _ ≤ η*E+E*R := add_le_add (mul_le_mul_of_nonneg_left hfull hη) le_rfl
    _ = _ := by ring

end
end ArtinMatthews
