module

public import ArtinMatthews.MarkedMajorMellinLocalMeanTail
public import ArtinMatthews.MarkedMajorLabelLocalMean
public import ArtinMatthews.MarkedMajorLabelBounded


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine weighted coarse means for the actual major-arc label endpoint.
Every local-mean, continuity, and boundedness input is discharged. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

theorem marked_major_label_weighted_mean (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y,‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic B) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J]
      (bands : J → Finset ℕ),
      (∀ j p,p ∈ bands j → p.Prime) →
      Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      (∀ j,0 < bandReciprocalMass (bands j)) →
      ∀ (Y θ H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → 0 < H → 0 < U → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      H ≤ u → v ≤ 2*H → 1 ≤ Real.log u → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation c : ℝ),
      ∀ n : ℕ, 2 ≤ n →
      (∫ t : ℝ,markedMajorFourierWeight (H*U) n (t-c)*
        ‖markedMajorLabelEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β t‖^2) ≤
          C*L^(2*D+5) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_local_mean σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨markedMajorLocalMeanConstant*(3*C/2),mul_pos markedMajorLocalMeanConstant_pos (by positivity),?_⟩
  filter_upwards [hmean,eventually_ge_atTop (1:ℝ)] with L hL hLone
  intro J _ bands hbands hdis hV Y θ H u v U l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation c
  let W : ℝ := Real.exp (L^(6/25:ℝ))
  let Q := markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β
  have hQc : Continuous Q := markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W modulation H u v U l r β
  obtain ⟨K,hK⟩ := markedMajorLabelEndpoint_bounded bands cutoff χb θ Y χ W modulation H u v U l r β
  have hlocal (z : ℝ) : (∫ t in Set.Icc z (z+H*U), ‖Q t‖^2) ≤ (3*C/2)*L^(2*D+5) :=
    hL bands hbands hdis hV Y θ H u v U z l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
      k q χb χ modulation
  have hM : 0 ≤ (3*C/2)*L^(2*D+5) := by positivity
  intro n hn
  have h := markedMajorLocalMean_weighted_higher Q hQc K hK (mul_pos hH hU) hM hlocal c hn
  simpa only [Q,W,mul_assoc] using h

theorem marked_major_label_weighted_tail (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y,‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic B) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J]
      (bands : J → Finset ℕ),
      (∀ j p,p ∈ bands j → p.Prime) →
      Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      (∀ j,0 < bandReciprocalMass (bands j)) →
      ∀ (Y θ H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → 0 < H → 0 < U → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      H ≤ u → v ≤ 2*H → 1 ≤ Real.log u → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation c : ℝ),
      ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
      (∫ t : ℝ in {t | R ≤ |t-c|},markedMajorFourierWeight (H*U) (n+2) (t-c)*
        ‖markedMajorLabelEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β t‖^2) ≤
          ((1+R/(H*U))^n)⁻¹*(C*L^(2*D+5)) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_local_mean σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨markedMajorLocalMeanConstant*(3*C/2),mul_pos markedMajorLocalMeanConstant_pos (by positivity),?_⟩
  filter_upwards [hmean,eventually_ge_atTop (1:ℝ)] with L hL hLone
  intro J _ bands hbands hdis hV Y θ H u v U l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation c
  let W : ℝ := Real.exp (L^(6/25:ℝ))
  let Q := markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β
  have hQc : Continuous Q := markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W modulation H u v U l r β
  obtain ⟨K,hK⟩ := markedMajorLabelEndpoint_bounded bands cutoff χb θ Y χ W modulation H u v U l r β
  have hlocal (z : ℝ) : (∫ t in Set.Icc z (z+H*U), ‖Q t‖^2) ≤ (3*C/2)*L^(2*D+5) :=
    hL bands hbands hdis hV Y θ H u v U z l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
      k q χb χ modulation
  have hM : 0 ≤ (3*C/2)*L^(2*D+5) := by positivity
  intro n R hR
  have h := markedMajorLocalMean_weighted_tail Q hQc K hK (mul_pos hH hU) hM hR hlocal c n
  simpa only [Q,W,mul_assoc] using h

end ArtinMatthews
