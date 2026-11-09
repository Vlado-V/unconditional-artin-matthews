module

public import ArtinMatthews.MarkedMajorMellinLocalMeanScaled


set_option backward.privateInPublic true
@[expose] public section

/-! Enlarged-scale weighted means and tails for the actual conjugated endpoint. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

theorem marked_major_label_conjugate_weighted_scaled_mean (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
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
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation c scale : ℝ), 1 ≤ scale →
      ∀ n : ℕ, 2 ≤ n →
      (∫ t : ℝ,markedMajorFourierWeight (scale*(H*U)) n (t-c)*
        ‖markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β t‖^2) ≤
          C*scale*L^(2*D+5) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_weighted_scaled_mean σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨C,hC,?_⟩
  filter_upwards [hmean] with L hL
  intro J _ bands hbands hdis hV Y θ H u v U l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation c scale hscale n hn
  simpa only [markedMajorLabelConjugateEndpoint_eq] using
    hL bands hbands hdis hV Y θ H u v U l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
      k q χb χ (-modulation) c scale hscale n hn

theorem marked_major_label_conjugate_weighted_scaled_tail (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
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
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation c scale : ℝ), 1 ≤ scale →
      ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
      (∫ t : ℝ in {t | R ≤ |t-c|},markedMajorFourierWeight (scale*(H*U)) (n+2) (t-c)*
        ‖markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β t‖^2) ≤
          ((1+R/(scale*(H*U)))^n)⁻¹*(C*scale*L^(2*D+5)) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_weighted_scaled_tail σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨C,hC,?_⟩
  filter_upwards [hmean] with L hL
  intro J _ bands hbands hdis hV Y θ H u v U l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation c scale hscale n R hR
  simpa only [markedMajorLabelConjugateEndpoint_eq] using
    hL bands hbands hdis hV Y θ H u v U l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
      k q χb χ (-modulation) c scale hscale n R hR

end ArtinMatthews
