module

public import ArtinMatthews.MarkedMajorLabelMean


set_option backward.privateInPublic true
@[expose] public section

/-! The actual conjugated endpoint and its uniform translated coarse mean. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

noncomputable def markedMajorLabelConjugateEndpoint {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) (t : ℝ) : ℂ :=
  markedMajorLabelPolynomial bands cutoff χb θ Y t*
    markedMajorConjugateCenteredSum χ W modulation t H u v*markedDyadicPolynomial l r U β t

theorem markedMajorLabelConjugateEndpoint_eq {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) (t : ℝ) :
    markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t =
      markedMajorLabelEndpoint bands cutoff χb θ Y χ W (-modulation) H u v U l r β t := by
  simp only [markedMajorLabelConjugateEndpoint,markedMajorLabelEndpoint,marked_conjugate_centered_sum_eq]

theorem marked_major_label_conjugate_translated_mean (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y,‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic B) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J]
      (bands : J → Finset ℕ),
      (∀ j p,p ∈ bands j → p.Prime) →
      Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      (∀ j,0 < bandReciprocalMass (bands j)) →
      ∀ (Y θ H u v U T ξ : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → 0 < H → 0 < U → 0 < T → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      H ≤ u → v ≤ 2*H → 1 ≤ Real.log u → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation : ℝ),
      (∫ t in Set.Icc (-T) T,
        ‖markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β (t+ξ)‖^2) ≤
          C*L^(2*D+5)*(1+T/(H*U)) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_translated_mean σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨C,hC,?_⟩
  filter_upwards [hmean] with L hL
  intro J _ bands hbands hdis hV Y θ H u v U T ξ l r β hY hH hU hT hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation
  simp only [markedMajorLabelConjugateEndpoint_eq]
  exact hL bands hbands hdis hV Y θ H u v U T ξ l r β hY hH hU hT hX hXupper hHu hv hlog hl hr hβ
    k q χb χ (-modulation)

end ArtinMatthews
