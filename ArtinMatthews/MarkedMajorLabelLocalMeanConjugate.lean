module

public import ArtinMatthews.MarkedMajorLabelLocalMean


set_option backward.privateInPublic true
@[expose] public section

/-! The length-HU local mean for the conjugated normalized endpoint. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

theorem marked_major_label_conjugate_local_mean (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y,‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic B) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J]
      (bands : J → Finset ℕ),
      (∀ j p,p ∈ bands j → p.Prime) →
      Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      (∀ j,0 < bandReciprocalMass (bands j)) →
      ∀ (Y θ H u v U z : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → 0 < H → 0 < U → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      H ≤ u → v ≤ 2*H → 1 ≤ Real.log u → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation : ℝ),
      (∫ t in Set.Icc z (z+H*U),
        ‖markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β t‖^2) ≤
          (3*C/2)*L^(2*D+5) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_conjugate_translated_mean σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨C,hC,?_⟩
  filter_upwards [hmean] with L hL
  intro J _ bands hbands hdis hV Y θ H u v U z l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation
  have h := hL bands hbands hdis hV Y θ H u v U (H*U/2) (z+H*U/2) l r β
    hY hH hU (by positivity) hX hXupper hHu hv hlog hl hr hβ k q χb χ modulation
  rw [markedMajor_local_integral_eq_translated _ z (H*U) (mul_pos hH hU).le]
  convert h using 1
  have hx : H*U ≠ 0 := (mul_pos hH hU).ne'
  field_simp
  ring

end ArtinMatthews
