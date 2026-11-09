module

public import ArtinMatthews.MarkedMemoryGoodBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! A finite weighted adjoint inherits the energy bound of the original
operator on its invariant domain. Zero mass atoms require no division. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedWeightedPairing_self {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (f : Ω → ℂ) :
    (∑ s, (μ s : ℂ)*star (f s)*f s) = ((∑ s, μ s*‖f s‖^2 : ℝ) : ℂ) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    mul_assoc, Complex.star_def, Complex.conj_mul']

theorem markedWeightedAdjoint_energy_le {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s, 0 ≤ μ s) (S : (Ω → ℂ) → Prop)
    (T U : (Ω → ℂ) → Ω → ℂ)
    (hU : ∀ f, S f → S (U f))
    (hpair : ∀ f, S f → ∀ g, S g →
      (∑ s, (μ s : ℂ)*star (g s)*T f s) =
        ∑ s, (μ s : ℂ)*star (U g s)*f s)
    (C : ℝ) (hT : ∀ f, S f →
      (∑ s, μ s*‖T f s‖^2) ≤ C^2*∑ s, μ s*‖f s‖^2)
    (g : Ω → ℂ) (hg : S g) :
    (∑ s, μ s*‖U g s‖^2) ≤ C^2*∑ s, μ s*‖g s‖^2 := by
  let E : ℝ := ∑ s, μ s*‖U g s‖^2
  let D : ℝ := ∑ s, μ s*‖g s‖^2
  have hE₀ : 0 ≤ E := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  have hD₀ : 0 ≤ D := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  have hself : (∑ s, (μ s : ℂ)*star (g s)*T (U g) s) = (E : ℂ) :=
    (hpair (U g) (hU g hg) g hg).trans (markedWeightedPairing_self μ (U g))
  have hcs := markedWeightedBoundary_cauchy μ hμ g (T (U g))
  rw [hself] at hcs
  simp only [Complex.norm_real, Real.norm_of_nonneg hE₀] at hcs
  have hEE : E^2 ≤ D*(C^2*E) :=
    hcs.trans (mul_le_mul_of_nonneg_left (hT (U g) (hU g hg)) hD₀)
  by_cases hE : E = 0
  · change E ≤ C^2*D
    rw [hE]
    exact mul_nonneg (sq_nonneg C) hD₀
  · have hEp : 0 < E := lt_of_le_of_ne hE₀ (Ne.symm hE)
    apply (mul_le_mul_iff_of_pos_right hEp).mp
    calc
      E*E = E^2 := by ring
      _ ≤ D*(C^2*E) := hEE
      _ = (C^2*D)*E := by ring

end ArtinMatthews
