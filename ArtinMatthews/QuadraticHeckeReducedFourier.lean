module

public import ArtinMatthews.ProbeSexticGaussPhase
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped Classical BigOperators
noncomputable section
variable {R : Type} [CommRing R] [Fintype R]

/-- The exact reduced Fourier coefficients of a primitive finite-ring character. -/
def primitiveReducedFourierWeight (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (d : Rˣ) : ℂ :=
  χ⁻¹ d.val / gaussSum χ⁻¹ ψ

theorem primitiveReducedFourierExpansion (χ : MulChar R ℂ) (hχ : IsPrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (x : R) :
    letI : Fintype Rˣ := Fintype.ofFinite _
    χ x = ∑ d : Rˣ, primitiveReducedFourierWeight χ ψ d * ψ (x * d.val) := by
  let := (Fintype.ofFinite Rˣ)
  let f (d : R) := χ⁻¹ d * ψ (x * d)
  let i : Rˣ ↪ R := ⟨Units.val, Units.val_injective⟩
  have hsum : (∑ d : R, f d) = ∑ d : Rˣ, f (i d) := by
    rw [← Finset.sum_map]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro d _ hd
    have hnu : ¬ IsUnit d := by
      rintro ⟨u, hu⟩
      exact hd (Finset.mem_map.mpr ⟨u, Finset.mem_univ _, hu⟩)
    exact mul_eq_zero_of_left (MulChar.map_nonunit _ hnu) _
  calc
    χ x = (∑ d : R, f d) / gaussSum χ⁻¹ ψ :=
      primitive_character_expansion χ hχ ψ hψ x
    _ = (∑ d : Rˣ, f (i d)) / gaussSum χ⁻¹ ψ := by rw [hsum]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d _
      unfold f primitiveReducedFourierWeight
      change (χ⁻¹ d.val * ψ (x * d.val)) / _ = _
      ring

theorem primitiveReducedFourierWeight_mass (χ : MulChar R ℂ) (hχ : IsPrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    letI : Fintype Rˣ := Fintype.ofFinite _
    (∑ d : Rˣ, ‖primitiveReducedFourierWeight χ ψ d‖ ^ 2) ≤ 1 := by
  let := (Fintype.ofFinite Rˣ)
  have hq : 0 < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card Rˣ : ℝ) ≤ Fintype.card R := by
    exact_mod_cast Fintype.card_le_of_injective (fun d : Rˣ => d.val) Units.val_injective
  have hnorm (d : Rˣ) : ‖primitiveReducedFourierWeight χ ψ d‖ ^ 2 =
      (Fintype.card R : ℝ)⁻¹ := by
    unfold primitiveReducedFourierWeight
    rw [norm_div, div_pow, primitive_gaussSum_norm_sq χ⁻¹ hχ.inv ψ hψ]
    have hd : ‖χ⁻¹ d.val‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity ((χ⁻¹).apply_mem_rootsOfUnity d)
    rw [hd, one_pow, one_div]
  calc
    _ = (Fintype.card Rˣ : ℝ) * (Fintype.card R : ℝ)⁻¹ := by simp [hnorm]
    _ ≤ (Fintype.card R : ℝ) * (Fintype.card R : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hq.le)
    _ = 1 := mul_inv_cancel₀ hq.ne'

end
end ArtinMatthews.VaryingKummerAnalytic
