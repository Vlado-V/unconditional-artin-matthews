module

public import OAI.NumberTheory.DirichletL.FiniteFourier
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.MulChar.Duality
public import OAI.NumberTheory.DirichletL.Mellin.LogProfiles


set_option backward.privateInPublic true
@[expose] public section

/-! Finite conductor-character energy reduction to additive residue energy.
This is the exact finite-ring step in the conductor large sieve; it does not
assume an additive large-sieve or an analytic estimate. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped Classical BigOperators
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

theorem sum_mulChar_eq_units (χ : MulChar R ℂ) (f : R → ℂ) :
    (∑ x : R, χ x * f x) = ∑ u : Rˣ, χ (u : R) * f u := by
  symm
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro x hx
    rw [χ.map_nonunit (fun hu => hx hu), zero_mul]
  · intro u
    rfl

theorem primitive_character_sum_gauss {ι : Type*} (I : Finset ι)
    (n : ι → R) (a : ι → ℂ) (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ⁻¹ ψ * (∑ i ∈ I, a i * χ (n i)) =
      ∑ u : Rˣ, χ⁻¹ (u : R) * ∑ i ∈ I, a i * ψ (n i * u) := by
  calc
    _ = ∑ i ∈ I, a i * (χ (n i) * gaussSum χ⁻¹ ψ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i ∈ I, a i * ∑ u : R, χ⁻¹ u * ψ (n i * u) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(eq_div_iff (primitive_gaussSum_ne_zero χ⁻¹ hχ.inv ψ hψ)).mp
        (primitive_character_expansion χ hχ ψ hψ (n i))]
    _ = ∑ u : R, χ⁻¹ u * ∑ i ∈ I, a i * ψ (n i * u) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := sum_mulChar_eq_units χ⁻¹ _

theorem primitive_character_family_energy {ι : Type*} (I : Finset ι)
    (n : ι → R) (a : ι → ℂ) (S : Finset (MulChar R ℂ))
    (hS : ∀ χ ∈ S, IsPrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    (Fintype.card R : ℝ) * (∑ χ ∈ S, ‖∑ i ∈ I, a i * χ (n i)‖ ^ 2) ≤
      (Fintype.card Rˣ : ℝ) *
        ∑ u : Rˣ, ‖∑ i ∈ I, a i * ψ (n i * u)‖ ^ 2 := by
  let T : Rˣ → ℂ := fun u => ∑ i ∈ I, a i * ψ (n i * u)
  calc
    _ = ∑ χ ∈ S, ‖∑ u : Rˣ, T u * χ⁻¹ (u : R)‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [← primitive_gaussSum_norm_sq χ⁻¹ (hS χ hχ).inv ψ hψ,
        ← mul_pow, ← norm_mul, primitive_character_sum_gauss I n a χ (hS χ hχ) ψ hψ]
      simp only [T, mul_comm]
    _ ≤ ∑ χ : MulChar R ℂ, ‖∑ u : Rˣ, T u * χ⁻¹ (u : R)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun χ _ _ => sq_nonneg _)
    _ = ∑ χ : MulChar R ℂ, ‖∑ u : Rˣ, T u * χ (u : R)‖ ^ 2 :=
      Fintype.sum_bijective Inv.inv inv_involutive.bijective _ _ (fun _ => rfl)
    _ = _ := OAI.FiniteRingSieve.complete_character_plancherel T

theorem primitive_character_family_le_additive_energy {ι : Type*} (I : Finset ι)
    (n : ι → R) (a : ι → ℂ) (S : Finset (MulChar R ℂ))
    (hS : ∀ χ ∈ S, IsPrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    (∑ χ ∈ S, ‖∑ i ∈ I, a i * χ (n i)‖ ^ 2) ≤
      ∑ u : Rˣ, ‖∑ i ∈ I, a i * ψ (n i * u)‖ ^ 2 := by
  have he := primitive_character_family_energy I n a S hS ψ hψ
  have hc : (Fintype.card Rˣ : ℝ) ≤ (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective Units.val Units.val_injective
  have hcard : 0 < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_of_pos_left hcard).mp
  exact he.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end
end ArtinMatthews.VaryingKummerAnalytic
