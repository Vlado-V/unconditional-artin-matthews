module

public import ArtinMatthews.IdealCharacterCellReproduction
public import ArtinMatthews.IdealConditionalCharacterActual


set_option backward.privateInPublic true
@[expose] public section

/-! Retained source cells reproduce the literal primitive family with
arbitrary logarithmic precision and no additional character hypothesis. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem idealSource_prime_gt_conductor (a c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ Q p : ℕ,
      (Q : ℝ) ≤ L^a → Real.exp (L^c) ≤ (p : ℝ) → Q < p := by
  have hh := (rpow_mul_exp_neg_rpow_tendsto a hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hh] with L hL
  intro Q p hQ hp
  have he : L^a < Real.exp (L^c) := by
    apply (div_lt_one (Real.exp_pos _)).mp
    simpa only [neg_one_mul, Real.exp_neg, div_eq_mul_inv] using hL
  exact_mod_cast hQ.trans_lt (he.trans_le hp)

theorem idealCharacterCellReproduction_actual (a c d X D v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X)
    (hD : 0 ≤ D) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^a →
        ∀ (P : I → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
        (∀ i, 0 < bandReciprocalMass (P i)) →
        (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        ∀ i : I, IdealPrimeInterval (P i) → v₀ ≤ bandReciprocalMass (P i) →
        ∀ (h : ℝ), 0 < h → ∀ (ψ : IdealPrimitiveCharacters Q) (x : IdealSelectedLabels P),
          L^(-X) ≤ idealLogCellMass P h (idealLogCell h x) →
          ‖idealCharacterCellApply P Q h (L^(-X))
              (fun z => idealPrimitiveCharacterValue ψ (idealSelectedProduct z)) x -
            idealPrimitiveCharacterValue ψ (idealSelectedProduct x)‖ ≤ L^(-D) := by
  filter_upwards [idealCharacterCellGram_offDiagonal (I := I) a c d (2*a+X+D) v₀
    ha hc hd (by positivity) hv₀, idealSource_prime_gt_conductor a c hc,
    eventually_gt_atTop (0 : ℝ)] with L hoff hlarge hL
  intro Q hQ P hP hV hbounds i hinterval hVlo h hh ψ x hret
  have hm : 0 < idealLogCellMass P h (idealLogCell h x) :=
    (Real.rpow_pos_of_pos hL (-X)).trans_le hret
  have hp : ∀ k p, p ∈ P k → Q < p := fun k p hmem =>
    hlarge Q p hQ (hbounds k p hmem).1
  have hbound := idealCharacterCellApply_primitive_error P Q h (L^(-X)) hP hp
    (ε := L^(-(2*a+X+D))) (Real.rpow_nonneg hL.le _) ψ x hm hret
    (fun χ hne => hoff Q hQ χ ψ hne P hP hV i hinterval (hbounds i) hVlo h hh _)
  apply hbound.trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hm).mpr
  have hQ2 : (Q : ℝ)^2 ≤ L^(2*a) := by
    calc
      _ ≤ (L^a)^2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
      _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hL.le]; congr 1; ring
  calc
    _ ≤ L^(2*a) * L^(-(2*a+X+D)) :=
      mul_le_mul_of_nonneg_right hQ2 (Real.rpow_nonneg hL.le _)
    _ = L^(-D)*L^(-X) := by
      rw [← Real.rpow_add hL, ← Real.rpow_add hL]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hret (Real.rpow_nonneg hL.le _)

end
end ArtinMatthews
