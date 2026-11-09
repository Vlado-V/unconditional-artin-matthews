module

public import ArtinMatthews.IdealCharacterUniformNorm
public import ArtinMatthews.IdealCharacterCellReproduction


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive reproduction with its arithmetic threshold chosen before
any finite source slot carrier. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem idealCharacterCellReproduction_of_primeInput {I : Type*} [Fintype I] [DecidableEq I]
    {L c d v₀ ε ξ : ℝ} {Q : ℕ} (hinput : IdealPrimeCharacterInput L c d v₀ Q ε)
    (hε : 0 ≤ ε) (P : I → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (hlarge : ∀ i p, p ∈ P i → Q < p)
    (i : I) (hinterval : IdealPrimeInterval (P i))
    (hbounds : ∀ p ∈ P i, Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d))
    (hVlo : v₀ ≤ bandReciprocalMass (P i)) (h : ℝ) (hh : 0 < h)
    (ψ : IdealPrimitiveCharacters Q) (x : IdealSelectedLabels P)
    (hm : 0 < idealLogCellMass P h (idealLogCell h x))
    (hr : ξ ≤ idealLogCellMass P h (idealLogCell h x)) :
    ‖idealCharacterCellApply P Q h ξ (fun z => idealPrimitiveCharacterValue ψ (idealSelectedProduct z)) x -
      idealPrimitiveCharacterValue ψ (idealSelectedProduct x)‖ ≤
        (Q : ℝ)^2*(ε/idealLogCellMass P h (idealLogCell h x)) :=
  idealCharacterCellApply_primitive_error P Q h ξ hP hlarge hε ψ x hm hr
    (fun χ hne => idealCharacterCellGram_of_primeInput hinput P hP hV i hinterval hbounds hVlo h hh _ χ ψ hne)

theorem idealCharacterCellReproduction_uniform (a c d X D v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X)
    (hD : 0 ≤ D) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type u) [Fintype I] [DecidableEq I],
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^a →
      ∀ (P : I → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
      (∀ i, 0 < bandReciprocalMass (P i)) →
      (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      ∀ i : I, IdealPrimeInterval (P i) → v₀ ≤ bandReciprocalMass (P i) →
      ∀ h : ℝ, 0 < h → ∀ (ψ : IdealPrimitiveCharacters Q) (x : IdealSelectedLabels P),
      L^(-X) ≤ idealLogCellMass P h (idealLogCell h x) →
      ‖idealCharacterCellApply P Q h (L^(-X))
          (fun z => idealPrimitiveCharacterValue ψ (idealSelectedProduct z)) x -
        idealPrimitiveCharacterValue ψ (idealSelectedProduct x)‖ ≤ L^(-D) := by
  filter_upwards [idealPrimeCharacterInput_eventually a c d (2*a+X+D) v₀
    ha hc hd (by positivity) hv₀, idealSource_prime_gt_conductor a c hc,
    eventually_gt_atTop (0 : ℝ)] with L hinput hsize hL
  intro I _ _ Q hQ P hP hV hbounds i hinterval hVlo h hh ψ x hret
  have hm : 0 < idealLogCellMass P h (idealLogCell h x) := (Real.rpow_pos_of_pos hL _).trans_le hret
  have hb := idealCharacterCellReproduction_of_primeInput (hinput Q hQ) (Real.rpow_nonneg hL.le _)
    P hP hV (fun k p hp => hsize Q p hQ (hbounds k p hp).1)
    i hinterval (hbounds i) hVlo h hh ψ x hm hret
  apply hb.trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hm).mpr
  have hQ2 : (Q : ℝ)^2 ≤ L^(2*a) := by
    calc
      _ ≤ (L^a)^2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
      _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hL.le]; congr 1; ring
  calc
    _ ≤ L^(2*a)*L^(-(2*a+X+D)) := mul_le_mul_of_nonneg_right hQ2 (Real.rpow_nonneg hL.le _)
    _ = L^(-D)*L^(-X) := by rw [← Real.rpow_add hL, ← Real.rpow_add hL]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hret (Real.rpow_nonneg hL.le _)

end
end ArtinMatthews
