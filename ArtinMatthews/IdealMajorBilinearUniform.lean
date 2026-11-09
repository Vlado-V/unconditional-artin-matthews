module

public import ArtinMatthews.IdealMajorCellComparisonUniform
public import ArtinMatthews.IdealDiscardedCellUniform
public import ArtinMatthews.IdealCellPhaseBilinear


set_option backward.privateInPublic true
@[expose] public section

/-! The small-denominator branch for arbitrary full selected-label
tests includes the actual discarded logarithmic cells. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

def idealMajorBilinearWidth (a B C E : ℝ) : ℝ :=
  idealMajorCellExponent a B C (E+2)

def idealMajorBilinearThreshold (a B C d E : ℝ) : ℝ :=
  idealDiscardedThresholdExponent d (idealMajorBilinearWidth a B C E) E

theorem idealMajorCellBilinear_uniform (a c d B₀ C E C₀ v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hB : 0 ≤ B₀)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Type u) (B : Type v)
      [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B],
      ∀ (Q r : ℕ) [NeZero r], (Q : ℝ) ≤ L^a → r ≤ Q →
      ∀ (P : A → Finset ℕ) (R : B → Finset ℕ),
      (∀ i p, p ∈ P i → p.Prime) → (∀ i p, p ∈ R i → p.Prime) →
      (∀ i, 0 < bandReciprocalMass (P i)) → (∀ i, 0 < bandReciprocalMass (R i)) →
      (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      (∀ i p, p ∈ R i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      (Fintype.card A : ℝ) ≤ C₀*Real.log L → (Fintype.card B : ℝ) ≤ C₀*Real.log L →
      ∀ (i : A) (j : B), IdealPrimeInterval (P i) → IdealPrimeInterval (R j) →
      v₀ ≤ bandReciprocalMass (P i) → v₀ ≤ bandReciprocalMass (R j) →
      ∀ (u : ℤ) (ζ β : ℝ) (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ),
      |ζ| ≤ L^C →
      (∀ x y, f x ≠ 0 → g y ≠ 0 →
        |β| * (idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ) ≤ L^B₀) →
      ‖∑ x : IdealSelectedLabels P, (idealSelectedMass P x : ℂ)*f x*
        ∑ y : IdealSelectedLabels R, (idealSelectedMass R y : ℂ)*g y*
          (idealProductPhase ζ ((u : ℝ)/r+β) (idealSelectedProduct x) (idealSelectedProduct y) -
            idealFullCellPhaseAverage P R Q (L^(-idealMajorBilinearWidth a B₀ C E))
              (L^(-idealMajorBilinearThreshold a B₀ C d E)) ζ ((u : ℝ)/r+β) x y)‖^2 ≤
        L^(-2*E)*idealFrameEnergy (idealSelectedMass P) f*idealFrameEnergy (idealSelectedMass R) g := by
  let H := idealMajorBilinearWidth a B₀ C E
  let X := idealMajorBilinearThreshold a B₀ C d E
  have hH : 0 ≤ H := by dsimp [H, idealMajorBilinearWidth, idealMajorCellExponent]; linarith
  have hX : 0 ≤ X := by dsimp [X, idealMajorBilinearThreshold, idealDiscardedThresholdExponent]; linarith
  filter_upwards [idealMajorCellComparison_uniform.{u,v} a c d X B₀ C (E+1) v₀
      ha hc hd hX hB hC (by positivity) hv₀,
    idealDiscardedCellMass_uniform.{u} d H E C₀ hd hH,
    idealDiscardedCellMass_uniform.{v} d H E C₀ hd hH,
    eventually_ge_atTop (2 : ℝ)] with L hmajor hbadP hbadR hL2
  have hL : 0 < L := by linarith
  intro A B _ _ _ _ Q r _ hQ hQr P R hP hR hVP hVR hbP hbR hcP hcR i j hi hj hVi hVj
    u ζ β f g hζ hβ
  have heq : idealMajorCellExponent a B₀ C (E+1+1) = H := by
    dsimp [H, idealMajorBilinearWidth, idealMajorCellExponent]
    ring
  have hmain := idealCellPhaseBilinear_sq_le P R hP hR hVP hVR Q (L^(-H)) (L^(-X))
    ζ ((u : ℝ)/r+β) f g (Real.rpow_nonneg hL.le (-(E+1)))
    (fun x y hx hy hcx hcy => by
      have hh := hmajor A B Q r hQ hQr P R hP hR hVP hVR hbP hbR i j hi hj hVi hVj
        u ζ β x y hζ (hβ x y hx hy)
      rw [heq] at hh
      exact hh hcx hcy)
  have hp := hbadP A P hP (fun i p hp => (hbP i p hp).2) hcP
  have hr := hbadR B R hR (fun i p hp => (hbR i p hp).2) hcR
  change idealDiscardedCellMass P (L^(-H)) (L^(-X)) ≤ L^(-2*E-2) at hp
  change idealDiscardedCellMass R (L^(-H)) (L^(-X)) ≤ L^(-2*E-2) at hr
  have hsquare : (L^(-(E+1)))^2 = L^(-2*E-2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
    congr 1
    ring
  have hcost : (L^(-(E+1)))^2+idealDiscardedCellMass P (L^(-H)) (L^(-X))+
      idealDiscardedCellMass R (L^(-H)) (L^(-X)) ≤ L^(-2*E) := by
    rw [hsquare]
    calc
      _ ≤ 3*L^(-2*E-2) := by linarith
      _ = (3/L^2)*L^(-2*E) := by
        rw [show -2*E-2 = -2*E+(-2) by ring, Real.rpow_add hL,
          Real.rpow_neg hL.le, Real.rpow_two]
        ring
      _ ≤ 1*L^(-2*E) := mul_le_mul_of_nonneg_right
        ((div_le_one₀ (by positivity)).mpr (by nlinarith)) (Real.rpow_nonneg hL.le _)
      _ = _ := one_mul _
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost
      (idealFrameEnergy_nonneg _ (idealSelectedMass_nonneg P hVP) f))
    (idealFrameEnergy_nonneg _ (idealSelectedMass_nonneg R hVR) g))

end
end ArtinMatthews
