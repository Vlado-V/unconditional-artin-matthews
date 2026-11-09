module

public import ArtinMatthews.IdealRationalCellActual
public import ArtinMatthews.IdealCharacterUniformReproduction


set_option backward.privateInPublic true
@[expose] public section

/-! Actual retained cells approximate every rational phase with denominator
inside the character cutoff, at arbitrary logarithmic precision. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

universe u v

theorem idealRationalCellAverage_uniform (a c d X D v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X)
    (hD : 0 ≤ D) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Type u) (B : Type v)
      [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B],
      ∀ (Q r : ℕ) [NeZero r], (Q : ℝ) ≤ L^a → r ≤ Q →
        ∀ (P : A → Finset ℕ) (R : B → Finset ℕ),
        (∀ i p, p ∈ P i → p.Prime) → (∀ i p, p ∈ R i → p.Prime) →
        (∀ i, 0 < bandReciprocalMass (P i)) → (∀ i, 0 < bandReciprocalMass (R i)) →
        (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        (∀ i p, p ∈ R i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        ∀ (i : A) (k : B), IdealPrimeInterval (P i) → IdealPrimeInterval (R k) →
        v₀ ≤ bandReciprocalMass (P i) → v₀ ≤ bandReciprocalMass (R k) →
        ∀ (h : ℝ), 0 < h → ∀ (u : ℤ) (x : IdealSelectedLabels P) (y : IdealSelectedLabels R),
          L^(-X) ≤ idealLogCellMass P h (idealLogCell h x) →
          L^(-X) ≤ idealLogCellMass R h (idealLogCell h y) →
          ‖(Real.fourierChar ((u : ℝ)*(idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ)/r) : ℂ) -
            idealRationalCellAverage P R Q r h (L^(-X)) u x y‖ ≤ L^(-D) := by
  let E := D+a+2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  filter_upwards [idealCharacterCellReproduction_uniform.{u} a c d X E v₀ ha hc hd hX hE hv₀,
    idealCharacterCellReproduction_uniform.{v} a c d X E v₀ ha hc hd hX hE hv₀,
    idealSource_prime_gt_conductor a c hc, eventually_ge_atTop (2 : ℝ)]
    with L hA hB hlarge hL2
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  intro A B _ _ _ _ Q r _ hQ hQr P R hP hR hVP hVR hboundsP hboundsR i k hintervalP hintervalR
    hVloP hVloR h hh u x y hx hy
  have hunitP (z : IdealSelectedLabels P) : (idealSelectedProduct z).Coprime r :=
    idealSelectedProduct_coprime_nat (Nat.pos_of_ne_zero (NeZero.ne r)) hP
      (fun i p hp => hQr.trans_lt (hlarge Q p hQ (hboundsP i p hp).1)) z
  have hunitR (z : IdealSelectedLabels R) : (idealSelectedProduct z).Coprime r :=
    idealSelectedProduct_coprime_nat (Nat.pos_of_ne_zero (NeZero.ne r)) hR
      (fun k p hp => hQr.trans_lt (hlarge Q p hQ (hboundsR k p hp).1)) z
  have hδ : 0 ≤ L^(-E) := Real.rpow_nonneg hL.le _
  have hδ1 : L^(-E) ≤ 1 := by
    have he := Real.rpow_le_rpow_of_exponent_le hL1 (neg_nonpos.mpr hE)
    simpa only [Real.rpow_zero] using he
  have herr := idealRationalCellAverage_error P R hQr h (L^(-X)) u hunitP hunitR x y hδ
    (fun ψ => hA A Q hQ P hP hVP hboundsP i hintervalP hVloP h hh ψ x hx)
    (fun ψ => hB B Q hQ R hR hVR hboundsR k hintervalR hVloR h hh ψ y hy)
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hsqrt : Real.sqrt (r.totient : ℝ) ≤ L^a := by
    have ht : (r.totient : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.totient_le r
    have hs : Real.sqrt (r.totient : ℝ) ≤ (r : ℝ) :=
      Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg r, by nlinarith⟩
    exact hs.trans ((by exact_mod_cast hQr : (r : ℝ) ≤ (Q : ℝ)).trans hQ)
  calc
    _ ≤ Real.sqrt (r.totient : ℝ) * (L^(-E)*(2+L^(-E))) := herr
    _ ≤ L^a * (L^(-E)*3) :=
      mul_le_mul hsqrt (mul_le_mul_of_nonneg_left (by linarith) hδ)
        (by positivity) (by positivity)
    _ = (3/L^2)*L^(-D) := by
      have he : a + -E = -2 + -D := by dsimp [E]; ring
      rw [← mul_assoc, ← Real.rpow_add hL, he, Real.rpow_add hL,
        Real.rpow_neg hL.le, Real.rpow_two]
      ring
    _ ≤ 1*L^(-D) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_one₀ (sq_pos_of_pos hL)).mpr
      nlinarith
    _ = _ := one_mul _

end
end ArtinMatthews
