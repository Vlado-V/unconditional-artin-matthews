module

public import ArtinMatthews.IdealCharacterCellGram


set_option backward.privateInPublic true
@[expose] public section

/-! A pointwise arithmetic interface derived uniformly before any finite
slot carrier is chosen. This preserves uniformity for growing prime groups. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def IdealPrimeCharacterInput (L c d v₀ : ℝ) (Q : ℕ) (ε : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    (q : ℝ) ≤ (Q : ℝ)^2 → χ ≠ 1 →
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → IdealPrimeInterval P →
    (∀ p ∈ P, Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
    v₀ ≤ bandReciprocalMass P →
    ∀ h : ℝ, 0 < h → ∀ r : ℕ, 0 < r → ∀ j : ℤ,
      ‖idealHarmonicPrimeCell χ P h r j‖ ≤ ε

theorem idealPrimeCharacterInput_eventually (a c d D v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hD : 0 ≤ D) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, (Q : ℝ) ≤ L^a →
      IdealPrimeCharacterInput L c d v₀ Q (L^(-D)) := by
  filter_upwards [idealHarmonicPrimeCell_source_bound (2*a) c d D v₀
    (by positivity) hc hd hD hv₀, eventually_gt_atTop (0 : ℝ)] with L hcell hL
  intro Q hQ q _ χ hq hχ P hP hinterval hbounds hV h hh r hr j
  have hQ2 : (Q : ℝ)^2 ≤ L^(2*a) := by
    calc
      _ ≤ (L^a)^2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
      _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hL.le]; congr 1; ring
  exact hcell q χ (hq.trans hQ2) hχ P hP hinterval hbounds hV h hh r hr j

theorem idealCharacterCellGram_of_primeInput {I : Type*} [Fintype I] [DecidableEq I]
    {L c d v₀ ε : ℝ} {Q : ℕ} (hinput : IdealPrimeCharacterInput L c d v₀ Q ε)
    (P : I → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (i : I)
    (hinterval : IdealPrimeInterval (P i))
    (hbounds : ∀ p ∈ P i, Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d))
    (hVlo : v₀ ≤ bandReciprocalMass (P i)) (h : ℝ) (hh : 0 < h) (j : ℤ)
    (χ ψ : IdealPrimitiveCharacters Q) (hne : χ ≠ ψ) :
    ‖idealCharacterCellGram P Q h j χ ψ‖ ≤ ε := by
  let : NeZero χ.1.val := ⟨(idealPrimitiveCharacter_level_pos χ).ne'⟩
  let : NeZero ψ.1.val := ⟨(idealPrimitiveCharacter_level_pos ψ).ne'⟩
  have hq : ((χ.1.val*ψ.1.val : ℕ) : ℝ) ≤ (Q : ℝ)^2 := by
    have hχ : (χ.1.val : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp χ.1.property).2
    have hψ : (ψ.1.val : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp ψ.1.property).2
    simpa only [Nat.cast_mul, pow_two] using
      mul_le_mul hχ hψ (Nat.cast_nonneg ψ.1.val) (Nat.cast_nonneg Q)
  rw [idealCharacterCellGram_eq]
  apply idealSelectedCharacterCell_bound _ P hP hV i h j
  intro r hr
  exact hinput _ (heckeDirichletProduct (star χ.2.val) ψ.2.val) hq
    (idealPrimitiveCharacters_product_nonprincipal χ ψ hne) (P i) (hP i)
    hinterval hbounds hVlo h hh r hr j

end
end ArtinMatthews
