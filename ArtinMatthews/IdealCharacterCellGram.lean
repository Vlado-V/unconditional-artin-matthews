module

public import ArtinMatthews.IdealSelectedCellCancellation
public import ArtinMatthews.IdealSelectedCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! Actual diagonal and off-diagonal character moments in source log cells. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def idealCharacterCellGram (P : I → Finset ℕ) (Q : ℕ) (h : ℝ) (j : ℤ)
    (χ ψ : IdealPrimitiveCharacters Q) : ℂ :=
  ∑ a : IdealSelectedLabels P, (idealSelectedMass P a : ℂ) *
    (if idealLogCell h a = j then
      star (idealPrimitiveCharacterValue χ (idealSelectedProduct a)) *
        idealPrimitiveCharacterValue ψ (idealSelectedProduct a) else 0)

theorem idealCharacterCellGram_eq (P : I → Finset ℕ) (Q : ℕ) (h : ℝ) (j : ℤ)
    (χ ψ : IdealPrimitiveCharacters Q) :
    idealCharacterCellGram P Q h j χ ψ =
      idealSelectedCharacterCell (heckeDirichletProduct (star χ.2.val) ψ.2.val) P h j := by
  unfold idealCharacterCellGram idealSelectedCharacterCell
  apply sum_congr rfl
  intro a _
  rw [heckeDirichletProduct_natCast]
  rfl

theorem idealCharacterCellGram_diag (P : I → Finset ℕ) (Q : ℕ) (h : ℝ) (j : ℤ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hlarge : ∀ i p, p ∈ P i → Q < p)
    (χ : IdealPrimitiveCharacters Q) :
    idealCharacterCellGram P Q h j χ χ = (idealLogCellMass P h j : ℂ) := by
  rw [idealCharacterCellGram, idealLogCellMass, Complex.ofReal_sum]
  apply sum_congr rfl
  intro a _
  split_ifs
  · rw [Complex.star_def, Complex.conj_mul', idealSelectedCharacter_norm_one hP hlarge χ a]
    norm_num
  · simp only [mul_zero, Complex.ofReal_zero]

theorem idealCharacterCellGram_offDiagonal (a c d D v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hD : 0 ≤ D) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^a →
        ∀ (χ ψ : IdealPrimitiveCharacters Q), χ ≠ ψ →
        ∀ (P : I → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
        (∀ i, 0 < bandReciprocalMass (P i)) → ∀ i : I,
        IdealPrimeInterval (P i) →
        (∀ p ∈ P i, Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        v₀ ≤ bandReciprocalMass (P i) →
        ∀ (h : ℝ), 0 < h → ∀ j : ℤ,
          ‖idealCharacterCellGram P Q h j χ ψ‖ ≤ L^(-D) := by
  filter_upwards [idealSelectedCharacterCell_source_bound (I := I) (2*a) c d D v₀
    (by positivity) hc hd hD hv₀, eventually_gt_atTop (0 : ℝ)] with L hcell hL
  intro Q hQ χ ψ hne P hP hV i hinterval hbounds hVlo h hh j
  let : NeZero χ.1.val := ⟨(idealPrimitiveCharacter_level_pos χ).ne'⟩
  let : NeZero ψ.1.val := ⟨(idealPrimitiveCharacter_level_pos ψ).ne'⟩
  have hq : ((χ.1.val*ψ.1.val : ℕ) : ℝ) ≤ L^(2*a) := by
    have hχ : (χ.1.val : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp χ.1.property).2
    have hψ : (ψ.1.val : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp ψ.1.property).2
    calc
      _ = (χ.1.val : ℝ) * (ψ.1.val : ℝ) := by norm_cast
      _ ≤ (Q : ℝ)*(Q : ℝ) := mul_le_mul hχ hψ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ ≤ L^a * L^a := mul_le_mul hQ hQ (Nat.cast_nonneg _) (by positivity)
      _ = L^(2*a) := by rw [← Real.rpow_add hL]; congr 1; ring
  rw [idealCharacterCellGram_eq]
  exact hcell _ (heckeDirichletProduct (star χ.2.val) ψ.2.val) hq
    (idealPrimitiveCharacters_product_nonprincipal χ ψ hne) P hP hV i
    hinterval hbounds hVlo h hh j

end
end ArtinMatthews
