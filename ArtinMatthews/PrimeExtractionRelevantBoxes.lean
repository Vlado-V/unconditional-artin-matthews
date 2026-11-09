module

public import ArtinMatthews.PrimeExtractionDyadicMellin
public import ArtinMatthews.PrimeExtractionRoughSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Exact selection of the boxes required by the marked bilinear criterion:
their products are comparable with x and both endpoints are large. -/

noncomputable section
namespace ArtinMatthews

open OAI.SevenEighths
open scoped BigOperators

def primeExtractionRelevantBoxes (N : ℕ) (a γ x : ℝ) : Finset (ℕ × ℕ) :=
  (primeExtractionDyadicActive N).filter fun kl =>
    a*x ≤ 4*primeExtractionDyadicHeight kl.1 kl.2 ∧
      x^γ/2 < (2 : ℝ)^kl.1 ∧ x^γ/2 < (2 : ℝ)^kl.2

theorem primeExtractionRelevantBoxes_subset (N : ℕ) (a γ x : ℝ) :
    primeExtractionRelevantBoxes N a γ x ⊆ primeExtractionDyadicActive N :=
  Finset.filter_subset _ _

theorem markedExtractionBilinearTerm_eq_zero_of_irrelevant {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a T x γ : ℝ}
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hx : 0 < x)
    {j N : ℕ} (hj : 2 ≤ j) {kl : ℕ × ℕ}
    (hactive : kl ∈ primeExtractionDyadicActive N)
    (hirrel : kl ∉ primeExtractionRelevantBoxes N a γ x)
    {m n : ℕ} (hm : m ∈ primeExtractionDyadicBlock N kl.1)
    (hn : n ∈ primeExtractionDyadicBlock N kl.2) :
    markedExtractionBilinearCoefficient e η χ G γ j x m n *
      (Φ (((m*n : ℕ) : ℝ)/x) : ℂ) = 0 := by
  by_contra hne
  obtain ⟨hA, hcut⟩ := mul_ne_zero_iff.mp hne
  have hlower := markedExtractionBilinearCoefficient_dyadic_lower e η χ G γ x hj hm hn hA
  have hprod := primeExtractionDyadicCutoff_height hx
    (primeExtraction_complexCutoff_support Φ hsupp) hm hn hcut
  exact hirrel (Finset.mem_filter.mpr ⟨hactive, hprod.2, hlower⟩)

theorem markedDirectTupleThetaSum_relevant {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a T x : ℝ}
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hx : 0 < x)
    (γ : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    markedDirectTupleThetaSum e η χ G Φ T γ j x =
      ∑ kl ∈ primeExtractionRelevantBoxes ⌊T*x⌋₊ a γ x,
        ∑ m ∈ primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1,
          ∑ n ∈ primeExtractionDyadicBlock ⌊T*x⌋₊ kl.2,
            markedExtractionBilinearCoefficient e η χ G γ j x m n *
              (Φ (((m*n : ℕ) : ℝ)/x) : ℂ) := by
  rw [markedDirectTupleThetaSum_dyadic e η χ G Φ hsupp hx γ (by omega)]
  symm
  apply Finset.sum_subset (primeExtractionRelevantBoxes_subset _ _ _ _)
  intro kl hactive hirrel
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  exact markedExtractionBilinearTerm_eq_zero_of_irrelevant e η χ G Φ hsupp hx hj
    hactive hirrel hm hn

theorem primeExtractionRelevantBoxes_geometry {N : ℕ} {a T γ x : ℝ}
    (hN : (N : ℝ) ≤ T*x) {kl : ℕ × ℕ}
    (hkl : kl ∈ primeExtractionRelevantBoxes N a γ x) :
    a*x/4 ≤ primeExtractionDyadicHeight kl.1 kl.2 ∧
      primeExtractionDyadicHeight kl.1 kl.2 ≤ T*x ∧
      x^γ/2 < (2 : ℝ)^kl.1 ∧ x^γ/2 < (2 : ℝ)^kl.2 := by
  obtain ⟨hactive, hprod, hm, hn⟩ := Finset.mem_filter.mp hkl
  have hheight : primeExtractionDyadicHeight kl.1 kl.2 ≤ N := by
    unfold primeExtractionDyadicHeight
    exact_mod_cast (Finset.mem_filter.mp hactive).2
  exact ⟨by linarith, hheight.trans hN, hm, hn⟩

end ArtinMatthews
