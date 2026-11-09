module

public import ArtinMatthews.IdealGroupedSelected
public import ArtinMatthews.IdealGroupedPhaseBilinear


set_option backward.privateInPublic true
@[expose] public section

/-! Regrouping selected slots preserves the literal weighted phase
pairing and arbitrary tests on all ordered labels. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem idealGroupedSelected_expectation (P : A → Finset ℕ) (k : A → ℕ)
    (f : IdealSelectedLabels (fun z : Σ i, Fin (k i) => P z.1) → ℂ) :
    (∑ x, (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1) x : ℂ)*f x) =
      ∑ y : IdealGroupedLabels P k, (idealGroupedMass P k y : ℂ)*
        f ((idealGroupedSelectedEquiv P k).symm y) := by
  rw [← (idealGroupedSelectedEquiv P k).symm.sum_comp
    (fun x => (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1) x : ℂ)*f x)]
  apply sum_congr rfl
  intro y _
  rw [idealGroupedSelected_mass, Equiv.apply_symm_apply]

theorem idealGroupedSelected_pairing (P : A → Finset ℕ) (k : A → ℕ)
    (R : B → Finset ℕ) (l : B → ℕ)
    (f : IdealSelectedLabels (fun z : Σ i, Fin (k i) => P z.1) → ℂ)
    (g : IdealSelectedLabels (fun z : Σ i, Fin (l i) => R z.1) → ℂ)
    (K : ℕ → ℕ → ℂ) :
    (∑ x, (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1) x : ℂ)*f x*
      ∑ y, (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1) y : ℂ)*g y*
        K (idealSelectedProduct x) (idealSelectedProduct y)) =
      ∑ x : IdealGroupedLabels P k, (idealGroupedMass P k x : ℂ)*
        f ((idealGroupedSelectedEquiv P k).symm x)*
        ∑ y : IdealGroupedLabels R l, (idealGroupedMass R l y : ℂ)*
          g ((idealGroupedSelectedEquiv R l).symm y)*K (idealGroupedProduct x) (idealGroupedProduct y) := by
  simp only [mul_assoc]
  rw [idealGroupedSelected_expectation]
  apply sum_congr rfl
  intro x _
  rw [idealGroupedSelected_expectation]
  simp only [idealGroupedSelected_product, Equiv.apply_symm_apply]

theorem idealSelectedGroupedPhaseBilinear_sq_le
    (P : A → Finset ℕ) (k : A → ℕ) (R : B → Finset ℕ) (l : B → ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (hdisP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hdisR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hVP : ∀ i, 0 < bandReciprocalMass (P i)) (hVR : ∀ i, 0 < bandReciprocalMass (R i))
    (L T M N : ℕ) (hL : 0 < L) (hT : 0 < T)
    (f : IdealSelectedLabels (fun z : Σ i, Fin (k i) => P z.1) → ℂ)
    (g : IdealSelectedLabels (fun z : Σ i, Fin (l i) => R z.1) → ℂ)
    (hf : ∀ x, idealSelectedProduct x ∉ Ico L (L+M) → f x = 0)
    (hg : ∀ y, idealSelectedProduct y ∉ Ico T (T+N) → g y = 0)
    (ζ α : ℝ) (u : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime u (q : ℤ))
    (happrox : |α-(u : ℝ)/q| ≤ 1/(q : ℝ)^2) :
    ‖∑ x, (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1) x : ℂ)*f x*
      ∑ y, (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1) y : ℂ)*g y*
        idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y)‖^2 ≤
      markedMinorGramBudget M N q*
        (idealGroupedAtomBudget P k/(L : ℝ)*
          idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1)) f)*
        (idealGroupedAtomBudget R l/(T : ℝ)*
          idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1)) g) := by
  rw [idealGroupedSelected_pairing]
  have hsf (x : IdealGroupedLabels P k) (hx : idealGroupedProduct x ∉ Ico L (L+M)) :
      f ((idealGroupedSelectedEquiv P k).symm x) = 0 := by
    apply hf
    simpa only [idealGroupedSelected_product, Equiv.apply_symm_apply] using hx
  have hsg (y : IdealGroupedLabels R l) (hy : idealGroupedProduct y ∉ Ico T (T+N)) :
      g ((idealGroupedSelectedEquiv R l).symm y) = 0 := by
    apply hg
    simpa only [idealGroupedSelected_product, Equiv.apply_symm_apply] using hy
  have hb := idealGroupedPhaseBilinear_sq_le P k R l hP hR hdisP hdisR hVP hVR
    L T M N hL hT (fun x => f ((idealGroupedSelectedEquiv P k).symm x))
    (fun y => g ((idealGroupedSelectedEquiv R l).symm y)) hsf hsg ζ α u q hq hcop happrox
  simpa only [idealFrameEnergy, ← idealGroupedSelected_energy] using hb

end
end ArtinMatthews
