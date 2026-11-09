module

public import ArtinMatthews.MarkedPhysicalBadHaarMain
public import ArtinMatthews.MarkedPhysicalBadRootReplacement


set_option backward.privateInPublic true
@[expose] public section

/-! Identification and estimate of the explicit main term returned by
the actual positive canonical-root replacement. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalBadRootKernelMain_eq_positive
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (S : ℕ) (A B C D : ℝ) (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ) :
    markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D d b a R Q ψ =
      markedPhysicalRootPositiveMain Finset.univ S A B C D
        (markedPhysicalBadArcLower e x source d₀ Y)
        (markedPhysicalBadArcUpper e x source d₀ Y)
        (markedPhysicalBadArcCoefficient e x source d₀ Y) d b a R Y Q ψ := by
  unfold markedPhysicalBadRootKernelMain markedPhysicalRootPositiveMain
  rw [Finset.product_eq_sprod, Finset.sum_product]

theorem markedPhysicalBadRootKernelMain_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e) (T : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d₀ Y : ℝ,
      Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (S : ℕ), Squarefree S →
        ∀ A B C D : ℝ, A ≤ B → C ≤ D →
        ∀ (d b a : ℤ) (R Q W : ℝ) (ψ : ℝ → ℂ),
          1 ≤ Q → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
          (∀ u, ‖ψ u‖ ≤ W) → (∀ u, ψ u ≠ 0 → |u| ≤ R) →
          markedPhysicalBadRootKernelMain e x source d₀ Y (S := S) A B C D d b a R Q ψ ≤
          ((B-A)*(D-C)/((riemannZeta 2).re*
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
            ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
  filter_upwards [markedPhysicalBadRootPositiveMain_log_saving e he hinj T] with x hx
  intro d₀ Y hY source S hS A B C D hAB hCD d b a R Q W ψ hQ hYone hR hW hψ hsupp
  rw [markedPhysicalBadRootKernelMain_eq_positive]
  exact hx d₀ Y hY source S hS A B C D hAB hCD d b a R Q W ψ hQ hYone hR hW hψ hsupp

end ArtinMatthews
