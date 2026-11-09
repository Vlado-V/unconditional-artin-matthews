module

public import ArtinMatthews.IdealSelectedKernelTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The complete bilinear comparison expression, its arbitrary tests,
and both harmonic energies are unchanged by selected-slot reindexing. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealSelectedComparisonForm {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : I → Finset ℕ) (R : J → Finset ℕ) (Q : ℕ) (h ξ ζ α : ℝ)
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ) : ℂ :=
  ∑ x,(idealSelectedMass P x:ℂ)*f x*∑ y,(idealSelectedMass R y:ℂ)*g y*
    (idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y)-
      idealFullCellPhaseAverage P R Q h ξ ζ α x y)

theorem idealSelectedComparisonForm_transport {I J I' J' : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (P : I → Finset ℕ) (R : J → Finset ℕ) (P' : I' → Finset ℕ) (R' : J' → Finset ℕ)
    (e : IdealSelectedLabels P ≃ IdealSelectedLabels P')
    (d : IdealSelectedLabels R ≃ IdealSelectedLabels R')
    (hmP : ∀ a,idealSelectedMass P a=idealSelectedMass P' (e a))
    (hpP : ∀ a,idealSelectedProduct a=idealSelectedProduct (e a))
    (hmR : ∀ a,idealSelectedMass R a=idealSelectedMass R' (d a))
    (hpR : ∀ a,idealSelectedProduct a=idealSelectedProduct (d a))
    (Q : ℕ) (h ξ ζ α : ℝ) (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ) :
    idealSelectedComparisonForm P R Q h ξ ζ α f g=
      idealSelectedComparisonForm P' R' Q h ξ ζ α (fun a => f (e.symm a)) (fun a => g (d.symm a)) := by
  unfold idealSelectedComparisonForm
  rw [← e.symm.sum_comp]
  apply sum_congr rfl
  intro x _
  rw [hmP,Equiv.apply_symm_apply]
  congr 1
  rw [← d.symm.sum_comp]
  apply sum_congr rfl
  intro y _
  rw [hmR,hpP,hpR,idealFullCellPhaseAverage_transport P R P' R' e d hmP hpP hmR hpR,
    Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem idealSelectedComparisonForm_sigma {G H : Type*}
    [Fintype G] [DecidableEq G] [Fintype H] [DecidableEq H]
    (P : G → Finset ℕ) (R : H → Finset ℕ) {M N : ℕ}
    (S : Finset (G × Fin M)) (T : Finset (H × Fin N))
    (Q : ℕ) (h ξ ζ α : ℝ)
    (f : IdealSelectedLabels (idealResidualBands P S) → ℂ)
    (g : IdealSelectedLabels (idealResidualBands R T) → ℂ) :
    idealSelectedComparisonForm (idealResidualBands P S) (idealResidualBands R T) Q h ξ ζ α f g=
      idealSelectedComparisonForm
        (fun v : Σ a,Fin (idealResidualFreeSlots S a).card => P v.1)
        (fun v : Σ b,Fin (idealResidualFreeSlots T b).card => R v.1) Q h ξ ζ α
        (fun a => f ((idealSelectedSigmaFinEquiv P S).symm a))
        (fun a => g ((idealSelectedSigmaFinEquiv R T).symm a)) :=
  idealSelectedComparisonForm_transport _ _ _ _ (idealSelectedSigmaFinEquiv P S)
    (idealSelectedSigmaFinEquiv R T) (idealSelectedSigmaFin_mass P S) (idealSelectedSigmaFin_product P S)
    (idealSelectedSigmaFin_mass R T) (idealSelectedSigmaFin_product R T) Q h ξ ζ α f g

end
end ArtinMatthews
