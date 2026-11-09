module

public import ArtinMatthews.IdealSelectedFibers
public import ArtinMatthews.IdealCellPhaseComparison


set_option backward.privateInPublic true
@[expose] public section

/-! Mass and product preserving slot reindexing transports the actual
log-cell kernel and its full phase average exactly. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealLogCell_transport {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : I → Finset ℕ) (R : J → Finset ℕ)
    (e : IdealSelectedLabels P ≃ IdealSelectedLabels R)
    (hp : ∀ a,idealSelectedProduct a=idealSelectedProduct (e a))
    (h : ℝ) (a : IdealSelectedLabels P) : idealLogCell h a=idealLogCell h (e a) := by
  unfold idealLogCell
  rw [hp]

theorem idealLogCellMass_transport {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : I → Finset ℕ) (R : J → Finset ℕ)
    (e : IdealSelectedLabels P ≃ IdealSelectedLabels R)
    (hm : ∀ a,idealSelectedMass P a=idealSelectedMass R (e a))
    (hp : ∀ a,idealSelectedProduct a=idealSelectedProduct (e a)) (h : ℝ) (j : ℤ) :
    idealLogCellMass P h j=idealLogCellMass R h j := by
  unfold idealLogCellMass
  rw [← e.symm.sum_comp]
  apply sum_congr rfl
  intro a _
  rw [idealLogCell_transport P R e hp,hm,Equiv.apply_symm_apply]

theorem idealCharacterCellKernel_transport {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : I → Finset ℕ) (R : J → Finset ℕ)
    (e : IdealSelectedLabels P ≃ IdealSelectedLabels R)
    (hm : ∀ a,idealSelectedMass P a=idealSelectedMass R (e a))
    (hp : ∀ a,idealSelectedProduct a=idealSelectedProduct (e a))
    (Q : ℕ) (h ξ : ℝ) (a b : IdealSelectedLabels P) :
    idealCharacterCellKernel P Q h ξ a b=idealCharacterCellKernel R Q h ξ (e a) (e b) := by
  unfold idealCharacterCellKernel
  rw [idealLogCell_transport P R e hp h a,idealLogCell_transport P R e hp h b,
    idealLogCellMass_transport P R e hm hp]
  rw [hp a,hp b]

theorem idealSelectedEnergy_transport {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : I → Finset ℕ) (R : J → Finset ℕ)
    (e : IdealSelectedLabels P ≃ IdealSelectedLabels R)
    (hm : ∀ a,idealSelectedMass P a=idealSelectedMass R (e a))
    (f : IdealSelectedLabels P → ℂ) :
    idealFrameEnergy (idealSelectedMass P) f=
      idealFrameEnergy (idealSelectedMass R) (fun a => f (e.symm a)) := by
  unfold idealFrameEnergy
  rw [← e.symm.sum_comp]
  apply sum_congr rfl
  intro a _
  rw [hm,Equiv.apply_symm_apply]

theorem idealFullCellPhaseAverage_transport {I J I' J' : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (P : I → Finset ℕ) (R : J → Finset ℕ) (P' : I' → Finset ℕ) (R' : J' → Finset ℕ)
    (e : IdealSelectedLabels P ≃ IdealSelectedLabels P')
    (d : IdealSelectedLabels R ≃ IdealSelectedLabels R')
    (hmP : ∀ a,idealSelectedMass P a=idealSelectedMass P' (e a))
    (hpP : ∀ a,idealSelectedProduct a=idealSelectedProduct (e a))
    (hmR : ∀ a,idealSelectedMass R a=idealSelectedMass R' (d a))
    (hpR : ∀ a,idealSelectedProduct a=idealSelectedProduct (d a))
    (Q : ℕ) (h ξ ζ α : ℝ) (a : IdealSelectedLabels P) (b : IdealSelectedLabels R) :
    idealFullCellPhaseAverage P R Q h ξ ζ α a b=
      idealFullCellPhaseAverage P' R' Q h ξ ζ α (e a) (d b) := by
  unfold idealFullCellPhaseAverage
  rw [← e.symm.sum_comp]
  apply sum_congr rfl
  intro x _
  rw [← d.symm.sum_comp]
  apply sum_congr rfl
  intro y _
  rw [hmP,hmR,idealCharacterCellKernel_transport P P' e hmP hpP,
    idealCharacterCellKernel_transport R R' d hmR hpR,hpP,hpR,
    Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem idealSelectedSigmaFin_kernel {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (Q : ℕ) (h ξ : ℝ) (a b : IdealSelectedLabels (idealResidualBands P S)) :
    idealCharacterCellKernel (idealResidualBands P S) Q h ξ a b=
      idealCharacterCellKernel (fun v : Σ g,Fin (idealResidualFreeSlots S g).card => P v.1) Q h ξ
        (idealSelectedSigmaFinEquiv P S a) (idealSelectedSigmaFinEquiv P S b) :=
  idealCharacterCellKernel_transport _ _ (idealSelectedSigmaFinEquiv P S)
    (idealSelectedSigmaFin_mass P S) (idealSelectedSigmaFin_product P S) Q h ξ a b

end
end ArtinMatthews
