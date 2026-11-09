module

public import ArtinMatthews.IdealSelectedComparisonTransport
public import ArtinMatthews.IdealCharacterCellComparison


set_option backward.privateInPublic true
@[expose] public section

/-! The actual uniform character comparison acts on the literal
selected probe coordinates used by the residual family. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

theorem idealResidualSelected_comparison (m : ℕ) (C₀ v₀ c d C A₀ : ℝ)
    (hC₀ : 0 ≤ C₀) (hv₀ : 0 < v₀) (hc : 0 < c) (hd : 0 ≤ d)
    (hC : 0 ≤ C) (hA₀ : 0 ≤ A₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : Type u) (H : Type v)
      [Fintype G] [DecidableEq G] [Fintype H] [DecidableEq H],
      ∀ (P : G → Finset ℕ) (R : H → Finset ℕ) (M N : ℕ)
        (S : Finset (G × Fin M)) (T : Finset (H × Fin N)),
      (∀ i p,p∈P i → p.Prime) → (∀ i p,p∈R i → p.Prime) →
      Pairwise (fun i j => Disjoint (P i) (P j)) → Pairwise (fun i j => Disjoint (R i) (R j)) →
      (∀ i,v₀ ≤ bandReciprocalMass (P i)) → (∀ i,v₀ ≤ bandReciprocalMass (R i)) →
      (∀ i,(idealResidualFreeSlots S i).card ≤ m) →
      (∀ i,(idealResidualFreeSlots T i).card ≤ m) →
      (Fintype.card G:ℝ) ≤ C₀*Real.log L → (Fintype.card H:ℝ) ≤ C₀*Real.log L →
      (∀ i p,p∈P i → Real.exp (L^c) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^d)) →
      (∀ i p,p∈R i → Real.exp (L^c) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^d)) →
      ∀ (u : ↥S) (v : ↥T),IdealPrimeInterval (P u.val.1) → IdealPrimeInterval (R v.val.1) →
      ∀ (ζ α : ℝ),|ζ| ≤ L^C →
      ∀ (f : IdealSelectedLabels (idealResidualBands P S) → ℂ)
        (g : IdealSelectedLabels (idealResidualBands R T) → ℂ),
      ‖idealSelectedComparisonForm (idealResidualBands P S) (idealResidualBands R T)
        ⌊L^(idealMinorBilinearExponent m C₀ v₀ d (idealComparisonPrecision d A₀))⌋₊
        (L^(-idealComparisonWidth m C₀ v₀ d C (idealComparisonPrecision d A₀)))
        (L^(-idealComparisonThreshold m C₀ v₀ d C (idealComparisonPrecision d A₀))) ζ α f g‖ ≤
        L^(-A₀)*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P S)) f)*
          Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands R T)) g) := by
  filter_upwards [idealCharacterCell_comparison.{u,v} m C₀ v₀ c d C A₀ hC₀ hv₀ hc hd hC hA₀] with L hL
  intro G H _ _ _ _ P R M N S T hP hR hdisP hdisR hVP hVR hS hT hcardG hcardH hbP hbR u v hu hv ζ α hζ f g
  have hu' : (idealSelectedFinIndexEquiv S u).1=u.val.1 := rfl
  have hv' : (idealSelectedFinIndexEquiv T v).1=v.val.1 := rfl
  have hcmp := hL G H P (fun i => (idealResidualFreeSlots S i).card)
    R (fun i => (idealResidualFreeSlots T i).card) hP hR hdisP hdisR hVP hVR hS hT hcardG hcardH hbP hbR
    (idealSelectedFinIndexEquiv S u) (idealSelectedFinIndexEquiv T v) (hu' ▸ hu) (hv' ▸ hv)
    ζ α hζ (fun a => f ((idealSelectedSigmaFinEquiv P S).symm a))
    (fun a => g ((idealSelectedSigmaFinEquiv R T).symm a))
  rw [idealSelectedComparisonForm_sigma]
  rw [← idealSelectedEnergy_transport _ _ (idealSelectedSigmaFinEquiv P S) (idealSelectedSigmaFin_mass P S) f,
    ← idealSelectedEnergy_transport _ _ (idealSelectedSigmaFinEquiv R T) (idealSelectedSigmaFin_mass R T) g] at hcmp
  exact hcmp

end
end ArtinMatthews
