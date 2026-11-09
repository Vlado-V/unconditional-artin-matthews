module

public import ArtinMatthews.MarkedMemoryHistoryChronological
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed local change of atom normalization. Multiplying every
band atom by V removes V from a ghost creation coefficient, while each
actual edge pays one inverse V per band, whether promoted or fresh. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}

abbrev markedMemoryScaledAtoms (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) :=
  fun j p => V j*ν j p

theorem markedMemoryGhost_product_rescale
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {B : ℕ} (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l) :
    markedRawGhostSignedCoefficient V qStage ρ m z hz del l*markedRawGhostBirthMass ν l births=
      markedRawGhostSignedCoefficient (fun _ => 1) qStage ρ m z hz del l*
        markedRawGhostBirthMass (markedMemoryScaledAtoms ν V) l births := by
  unfold markedRawGhostSignedCoefficient markedRawGhostBirthMass
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hp : (∏ k,markedMemoryScaledAtoms ν V j (births j k))=
      (V j)^(l.1 j:ℕ)*(∏ k,ν j (births j k)) := by
    simp only [markedMemoryScaledAtoms,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
  have hc : -(1-qStage)*V j/ρ=(-(1-qStage)/ρ)*V j := by ring
  rw [hp,hc,mul_pow]
  simp only [mul_one]
  ring

theorem markedMemoryGhostChoiceWeight_rescale
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P M B Z) (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostChoiceWeight ν V qStage ρ hZ s c=
      markedMemoryGhostChoiceWeight (markedMemoryScaledAtoms ν V) (fun _ => 1) qStage ρ hZ s c :=
  congrArg (fun x : ℝ => (x:ℂ))
    (markedMemoryGhost_product_rescale ν V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) c.deletion c.sizes c.births)

theorem markedMemoryRawEdgePrimeMass_rescale
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hV : ∀ j,V j≠0)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hZ s c=
      (∏ j,(V j)⁻¹)*markedRawEdgeChoicePrimeMass (markedMemoryScaledAtoms ν V) (fun _ => 1) hZ s c := by
  rw [markedRawEdgeChoicePrimeMass_eq_targetLast,markedRawEdgeChoicePrimeMass_eq_targetLast,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hp : (c.promotions j).isSome <;>
    simp [hp,markedMemoryScaledAtoms,hV j]

theorem markedMemoryEdgeChoiceWeight_rescale
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hV : ∀ j,V j≠0)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c=
      ((∏ j,(V j)⁻¹:ℝ):ℂ)*
        markedMemoryEdgeChoiceWeight (markedMemoryScaledAtoms ν V) (fun _ => 1) hZ ψ η d₀ Y Q ρ χ s c := by
  unfold markedMemoryEdgeChoiceWeight
  rw [markedMemoryRawEdgePrimeMass_rescale ν V hV]
  push_cast
  ring

end
end ArtinMatthews
