module

public import ArtinMatthews.MarkedMemoryChronologicalRescale
public import ArtinMatthews.MarkedMemorySourceBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! The empty-memory boundary contributes its initial atom normalization
outside W. Combined with the literal n edge factors this is the exact
constant V normalization of each guarded signed memory history. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hV : ∀ j,V j≠0)

include hV

theorem markedMemoryRawActiveMass_rescale {M : ℕ} (a : MarkedRawActive P M) :
    markedRawActiveMass ν a=(∏ j,(V j)⁻¹)^M*
      markedRawActiveMass (markedMemoryScaledAtoms ν V) a := by
  calc
    _ = ∏ j,∏ k,(V j)⁻¹*markedMemoryScaledAtoms ν V j (a j k) := by
      unfold markedRawActiveMass
      apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro k _
      simp [markedMemoryScaledAtoms,hV j]
    _ = _ := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        Finset.prod_pow,markedRawActiveMass]

variable {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (z₀ : Z) (a : MarkedRawActive P (pads+1))

local notation "s" => markedMemoryBoundarySource (B := B) z₀ a

theorem markedMemoryBoundarySource_mass_rescale :
    markedRawStateMass ν s=(∏ j,(V j)⁻¹)^(pads+1)*markedRawStateMass (markedMemoryScaledAtoms ν V) s := by
  rw [markedMemoryBoundarySource_mass,markedMemoryBoundarySource_mass]
  exact markedMemoryRawActiveMass_rescale ν V hV a

variable (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

theorem markedMemoryBoundaryHistory_rescale (n k : ℕ) (H : MarkedMemoryChronologicalHistory hZ n s) :
    (markedRawStateMass ν s:ℂ)*markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k H=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^(pads+1+n))*(markedRawStateMass (markedMemoryScaledAtoms ν V) s:ℂ)*
        markedMemoryChronologicalWeight (markedMemoryScaledAtoms ν V) (fun _ => 1)
          hZ ψ η d₀ Y Q ρ qStage χ n k H := by
  rw [markedMemoryBoundarySource_mass_rescale ν V hV z₀ a,
    markedMemoryChronologicalWeight_rescale ν V hV]
  push_cast
  rw [pow_add]
  ring

theorem markedMemoryBoundaryHistory_guarded_rescale (n k : ℕ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (markedRawStateMass ν s:ℂ)*
      (∑ H : MarkedMemoryChronologicalHistory hZ n s,
        if keep H then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k H*
          f (markedMemoryChronologicalTarget hZ H) else 0)=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^(pads+1+n))*(markedRawStateMass (markedMemoryScaledAtoms ν V) s:ℂ)*
        (∑ H : MarkedMemoryChronologicalHistory hZ n s,
          if keep H then markedMemoryChronologicalWeight (markedMemoryScaledAtoms ν V) (fun _ => 1)
            hZ ψ η d₀ Y Q ρ qStage χ n k H*f (markedMemoryChronologicalTarget hZ H) else 0) := by
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  by_cases hh : keep H
  · simp only [ite_eq_left hh]
    rw [← mul_assoc,markedMemoryBoundaryHistory_rescale ν V hV hZ z₀ a ψ η d₀ Y Q ρ qStage χ n k H]
    ring
  · simp only [ite_eq_right hh,mul_zero]

end
end ArtinMatthews
