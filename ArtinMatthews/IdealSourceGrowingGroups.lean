module

public import ArtinMatthews.IdealSourceParameterChoice
public import ArtinMatthews.IdealSourceBlocks


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed source parameters apply to every sufficiently large source
parameter and every finite group carrier satisfying the original bounds. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem idealSource_parameters_for_groups (c₀ C₀ v₀ d C E : ℝ) (ell : ℕ)
    (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d) (hC : 0 ≤ C) (hE : 0 ≤ E) :
    ∃ m : ℕ, 1 ≤ m ∧ 0 < (2/(m+1 : ℕ) : ℝ) ∧ (2/(m+1 : ℕ) : ℝ) < 1 ∧
      (0 ≤ idealSourceErrorExponent E C₀ m ∧
       0 ≤ idealSourceRationalExponent E C₀ v₀ d m ∧
       1 ≤ idealSourceWidthExponent E C₀ v₀ d C m ∧
       0 ≤ idealSourceThresholdExponent E C₀ v₀ d C m ∧
       0 ≤ idealSourceCostExponent E C₀ v₀ d C m) ∧
      ∀ J : ℕ, idealSourceDimensionThreshold m ell ≤ J →
        m ≤ J ∧ (m+ell)*(m+ell-1) ≤ J+ell ∧
        ∀ᶠ L : ℝ in atTop, ∀ (G : Type u) [Fintype G] [DecidableEq G] (U : Finset G),
          c₀*Real.log L ≤ U.card → (U.card : ℝ) ≤ C₀*Real.log L →
          ∃ S T : Finset G, Disjoint S T ∧ S ∪ T = U ∧
            c₀*Real.log L/3 ≤ S.card ∧ c₀*Real.log L/3 ≤ T.card ∧
            (Real.sqrt ((2/(m+1 : ℕ) : ℝ)^S.card)+Real.sqrt ((2/(m+1 : ℕ) : ℝ)^T.card)+
              (2 : ℝ)^(m*U.card)*L^(-idealSourceErrorExponent E C₀ m) ≤ L^(-E)) ∧
            ((1+(2 : ℝ)^(m*U.card))*
              (1+(((⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊ : ℕ) : ℝ)^2/
                L^(-idealSourceThresholdExponent E C₀ v₀ d C m))^2) ≤
              L^(idealSourceCostExponent E C₀ v₀ d C m)) := by
  obtain ⟨m,hm,hθ,hθ1,hparams,hchoice⟩ :=
    idealSource_parameter_choice c₀ C₀ v₀ d C E ell hc₀ hC₀ hd hC hE
  refine ⟨m,hm,hθ,hθ1,hparams,?_⟩
  intro J hJ
  have hfixed := hchoice J hJ
  refine ⟨hfixed.1,hfixed.2.1,?_⟩
  filter_upwards [idealSource_balanced_blocks_eventually.{u} c₀ hc₀,
    eventually_ge_atTop (2 : ℝ)] with L hblocks hL
  intro G _ _ U hUlo hUhi
  obtain ⟨S,T,hST,hunion,hS,hT⟩ := hblocks G U hUlo
  have hbudget := hfixed.2.2 L U.card S.card T.card (m*U.card) hL hUhi le_rfl hS hT
  exact ⟨S,T,hST,hunion,hS,hT,hbudget.1,hbudget.2⟩

end
end ArtinMatthews
