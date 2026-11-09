module

public import ArtinMatthews.IdealSourceParameterDefinitions
public import ArtinMatthews.IdealSourceBlocks
public import ArtinMatthews.IdealResidualPolynomialCost


set_option backward.privateInPublic true
@[expose] public section

/-! A constant bound on every actual residual coefficient has the
required total cost on the literal canonical pattern family. -/
namespace ArtinMatthews
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealSource_pattern_constant_cost {G : Type*} [DecidableEq G]
    (S T U : Finset G) {m J : ℕ} (hm : m ≤ J) (hST : Disjoint S T) (hU : S ∪ T = U)
    {E C₀ v₀ d C L : ℝ} (hE : 0 ≤ E) (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (hL : 2 ≤ L) (hcard : (U.card : ℝ) ≤ C₀*Real.log L) :
    ((idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm)).card : ℝ)*
      (1+(((⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊ : ℕ) : ℝ)^2/
        L^(-idealSourceThresholdExponent E C₀ v₀ d C m))^2) ≤
      L^(idealSourceCostExponent E C₀ v₀ d C m) := by
  have hcount := idealResidualPatterns_card_le (idealSourceProbes S hm) (idealSourceProbes T hm)
  have hcountR : ((idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm)).card : ℝ) ≤
      1+(2 : ℝ)^((idealSourceProbes S hm).card+(idealSourceProbes T hm).card) := by
    exact_mod_cast hcount
  have hp := idealSourceParameters_nonnegative (v₀ := v₀) hE hC₀ hd hC m
  have hP : (((idealSourceProbes S hm).card+(idealSourceProbes T hm).card : ℕ) : ℝ) ≤
      ((m : ℝ)*C₀)*Real.log L := by
    rw [idealSourceProbes_total_card S T U hm hST hU, Nat.cast_mul]
    have h := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith
  refine (mul_le_mul_of_nonneg_right hcountR (by positivity)).trans ?_
  exact idealResidualScalarCost_bound L ((m : ℝ)*C₀)
    (idealSourceRationalExponent E C₀ v₀ d m) (idealSourceThresholdExponent E C₀ v₀ d C m)
    ((idealSourceProbes S hm).card+(idealSourceProbes T hm).card)
    hL (mul_nonneg (Nat.cast_nonneg _) hC₀) hp.2.1 hp.2.2.2.1 hP

end
end ArtinMatthews
