module

public import ArtinMatthews.PositiveDensityCubicCuspStatistic


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed progression test of the actual cusp coefficients splits
into its literal Dirichlet twists, retaining their values at nonunits. -/

noncomputable section
namespace ArtinMatthews

open Filter UpperHalfPlane
open scoped MatrixGroups BigOperators Topology

theorem giantCubicCuspPrimeTest_character_expansion {A : ℤ}
    (f : CuspForm (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1)
    {M : ℕ} [NeZero M] (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) :
    giantCubicCuspPrimeTest f (fun p => giantUnitResidueIndicator U p) ε Φ T x =
      ∑ χ : DirichletCharacter ℂ M, giantResidueCharacterCoefficient U χ *
        giantCubicCuspPrimeTest f (fun p => χ p) ε Φ T x := by
  let w (p : ℕ) : ℂ := (giantSieveWeight Φ x p : ℂ) *
    (((giantPrimeFactors (p - 1) x ε).card : ℝ) : ℂ) * (qExpansion 1 f).coeff p
  unfold giantCubicCuspPrimeTest
  calc
    _ = ∑ p ∈ giantPrimeMeanRange T x, w p * giantUnitResidueIndicator U p := by
      apply Finset.sum_congr rfl
      intro p _hp
      dsimp only [w]
      ring
    _ = ∑ χ : DirichletCharacter ℂ M, giantResidueCharacterCoefficient U χ *
        ∑ p ∈ giantPrimeMeanRange T x, w p * χ p :=
      giantUnitResidueIndicator_weighted_sum U (giantPrimeMeanRange T x) w
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _hχ
      congr 1
      apply Finset.sum_congr rfl
      intro p _hp
      dsimp only [w]
      ring

theorem giantCubicCuspPrimeTest_mean_of_character_limits {A : ℤ}
    (f : CuspForm (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1)
    {M : ℕ} [NeZero M] (U : Finset (ZMod M)ˣ) (ε : ℝ) (Φ : ℝ → ℝ) (T : ℝ)
    (hχ : ∀ χ : DirichletCharacter ℂ M,
      Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
        giantCubicCuspPrimeTest f (fun p => χ p) ε Φ T x) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
      giantCubicCuspPrimeTest f (fun p => giantUnitResidueIndicator U p) ε Φ T x)
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (DirichletCharacter ℂ M))
    (fun χ _ => (tendsto_const_nhds (x := giantResidueCharacterCoefficient U χ)).mul (hχ χ))
  simp only [mul_zero, Finset.sum_const_zero] at h
  apply h.congr
  intro x
  rw [giantCubicCuspPrimeTest_character_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _hχ
  ring

end ArtinMatthews
