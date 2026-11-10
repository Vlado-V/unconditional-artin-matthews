module

public import ArtinMatthews.SourceAdditiveCompactBox
public import ArtinMatthews.SourceReducedFractionTraceLift
public import ArtinMatthews.GaussianCoordinateSchur
public import ArtinMatthews.SourceAdditiveFractionsGaussian
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleSieveScale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Section 05's two additive sieve inequalities for actual S-integer
rows and reduced fractions. The existing coordinate estimate is used
with the bounds derived from the compact box and the two ideal norms. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F}

local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "O" => (⊤ : Ideal (𝓞 F))
local notation "J" => IdealModuleFrequencyIndex F O top_ne_bot
local notation "dF" => Module.finrank ℚ F
local notation "coords" => idealModuleIntegerCoordinates F O top_ne_bot

private theorem sourceIntegerCoordinateEnergy_le (n : 𝓞 F) {L : ℝ} (hL : 0 ≤ L)
    (hn : ‖mixedEmbedding F (n : F)‖ ≤ L) :
    (∑ j : J, (coords ⟨n, by simp⟩ j : ℝ) ^ 2) ≤
      (Real.sqrt (dF : ℝ) * (idealModuleIntegerCoordinateConstant F O top_ne_bot * L)) ^ 2 := by
  let a : O := ⟨n, by simp⟩
  let B := idealModuleIntegerCoordinateConstant F O top_ne_bot * L
  have hB : 0 ≤ B := mul_nonneg (idealModuleIntegerCoordinateConstant_pos F O top_ne_bot).le hL
  have hnorm : ‖fun j => (coords a j : ℝ)‖ ≤ B :=
    (idealModuleIntegerCoordinates_norm_le F O top_ne_bot a).trans
      (mul_le_mul_of_nonneg_left hn (idealModuleIntegerCoordinateConstant_pos F O top_ne_bot).le)
  calc
    _ ≤ ∑ _ : J, B ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := (norm_le_pi_norm (fun j => (coords a j : ℝ)) j).trans hnorm
      rw [Real.norm_eq_abs] at h
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr h
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, idealModuleFrequencyIndex_card]
      change (dF : ℝ) * B ^ 2 = (Real.sqrt (dF : ℝ) * B) ^ 2
      calc
        _ = (Real.sqrt (dF : ℝ)) ^ 2 * B ^ 2 := by rw [Real.sq_sqrt (Nat.cast_nonneg dF)]
        _ = _ := (mul_pow _ _ _).symm

/-- The additive and adjoint inequalities on the literal source boxes.
The constant is fixed before any generators, denominator cut, or row
scale are selected. In particular it is uniform over balanced choices. -/
theorem sourceSeparatedAdditiveFractions_sieve (hζ : IsPrimitiveRoot ζ 12)
    (htrace : traceBadPlaces F ⊆ S)
    (B : Set (SLocalAdditiveCompletionSpace F S)) (hB : IsCompact B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : E → R) (ha : ∀ e, a e ≠ 0),
      (∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e}) →
      ∀ N V : ℝ, 1 ≤ N → 1 ≤ V →
      ∀ (A : Finset R) (P : Finset (SourceReducedFractionLabel F S₀ a)),
        (∀ m ∈ A, m ∈ sourceScaledLatticeRows F S₀ hζ B N) →
        (∀ p ∈ P, (q p.1 : ℝ) ≤ V) →
        (∀ b : SourceReducedFractionLabel F S₀ a → ℂ,
          (∑ m ∈ A, ‖∑ p ∈ P, b p * sourceReducedFractionPhase F S₀ a ha p m‖ ^ 2) ≤
            C * (N + V ^ 2) * ∑ p ∈ P, ‖b p‖ ^ 2) ∧
        (∀ v : R → ℂ,
          (∑ p ∈ P, ‖∑ m ∈ A, v m * sourceReducedFractionPhase F S₀ a ha p m‖ ^ 2) ≤
            C * (N + V ^ 2) * ∑ m ∈ A, ‖v m‖ ^ 2) := by
  obtain ⟨δ, hδ, hδS, C, hC, hclear⟩ := exists_sourceScaledLatticeRows_integral F S₀ hζ B hB
  let c := Real.sqrt (dF : ℝ) * (idealModuleIntegerCoordinateConstant F O top_ne_bot * C)
  have hc : 0 < c := mul_pos
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos : 0 < dF)))
    (mul_pos (idealModuleIntegerCoordinateConstant_pos F O top_ne_bot) hC)
  refine ⟨idealModuleSieveScaleConstant F O top_ne_bot c,
    idealModuleSieveScaleConstant_pos F O top_ne_bot hc.le, ?_⟩
  intro a ha hgen N V hN hV A P hA hP
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  let T := N ^ (dF : ℝ)⁻¹
  have hT : 0 < T := Real.rpow_pos_of_pos hN0 _
  let H := c * T
  have hH : 0 < H := mul_pos hc hT
  choose n hn hnorm using fun m (hm : m ∈ A) => hclear N hN0 m (hA m hm)
  have hsupport (m : R) (hm : m ∈ A) : (∑ j : J, (coords ⟨n m hm, by simp⟩ j : ℝ) ^ 2) ≤ H ^ 2 := by
    have he := sourceIntegerCoordinateEnergy_le F (n m hm) (mul_nonneg hC.le hT.le) (hnorm m hm)
    simpa only [H, c, T, mul_assoc] using he
  have hdual (b : SourceReducedFractionLabel F S₀ a → ℂ) :
      (∑ m ∈ A, ‖∑ p ∈ P, b p * sourceReducedFractionPhase F S₀ a ha p m‖ ^ 2) ≤
        idealModuleSieveScaleConstant F O top_ne_bot c * (N + V ^ 2) * ∑ p ∈ P, ‖b p‖ ^ 2 := by
    have hs := sourceReducedFraction_gaussianDual F S₀ hζ htrace δ hδ hδS a ha hgen A n hn
      hH hV0 hsupport P hP b
    exact hs.trans (mul_le_mul_of_nonneg_right
      (idealModuleSieveScale_bound F O top_ne_bot hc.le hN hV)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  refine ⟨hdual, ?_⟩
  have hnonneg : 0 ≤ idealModuleSieveScaleConstant F O top_ne_bot c * (N + V ^ 2) :=
    mul_nonneg (idealModuleSieveScaleConstant_pos F O top_ne_bot hc.le).le (by positivity)
  exact coordinate_finite_sieve_duality P A (sourceReducedFractionPhase F S₀ a ha) hnonneg hdual

end
end ArtinMatthews.SourcePhysical
