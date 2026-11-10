module

public import ArtinMatthews.SourceReflectionFrozenWeights
public import ArtinMatthews.SourcePrimeIdealFactorization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Uniformly summing over admitted active products costs an arbitrary
small power of the actual powerful ideal norm. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "qp" => sourceReflectionPrimeNorm F S₀

theorem sourceReflectionActiveSum_le_product (h : E) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ f ∈ sourceReflectionActiveChoices F S₀ h, sourceReflectionFrozenFactors F S₀ f σ ≤
      ∏ P ∈ h.support, (1 + sourceReflectionFrozenLocalFactor (qp P) σ) := by
  rw [Finset.prod_one_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun f _ _ => sourceReflectionFrozenFactors_nonneg F S₀ f hσ)

theorem exists_sourceReflectionActiveBudget {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : E) (σ : ℝ), 0 ≤ σ →
      ∑ f ∈ sourceReflectionActiveChoices F S₀ h, sourceReflectionFrozenFactors F S₀ f σ ≤
        C * (q h : ℝ) ^ δ := by
  let B : ℝ := 4 + Real.sqrt 2
  have hB : 1 ≤ B := by dsimp [B]; linarith [Real.sqrt_nonneg (2 : ℝ)]
  let T : ℝ := B ^ δ⁻¹
  have hT : 0 ≤ T := Real.rpow_nonneg (zero_le_one.trans hB) _
  let Small : Finset Prime :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊T⌋₊).toFinset.preimage
      (sourceExteriorPrimeIdealEmbedding F S₀) (sourceExteriorPrimeIdealEmbedding F S₀).injective.injOn
  have hsmall (P : Prime) : P ∈ Small ↔ qp P ≤ T := by
    simp only [Small, Finset.mem_preimage, Set.Finite.mem_toFinset]
    exact Nat.le_floor_iff hT
  refine ⟨B ^ Small.card, pow_pos (zero_lt_one.trans_le hB) _, ?_⟩
  intro h σ hσ
  refine (sourceReflectionActiveSum_le_product F S₀ h hσ).trans ?_
  let w (P : Prime) : ℝ := if P ∈ Small then B else 1
  have hb (P : Prime) (hp : P ∈ h.support) :
      1 + sourceReflectionFrozenLocalFactor (qp P) σ ≤ w P * ((qp P) ^ h P) ^ δ := by
    have hpq : 1 ≤ qp P := (show (1 : ℝ) ≤ 2 by norm_num).trans
      (sourceReflection_primeNorm_two_le F S₀ P)
    have he : 1 ≤ h P := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hqpow : qp P ≤ (qp P) ^ h P := by
      simpa only [pow_one] using pow_le_pow_right₀ hpq he
    have h₁ : 1 ≤ ((qp P) ^ h P) ^ δ := Real.one_le_rpow (hpq.trans hqpow) hδ.le
    have hlocal := add_le_add (le_refl (1 : ℝ))
      (sourceReflectionFrozenLocalFactor_le (sourceReflection_primeNorm_two_le F S₀ P) hσ)
    have hlocal' : 1 + sourceReflectionFrozenLocalFactor (qp P) σ ≤ B := by
      dsimp [B]
      linarith
    by_cases hs : P ∈ Small
    · simp only [w, ite_eq_left hs]
      exact hlocal'.trans (le_mul_of_one_le_right (zero_le_one.trans hB) h₁)
    · have hP : T ≤ qp P := le_of_lt (lt_of_not_ge (fun h => hs ((hsmall P).2 h)))
      have hT' : T ^ δ = B := by
        unfold T
        rw [← Real.rpow_mul (zero_le_one.trans hB), inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      simp only [w, ite_eq_right hs, one_mul]
      exact hlocal'.trans (hT' ▸ Real.rpow_le_rpow hT (hP.trans hqpow) hδ.le)
  have hprod : ∏ P ∈ h.support, w P ≤ B ^ Small.card := by
    rw [show (∏ P ∈ h.support, w P) =
        B ^ (h.support.filter (fun P => P ∈ Small)).card by
      simp only [w, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]]
    apply pow_le_pow_right₀ hB
    exact Finset.card_le_card (fun P hp => (Finset.mem_filter.mp hp).2)
  calc
    _ ≤ ∏ P ∈ h.support, w P * ((qp P) ^ h P) ^ δ := by
      apply Finset.prod_le_prod₀
      · intro P _
        exact add_nonneg zero_le_one
          (sourceReflectionFrozenLocalFactor_nonneg (sourceReflection_primeNorm_two_le F S₀ P) hσ)
      · exact hb
    _ = (∏ P ∈ h.support, w P) * (q h : ℝ) ^ δ := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow h.support (fun P => (qp P) ^ h P)
        (fun P _ => pow_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans
          (sourceReflection_primeNorm_two_le F S₀ P)) _) δ]
      congr 2
      simp only [sourcePrimeExponentNorm, Finsupp.prod, Nat.cast_prod, Nat.cast_pow, sourceReflectionPrimeNorm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end
end ArtinMatthews.SourceEulerAssembly
