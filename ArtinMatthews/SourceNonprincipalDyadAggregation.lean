module

public import ArtinMatthews.SourceNonprincipalDyadicExponents
public import ArtinMatthews.SourceNonprincipalRowSeries
public import ArtinMatthews.SourceContinuedPoissonDyadicRightBounds
public import ArtinMatthews.SourceNonprincipalDyadGoodBounds
public import ArtinMatthews.SourceNonprincipalDyadicCard
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual small, intermediate and far frequency dyads are bounded
at the source06 exponent. The intermediate count treats the actual
principal twist and primitive-zero rows as one explicit excluded set. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

private theorem sourceFiniteComplexSum_norm_le {ι : Type} [Fintype ι] (f : ι → ℂ) (B : ℝ)
    (h : ∀ i, ‖f i‖ ≤ B) : ‖∑ i, f i‖ ≤ (Fintype.card ι : ℝ)*B := by
  calc
    _ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, B := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp [nsmul_eq_mul]

private theorem sourceFiniteComplexSum_norm_le_split {ι : Type} [Fintype ι] (f : ι → ℂ) (T : Finset ι)
    (A B : ℝ) (hA : 0 ≤ A) (ha : ∀ i, i ∉ T → ‖f i‖ ≤ A) (hb : ∀ i ∈ T, ‖f i‖ ≤ B) :
    ‖∑ i, f i‖ ≤ (T.card : ℝ)*B+(Fintype.card ι : ℝ)*A := by
  have hC : ((Tᶜ).card : ℝ) ≤ Fintype.card ι := Nat.cast_le.mpr (Finset.card_le_univ _)
  calc
    _ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ = (∑ i ∈ T, ‖f i‖)+(∑ i ∈ Tᶜ, ‖f i‖) := (T.sum_add_sum_compl (fun i => ‖f i‖)).symm
    _ ≤ (∑ _i ∈ T, B)+(∑ _i ∈ Tᶜ, A) := add_le_add (Finset.sum_le_sum hb)
      (Finset.sum_le_sum (fun i hi => ha i (Finset.mem_compl.mp hi)))
    _ = (T.card : ℝ)*B+((Tᶜ).card : ℝ)*A := by simp [nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hC hA)

private theorem sourceDyadic_count_mul_power {m C B Z U a b c : ℝ}
    (hm : m ≤ C*U^c) (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hU : 0 < U) :
    m*(B*Z^a*U^b) ≤ (C*B)*(Z^a*U^(b+c)) := by
  calc
    _ ≤ (C*U^c)*(B*Z^a*U^b) := mul_le_mul_of_nonneg_right hm
      (mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hZ _)) (Real.rpow_nonneg hU.le _))
    _ = (C*B)*(Z^a*(U^b*U^c)) := by ring
    _ = _ := by rw [← Real.rpow_add hU]

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "D" => SourceNonprincipalFrequencyDyad F S₀
local notation "I" => sourceContinuedPoissonRowIntegral F S₀ hζ η hJ
local notation "A" => sourcePoissonNonprincipalDyadSum F S₀ hζ η hJ
local notation "R" => sourceNonprincipalDyadRepresentative F S₀ hζ
local notation "E" => sourceNonprincipalDyadExcluded F S₀ hζ η hJ
local notation "e" => sourceDyadicLoss
local notation "E₀" => sourceContourExponent principalProbeSigma (3/1000) (2/5)
local notation "E₁" => sourceContourExponent (499/500) (3/1000) (2/5)
local notation "E₂" => sourceContourExponent 4 4 350000

theorem exists_sourcePoissonNonprincipalDyad_sum_bound
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) :
    ∃ C U₀ : ℝ, 0 < C ∧ 2 ≤ U₀ ∧ ∀ (j : ℕ) (Z : ℝ), 1 ≤ Z → U₀ ≤ Z^(9/100 : ℝ) →
      ‖A v (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z j‖ ≤
        C*(Z^sourceNonprincipalTargetExponent*sourceNonprincipalDyadicWeight j) := by
  have he : 0 < e := by norm_num [sourceDyadicLoss]
  obtain ⟨L, hL, hlow⟩ := exists_sourceContinuedPoissonRow_low_w_dyadic_bound F S₀ hζ η hJ hcut v e he
  obtain ⟨P, hP, hfarBound⟩ := exists_sourceContinuedPoissonRow_far_z_dyadic_bound F S₀ hζ η hJ hcut v e he
  obtain ⟨r, C, U₀, hr, _, hC, hU₀, hcount, hgood⟩ := exists_sourceNonprincipalDyad_good_bounds F S₀ hζ η hJ hcut v
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 : ℝ)/r)
  have hn' : 2 ≤ r*(n : ℝ) := by
    have h := (div_lt_iff₀ hr).mp hn
    linarith only [h, mul_comm r (n : ℝ)]
  obtain ⟨G, hG, hGRow⟩ := hgood e he n
  let B := sourceFrequencyRepresentativeNormMass F S₀ (1+e)*(2 : ℝ)^(1+e)
  have hB : 0 ≤ B := mul_nonneg (sourceFrequencyRepresentativeNormMass_nonneg F S₀ _) (by positivity)
  let K := B*L+B*P+C*L+2*(B*G)+1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hBL := mul_nonneg hB hL.le
  have hBP := mul_nonneg hB hP.le
  have hCL := mul_nonneg hC.le hL.le
  have hBG := mul_nonneg hB hG.le
  have hKL : B*L ≤ K := by dsimp only [K]; linarith
  have hKP : B*P ≤ K := by dsimp only [K]; linarith
  have hKG : C*L+2*(B*G) ≤ K := by dsimp only [K]; linarith
  refine ⟨K,U₀,hK,hU₀,?_⟩
  intro j Z hZ hZ₀
  let U : ℝ := (2 : ℝ)^j
  let W := Z^sourceNonprincipalTargetExponent*U^(-e)
  have hU : 0 < U := by dsimp only [U]; positivity
  have hZ' : 0 < Z := zero_lt_one.trans_le hZ
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  let Q (i : D j) := I v (R j i) (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z 4 4 2
  have hcard : (Fintype.card (D j) : ℝ) ≤ B*U^(1+e) := sourceNonprincipalFrequencyDyad_card_le F S₀ _ (by linarith) j
  have hq (i : D j) := sourceNonprincipalFrequencyDyad_frequency_bounds F S₀ hζ i
  have hns (i : D j) : ¬ ∃ x : F, x^6 = ((R j i).val : F) := sourceNonprincipalFrequency_not_sixth F S₀ hζ i.val
  have hl (i : D j) : ‖Q i‖ ≤ L*Z^E₀*U^(1/10+e) := hlow (R j i) (hns i) U hU (hq i).1 (hq i).2.le Z hZ'
  have hp (i : D j) : ‖Q i‖ ≤ P*Z^E₂*U^(e-350000) := hfarBound (R j i) (hns i) U hU (hq i).1 (hq i).2.le Z hZ'
  change ‖∑ i, Q i‖ ≤ K*W
  by_cases hsmall : U ≤ Z^(9/100 : ℝ)
  · calc
      _ ≤ (Fintype.card (D j) : ℝ)*(L*Z^E₀*U^(1/10+e)) := sourceFiniteComplexSum_norm_le Q _ hl
      _ ≤ (B*L)*(Z^E₀*U^(1/10+e+(1+e))) := sourceDyadic_count_mul_power hcard hL.le hZ'.le hU
      _ ≤ (B*L)*W := mul_le_mul_of_nonneg_left (sourceNonprincipalDyadic_small_power hZ hU hsmall) (mul_nonneg hB hL.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right hKL hW
  · by_cases hfar : Z^(10001/100000 : ℝ) ≤ U
    · calc
        _ ≤ (Fintype.card (D j) : ℝ)*(P*Z^E₂*U^(e-350000)) := sourceFiniteComplexSum_norm_le Q _ hp
        _ ≤ (B*P)*(Z^E₂*U^(e-350000+(1+e))) := sourceDyadic_count_mul_power hcard hP.le hZ'.le hU
        _ ≤ (B*P)*W := mul_le_mul_of_nonneg_left (sourceNonprincipalDyadic_far_power hZ hU hfar) (mul_nonneg hB hP.le)
        _ ≤ _ := mul_le_mul_of_nonneg_right hKP hW
    · have hlo : Z^(9/100 : ℝ) ≤ U := (lt_of_not_ge hsmall).le
      have hhi : U ≤ Z^(10001/100000 : ℝ) := (lt_of_not_ge hfar).le
      have hth := hZ₀.trans hlo
      let T := E j r
      have hc : (T.card : ℝ) ≤ C*U^(1/2 : ℝ) := hcount j hth
      let V₁ := Z^E₁*U^(1/10+e)
      let V₂ := Z^E₀*U^(1/10+e-r*(n : ℝ))
      have hG' (i : D j) (hi : i ∉ T) : ‖Q i‖ ≤ G*(V₁+V₂) := hGRow j hth i hi Z hZ
      have hsum := sourceFiniteComplexSum_norm_le_split Q T (G*(V₁+V₂)) (L*Z^E₀*U^(1/10+e))
        (by dsimp only [V₁,V₂]; positivity) hG' (fun i _ => hl i)
      have hx := (sourceDyadic_count_mul_power (Z := Z) (a := E₀) (b := 1/10+e) hc hL.le hZ'.le hU).trans
        (mul_le_mul_of_nonneg_left (sourceNonprincipalDyadic_exception_power hZ hU hhi) (mul_nonneg hC.le hL.le))
      have hy := (sourceDyadic_count_mul_power (Z := Z) (a := E₁) (b := 1/10+e) hcard hG.le hZ'.le hU).trans
        (mul_le_mul_of_nonneg_left (sourceNonprincipalDyadic_good_center_power hZ hU hhi) (mul_nonneg hB hG.le))
      have hz := (sourceDyadic_count_mul_power (Z := Z) (a := E₀) (b := 1/10+e-r*(n : ℝ)) hcard hG.le hZ'.le hU).trans
        (mul_le_mul_of_nonneg_left (sourceNonprincipalDyadic_good_error_power hZ hU hlo hn') (mul_nonneg hB hG.le))
      calc
        _ ≤ _ := hsum
        _ = (T.card : ℝ)*(L*Z^E₀*U^(1/10+e))+
            ((Fintype.card (D j) : ℝ)*(G*Z^E₁*U^(1/10+e))+
             (Fintype.card (D j) : ℝ)*(G*Z^E₀*U^(1/10+e-r*(n : ℝ)))) := by dsimp only [V₁,V₂]; ring
        _ ≤ (C*L)*W+((B*G)*W+(B*G)*W) := add_le_add hx (add_le_add hy hz)
        _ = (C*L+2*(B*G))*W := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hKG hW

end
end ArtinMatthews.SourceEulerAssembly
