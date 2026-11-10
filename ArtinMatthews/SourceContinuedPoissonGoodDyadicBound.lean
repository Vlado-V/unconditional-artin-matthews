module

public import ArtinMatthews.PrincipalDedekindAbsoluteContour
public import ArtinMatthews.SourceContinuedPoissonRowIntegral
public import ArtinMatthews.SourceProbeComparison
public import ArtinMatthews.SourceRowTwistDyadicExcluded
public import ArtinMatthews.SourceContinuedPoissonGoodXi
public import ArtinMatthews.SourcePoissonGoodXiInputs
public import ArtinMatthews.SourcePoissonGoodXiNorm
public import ArtinMatthews.SourceRowAnalyticBounds
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

/-! Quantitative estimate of the literal good dyad row. The central
piece gains the .998 exponent. The horizontal sides and original right
tail retain the right exponent and gain any chosen cutoff power. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set MeasureTheory
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "K" => sourceContinuedPoissonRowKernel F S₀ hζ η hJ
local notation "I" => sourceContinuedPoissonRowIntegral F S₀ hζ η hJ
local notation "Cw" => (3/1000 : ℝ)
local notation "Cz" => (2/5 : ℝ)
local notation "λx" => (499/500 : ℝ)
local notation "σx" => principalProbeSigma

theorem exists_sourceContinuedPoissonRow_good_dyadic_bound_of_reciprocal
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι] (f : ι → {u : R // u ≠ 0}) (i : ι),
      (¬ ∃ x : F, x^6 = ((f i).val : F)) →
      ∀ U r : ℝ, 1 ≤ U → 0 ≤ r → i ∉ sourceRowTwistDyadicExcludedRows F S₀ hζ η hJ f U r →
      U ≤ sourcePoissonFrequencyNorm F S₀ (f i) → sourcePoissonFrequencyNorm F S₀ (f i) ≤ 2*U →
      (∀ ξ : ℂ, λx ≤ ξ.re → |ξ.im| ≤ U^r →
        ‖sourceRowTwistReciprocal F hζ S₀ (f i).val (f i).property η hJ ξ‖ ≤ B*U^(ε/2)) →
      ∀ Z : ℝ, 1 ≤ Z →
        ‖I v (f i) (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z 4 4 2‖ ≤ C*
          (Z^(sourceContourExponent λx Cw Cz)*U^(1/10+ε)+
            Z^(sourceContourExponent σx Cw Cz)*U^(1/10+ε-r*(n : ℝ))) := by
  obtain ⟨D,hD,hdecay⟩ := exists_sourceContinuedPoissonLowKernel_decay_with_reciprocal_bound F S₀ hζ η hJ
    hcut v ε hε n
  have hab : λx ≤ σx := by norm_num [principalProbeSigma]
  have hσ : 1 < σx := by norm_num [principalProbeSigma]
  let G := Real.exp ((σx+Cz-1)^2)
  let Br := sourceRayAbsoluteEulerBound F σx
  let N := ‖(1/(2*Real.pi) : ℂ)^3‖
  have hG : 0 < G := Real.exp_pos _
  have hBr : 0 < Br := sourceRayAbsoluteEulerBound_pos F _
  have hN : 0 ≤ N := norm_nonneg _
  have hM₀ := sourcePoissonHeightMomentMass_nonneg 0
  have hMn := sourcePoissonHeightMomentMass_nonneg n
  have hHn := sourcePoissonHorizontalMass_nonneg n
  let C₁ := N*(D*B*G*sourcePoissonHeightMomentMass 0)
  let C₂ := N*(2*(D*B*G*sourcePoissonHorizontalMass n*(σx-λx))+D*Br*G*sourcePoissonHeightMomentMass n)
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by
    dsimp only [C₂]
    exact mul_nonneg hN (add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (sub_nonneg.mpr hab))) (by positivity))
  refine ⟨C₁+C₂+1, by linarith, ?_⟩
  intro ι inst f i hu U r hU hr hi hlo hhi hrec Z hZ
  have hU₀ : 0 < U := zero_lt_one.trans_le hU
  have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ
  let X := Z^(9/10 : ℝ)
  let Y := Z^(133/1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ₀ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ₀ _
  let T := U^r
  have hT : 0 ≤ T := Real.rpow_nonneg hU₀.le _
  let P := U^(1/10+ε)
  let P₁ := Z^(sourceContourExponent λx Cw Cz)*P
  let P₂ := Z^(sourceContourExponent σx Cw Cz)*U^(1/10+ε-r*(n : ℝ))
  have hP : 0 ≤ P := Real.rpow_nonneg hU₀.le _
  have hP₁ : 0 ≤ P₁ := by dsimp only [P₁]; positivity
  have hP₂ : 0 ≤ P₂ := by dsimp only [P₂]; positivity
  let L := D*B*G*P₁
  let H := D*B*G*P₂
  let Rt := D*Br*G*P₂
  let A (ξ : ℂ) (wt : ℝ×ℝ) := K v (f i) X Y Z (ξ,sourcePoissonVertical Cw wt.1,sourcePoissonVertical Cz wt.2)
  have hrec' (a x : ℝ) (ha : λx ≤ a) (hx : |x| ≤ T) :
      ‖sourceRowTwistReciprocal F hζ S₀ (f i).val (f i).property η hJ (sourcePoissonVertical a x)‖ ≤ B*U^(ε/2) :=
    hrec _ (by simpa only [sourcePoissonVertical_re] using ha) (by simpa only [sourcePoissonVertical_im] using hx)
  have habs (a x y t B' : ℝ) (ha : λx ≤ a) (ha' : a ≤ σx) (hB' : 0 ≤ B') (hx : T ≤ |x|)
      (hR' : ‖sourceRowTwistReciprocal F hζ S₀ (f i).val (f i).property η hJ
        (sourcePoissonVertical a x)‖ ≤ B'*U^(ε/2)) :
      ‖A (sourcePoissonVertical a x) (y,t)‖ ≤ (D*B'*G*P₂)*sourcePoissonHeightMoment n ((y,t),x) := by
    have hS : Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2) ≤
        Z^(sourceContourExponent σx Cw Cz)*G :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hZ (sourcePoissonLowExponent_le ha'))
        (sourcePoissonLowGaussian_le ha ha') (Real.exp_nonneg _) (Real.rpow_nonneg hZ₀.le _)
    have h0 := hdecay (f i) hu U hU₀ hlo hhi Z hZ₀ a ha y t x B' hR'
    let W := sourceContourHeightWeight y*(Real.exp (-((x+t)^2))/(1+|t|)^(n+2))
    have hW : 0 ≤ W := mul_nonneg (sourceContourHeightWeight_nonneg _) (by positivity)
    let E := D*B'*G*(Z^(sourceContourExponent σx Cw Cz)*P)
    have hE : 0 ≤ E := by dsimp only [E]; positivity
    have hcoeff : D*B'*Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2)*P ≤ E := by
      calc
        _ = (D*B'*(Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2)))*P := by ring
        _ ≤ (D*B'*(Z^(sourceContourExponent σx Cw Cz)*G))*P :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS (mul_nonneg hD.le hB')) hP
        _ = E := by dsimp only [E]; ring
    have hpow : P*U^(-r*(n : ℝ)) = U^(1/10+ε-r*(n : ℝ)) := by
      dsimp only [P]
      rw [← Real.rpow_add hU₀, sub_eq_add_neg, neg_mul]
    have hd := (sourcePoissonHeight_decay_pointwise n y t x T hT hx).trans
      (mul_le_mul_of_nonneg_right (sourcePoissonHeight_cutoffPower_le n (r := r) hU₀)
        (sourcePoissonHeightMoment_nonneg _ _))
    calc
      _ ≤ (D*B'*Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2)*P)*W := h0
      _ ≤ E*W := mul_le_mul_of_nonneg_right hcoeff hW
      _ ≤ E*(U^(-r*(n : ℝ))*sourcePoissonHeightMoment n ((y,t),x)) := mul_le_mul_of_nonneg_left hd hE
      _ = _ := by
        dsimp only [E,P₂]
        calc
          _ = (D*B'*G*(Z^(sourceContourExponent σx Cw Cz)*(P*U^(-r*(n : ℝ)))))*sourcePoissonHeightMoment n ((y,t),x) := by ring
          _ = _ := by rw [hpow]
  have hL (p : SourcePoissonHeights) (hp : p.2 ∈ Ioc (-T) T) :
      ‖sourcePoissonXiVerticalKernel A λx p‖ ≤ L*sourcePoissonHeightMoment 0 p := by
    have h0 := hdecay (f i) hu U hU₀ hlo hhi Z hZ₀ λx le_rfl p.1.1 p.1.2 p.2 B
      (hrec' λx p.2 le_rfl (abs_le.mpr ⟨hp.1.le,hp.2⟩))
    have hg := sourcePoissonLowGaussian_le (a := λx) le_rfl hab
    let W := sourceContourHeightWeight p.1.1*(Real.exp (-((p.2+p.1.2)^2))/(1+|p.1.2|)^(n+2))
    have hW : 0 ≤ W := mul_nonneg (sourceContourHeightWeight_nonneg _) (by positivity)
    have hcoef : D*B*Z^(sourceContourExponent λx Cw Cz)*Real.exp ((λx+Cz-1)^2)*P ≤ L := by
      calc
        _ ≤ D*B*Z^(sourceContourExponent λx Cw Cz)*G*P :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hP
        _ = L := by dsimp only [L,P₁]; ring
    calc
      _ ≤ (D*B*Z^(sourceContourExponent λx Cw Cz)*Real.exp ((λx+Cz-1)^2)*P)*W := h0
      _ ≤ L*W := mul_le_mul_of_nonneg_right hcoef hW
      _ ≤ _ := mul_le_mul_of_nonneg_left (sourcePoissonHeight_central_pointwise n _ _ _) (by dsimp only [L]; positivity)
  have habsT (x : ℝ) (hx : x = -T ∨ x = T) : |x| = T := by
    rcases hx with rfl | rfl <;> simp [abs_of_nonneg hT]
  have hH (x : ℝ) (hx : x = -T ∨ x = T) (p : SourcePoissonHeights) (hp : p.2 ∈ Ioc λx σx) :
      ‖sourcePoissonXiHorizontalKernel A x p‖ ≤ H*sourcePoissonHeightMoment n (p.1,x) :=
    habs p.2 x p.1.1 p.1.2 B hp.1.le hp.2 hB.le (habsT x hx).ge
      (hrec' p.2 x hp.1.le (habsT x hx).le)
  have hR (p : SourcePoissonHeights) (hp : p.2 ∈ (Ioc (-T) T)ᶜ) :
      ‖sourcePoissonXiVerticalKernel A σx p‖ ≤ Rt*sourcePoissonHeightMoment n p := by
    have hcutoff : T ≤ |p.2| := by
      by_contra! hh
      exact hp ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩
    have h := sourceRowTwistReciprocal_norm_le_right F hζ S₀ η hJ (f i).val (f i).property hσ
      (s := sourcePoissonVertical σx p.2) (by rw [sourcePoissonVertical_re])
    exact habs σx p.2 p.1.1 p.1.2 Br hab le_rfl hBr.le hcutoff
      (h.trans (le_mul_of_one_le_right hBr.le (Real.one_le_rpow hU (by positivity))))
  have hcL : ContinuousOn (sourcePoissonXiVerticalKernel A λx) (univ ×ˢ Ioc (-T) T) :=
    sourceContinuedPoissonLowKernel_good_continuousOn F S₀ hζ η hJ hcut v f i hu U r hU₀.le hr hi hX hY hZ₀ _
      (fun _ => λx) Prod.snd continuous_const continuous_snd (fun _ _ => le_rfl)
      (fun p hp => (abs_le.mpr ⟨hp.2.1.le,hp.2.2⟩).trans (by linarith))
  have hcH (x : ℝ) (hx : x = -T ∨ x = T) :
      ContinuousOn (sourcePoissonXiHorizontalKernel A x) (univ ×ˢ Ioc λx σx) :=
    sourceContinuedPoissonLowKernel_good_continuousOn F S₀ hζ η hJ hcut v f i hu U r hU₀.le hr hi hX hY hZ₀ _
      Prod.snd (fun _ => x) continuous_snd continuous_const (fun _ hp => hp.2.1.le)
      (fun _ _ => (habsT x hx).le.trans (by linarith))
  have hcR : ContinuousOn (sourcePoissonXiVerticalKernel A σx) (univ ×ˢ (Ioc (-T) T)ᶜ) :=
    (sourceContinuedPoissonRowOnLines_continuous_right F S₀ hζ η hJ v (f i) hcut hu hX hY hZ₀
      σx Cw Cz hσ le_rfl le_rfl).continuousOn
  have Hbound := sourcePoissonFiniteXi_integral_norm_le A hab hT n L H Rt
    (by dsimp only [L]; positivity) (by dsimp only [H]; positivity) (by dsimp only [Rt]; positivity)
    hcL hcH hcR hL hH hR
  rw [sourceContinuedPoissonRowIntegral_finite_good_xi F S₀ hζ η hJ hcut v f i hu U r hU₀.le hr hi hX hY hZ₀, norm_mul]
  calc
    _ ≤ N*(L*sourcePoissonHeightMomentMass 0+2*(H*sourcePoissonHorizontalMass n*(σx-λx))+
        Rt*sourcePoissonHeightMomentMass n) := mul_le_mul_of_nonneg_left Hbound hN
    _ = C₁*P₁+C₂*P₂ := by dsimp only [L,H,Rt,C₁,C₂]; ring
    _ ≤ (C₁+C₂+1)*P₁+(C₁+C₂+1)*P₂ := add_le_add
      (mul_le_mul_of_nonneg_right (by linarith) hP₁) (mul_le_mul_of_nonneg_right (by linarith) hP₂)
    _ = _ := by dsimp only [P₁,P₂,P]; ring

end
end ArtinMatthews.SourceEulerAssembly
