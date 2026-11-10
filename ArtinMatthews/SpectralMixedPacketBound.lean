module

public import ArtinMatthews.SpectralMixedPacketExpansion
public import ArtinMatthews.SpectralABLSourceTestBounds
public import ArtinMatthews.SpectralMixedPacketComplementaryCusp
public import ArtinMatthews.SpectralMixedPacketPrincipalCore
public import ArtinMatthews.SpectralMixedPacketComplementaryResidual
public import ArtinMatthews.SpectralMixedPacketContinuous
public import ArtinMatthews.SpectralMixedPacketPrincipalCusp
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The full nonholomorphic packet retains the principal cusp, continuous,
complementary cusp and finite residual sectors. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

theorem gamma0MixedPacket_small_height_exists {B p a : ℝ}
    (hB : 0 < B) (hp : 0 < p) (ha : 0 < a) :
    ∃ Y : ℝ, 0 < Y ∧ Y < (1/16)/B ∧ Y < (1/16)/p ∧ Y < (a^2/2)/p := by
  let U := (1/16)/B
  let V := (1/16)/p
  let W := (a^2/2)/p
  let M := min U (min V W)
  have hM : 0 < M := lt_min (by dsimp only [U]; positivity)
    (lt_min (by dsimp only [V]; positivity) (by dsimp only [W]; positivity))
  have hY : M/2 < M := by linarith
  exact ⟨M/2,by positivity,hY.trans_le (min_le_left _ _),
    hY.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
    hY.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem gamma0MixedPacket_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (h : SpectralEnergyTest) (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ)
        (hm : ∀ j, m j ≠ 0), Function.Injective m →
      ∀ (n : ℤ) (hn : n ≠ 0) {B Z a H Y : ℝ},
      0 < B → 1 ≤ Z → 0 < a → a ≤ 1 → 0 ≤ H → ∀ hY : 0 < Y,
      Y < (1/16)/B →
      Y < (1/16)/(|cuspFourierFrequency 1 n|/
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      Y < (a^2/2)/(|cuspFourierFrequency 1 n|/
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ j, |cuspFourierFrequency 1 (m j)| ≤ B) →
      spectralABLPrincipalSymbolBound h H Z → spectralABLComplementarySymbolBound h H a →
      let N := r*s
      let S := ∑ j ∈ v, ‖α j‖^2
      ‖gamma0MixedPacketSpectralSide N h (gamma0CuspOneOver s) Y hY n hn v α m hm‖ ≤
        C*H*(gamma0MixedPacketPrincipalSize N B |cuspFourierFrequency 1 n| Z S+
          gamma0MixedPacketExceptionalSize N B n a ε S) := by
  obtain ⟨C₁,hC₁,hCusp⟩ := gamma0MixedPacket_principal_cusp_bound
  obtain ⟨C₂,hC₂,hCont⟩ := gamma0MixedPacket_principal_continuous_bound
  obtain ⟨C₃,hC₃,hComp⟩ := gamma0MixedPacket_complementary_cusp_bound hε
  obtain ⟨C₄,hC₄,hRes⟩ := gamma0MixedPacket_complementary_residual_bound hε
  refine ⟨C₁+C₂+C₃+C₄,by positivity,?_⟩
  intro ι r s ir is hcop h v α m hm hinj n hn B Z a H Y hB hZ ha ha₁ hH hY hYL hYR hYE hfreq hP hE
  let U := gamma0HeatComplementaryCuspidalIndices (r*s)
  let S := ∑ j ∈ v, ‖α j‖^2
  let P := gamma0MixedPacketPrincipalSize (r*s) B |cuspFourierFrequency 1 n| Z S
  let E := gamma0MixedPacketExceptionalSize (r*s) B n a ε S
  let F := gamma0MixedPacketCuspidalTerm (r*s) h (gamma0CuspOneOver s) Y hY n hn v α m hm
  let I := gamma0MixedPacketContinuousIntegrand (r*s) h (gamma0CuspOneOver s) Y hY n hn v α m hm
  let D := gamma0MixedPacketResidualTerm (r*s) h (gamma0CuspOneOver s) n hn v α m hm
  have hYL' : Y < (1/4)/B := hYL.trans_le (div_le_div_of_nonneg_right (by norm_num) hB.le)
  obtain ⟨hs, hp₁⟩ := @hCusp ι r s ir is hcop h v α m hm hinj n hn
    B Z H Y hB hZ hH hY hYL hYR hfreq hP
  have hp₂ := (@hCont ι r s ir is hcop h v α m hm hinj n hn
    B Z H Y hB hZ hH hY hYL hYR hfreq hP).2
  have he₁ := @hComp ι r s ir is hcop h v α m hm hinj n hn
    B a H Y hB ha ha₁ hH hY hYL' hYE hfreq hE
  have he₂ := @hRes ι r s ir is hcop h v α m hm hinj n hn
    B a H hB ha ha₁ hH hfreq hE
  have hSum : Summable F := gamma0HeatCuspidal_summable_of_principal (r*s) F hs.of_norm
  change ‖(∑' i, F i)+((∫ t, I t ∂gamma0EisensteinSpectralMeasure)+
    ∑ l ∈ gamma0ResidualEnergyWindow (r*s), ∑ j, D l j)‖ ≤ (C₁+C₂+C₃+C₄)*H*(P+E)
  rw [gamma0HeatCuspidal_tsum_split (r*s) F hSum]
  have he₁' : ‖∑ i ∈ U, F i‖ ≤ C₃*H*E := (norm_sum_le _ _).trans he₁
  have he₂' : ‖∑ l ∈ gamma0ResidualEnergyWindow (r*s), ∑ j, D l j‖ ≤ C₄*H*E :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun _ _ => norm_sum_le _ _).trans he₂)
  have hp₂' : ‖∫ t, I t ∂gamma0EisensteinSpectralMeasure‖ ≤ C₂*H*P :=
    (norm_integral_le_integral_norm _).trans hp₂
  have hP₀ : 0 ≤ P := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hE₀ : 0 ≤ E := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ C₁*H*P+C₃*H*E+(C₂*H*P+C₄*H*E) :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hp₁ he₁')) ((norm_add_le _ _).trans (add_le_add hp₂' he₂')))
    _ ≤ _ := by
      have hcp : 0 ≤ (C₃+C₄)*H*P := by positivity
      have hce : 0 ≤ (C₁+C₂)*H*E := by positivity
      nlinarith only [hcp,hce]

end ArtinMatthews
