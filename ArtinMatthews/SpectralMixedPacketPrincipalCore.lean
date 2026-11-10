module

public import ArtinMatthews.SpectralMixedPacketPrincipalMass
public import ArtinMatthews.SpectralMixedPacketTerms
public import ArtinMatthews.SpectralPrincipalDecayWeight
public import ArtinMatthews.SpectralPrincipalWeightedSeries
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

/-! The actual principal cusp packet and its mixed singleton satisfy
weighted Cauchy--Schwarz with uniform level and frequency overlap. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0MixedPacketPrincipalSize (N : ℕ) (B q Z S : ℝ) : ℝ :=
  Real.sqrt (S*(Z^2+B*Z/(N : ℝ)))*Real.sqrt (Z^2+q*Z/(N : ℝ))

theorem gamma0CuspidalTestSymbol_eq_principal_frequency (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (i : Gamma0HeatPrincipalCuspidalIndex N) :
    gamma0CuspidalTestSymbol N h i.val =
      spectralContinuousTestSymbol h (gamma0CuspPrincipalParameter N i.val) := by
  rw [gamma0CuspidalTestSymbol,spectralContinuousTestSymbol_apply]
  apply congrArg (fun l : Ici (0 : ℝ) => h l)
  apply Subtype.ext
  change gamma0AllHeightGradientSpectralValue N i.val =
    1/4+(Real.sqrt (gamma0AllHeightGradientSpectralValue N i.val-1/4))^2
  rw [Real.sq_sqrt (sub_nonneg.mpr i.property)]
  ring

theorem gamma0MixedPacket_principal_cusp_bound_of_cutoffs {ι : Type*}
    (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (h : SpectralEnergyTest)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ) (hm : ∀ j, m j ≠ 0)
    (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y)
    {B q C₁ C₂ Z H : ℝ} (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hZ : 1 ≤ Z) (hH : 0 ≤ H)
    (hSym : ∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ ≤
      H*spectralPrincipalDecayWeight Z t/Real.cosh (Real.pi*t))
    (hcutL : ∀ (u : Finset (Gamma0HeatPrincipalCuspidalIndex N)) (R : ℝ), 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|gamma0CuspPrincipalParameter N j.val| ≤ R),
        gamma0InfinityPacketPrincipalDensity N v α m hm Y hY i) ≤
        (C₁*(∑ j ∈ v, ‖α j‖^2))*(R^2+(B/(N : ℝ))*R))
    (hcutR : ∀ (u : Finset (Gamma0HeatPrincipalCuspidalIndex N)) (R : ℝ), 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|gamma0CuspPrincipalParameter N j.val| ≤ R),
        gamma0NativePrincipalDensity N b Y hY n hn i) ≤ C₂*(R^2+(q/(N : ℝ))*R)) :
    let F (i : Gamma0HeatPrincipalCuspidalIndex N) :=
      gamma0MixedPacketCuspidalTerm N h b Y hY n hn v α m hm i.val
    Summable (fun i => ‖F i‖) ∧ ‖∑' i, F i‖ ≤
      (Real.sqrt (8*C₁)*Real.sqrt (8*C₂)/4)*H*
        gamma0MixedPacketPrincipalSize N B q Z (∑ j ∈ v, ‖α j‖^2) := by
  classical
  let S := ∑ j ∈ v, ‖α j‖^2
  let J := Gamma0HeatPrincipalCuspidalIndex N
  let τ (i : J) := gamma0CuspPrincipalParameter N i.val
  let W (t : ℝ) := Real.cosh (Real.pi*t)
  let A (i : J) := gamma0InfinityCuspPacketAmplitude N i.val v α m hm Y hY
  let D (i : J) := gamma0CuspUnitAmplitude N i.val b Y hY n hn
  let f := gamma0InfinityPacketPrincipalDensity N v α m hm Y hY
  let g := gamma0NativePrincipalDensity N b Y hY n hn
  let F (i : J) := gamma0MixedPacketCuspidalTerm N h b Y hY n hn v α m hm i.val
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW (t : ℝ) : 0 < W t := Real.cosh_pos _
  have hf (i : J) : 0 ≤ f i := div_nonneg (sq_nonneg _) (hW _).le
  have hg (i : J) : 0 ≤ g i := div_nonneg (sq_nonneg _) (hW _).le
  have hb (i : J) : ‖F i‖ ≤ (H/4)*spectralPrincipalDecayWeight Z (τ i)*Real.sqrt (f i)*Real.sqrt (g i) := by
    have hp : Real.sqrt (f i)*Real.sqrt (g i) = ‖A i‖*‖D i‖/W (τ i) := by
      change Real.sqrt (‖A i‖^2/W (τ i))*Real.sqrt (‖D i‖^2/W (τ i)) = _
      rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_div (sq_nonneg _),
        Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _),div_mul_div_comm,
        ← pow_two,Real.sq_sqrt (hW _).le]
    have h₀ := hSym (τ i)
    change ‖gamma0CuspidalTestSymbol N h i.val*(D i*star (A i))/4‖ ≤ _
    rw [norm_div,norm_mul,norm_mul,norm_star,show ‖(4 : ℂ)‖ = 4 from Complex.norm_natCast 4,
      gamma0CuspidalTestSymbol_eq_principal_frequency]
    calc
      _ ≤ (H*spectralPrincipalDecayWeight Z (τ i)/W (τ i))*(‖D i‖*‖A i‖)/4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h₀ (by positivity)) (by norm_num)
      _ = _ := by
        rw [mul_assoc ((H/4)*spectralPrincipalDecayWeight Z (τ i)),hp]
        ring
  have hB₁ : 0 ≤ B/(N : ℝ) := by positivity
  have hB₂ : 0 ≤ q/(N : ℝ) := by positivity
  obtain ⟨hs,_,hcross⟩ := spectralPrincipal_cross_summable τ f g F hf hg
    (div_nonneg hH (by norm_num)) hZ hB₁ hB₂ (mul_nonneg hC₁ hS) hC₂ hb
    hcutL hcutR
  refine ⟨hs,hcross.trans_eq ?_⟩
  unfold gamma0MixedPacketPrincipalSize
  have hL : 8*(C₁*S)*(Z^2+(B/(N : ℝ))*Z) = (8*C₁)*(S*(Z^2+B*Z/(N : ℝ))) := by ring
  have hR : 8*C₂*(Z^2+(q/(N : ℝ))*Z) = (8*C₂)*(Z^2+q*Z/(N : ℝ)) := by ring
  rw [hL,hR,Real.sqrt_mul (by positivity : 0 ≤ 8*C₁),Real.sqrt_mul (by positivity : 0 ≤ 8*C₂)]
  ring

end ArtinMatthews
