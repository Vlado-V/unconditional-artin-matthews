module

public import ArtinMatthews.SpectralInfinityComplementaryResidual
public import ArtinMatthews.SpectralABLResidualExceptionalMoment
public import ArtinMatthews.SpectralComplementaryCosineCross
public import ArtinMatthews.SpectralInfinityResidualGap
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

/-! The complete finite residual packet obeys the source-normalized
cosine Cauchy--Schwarz bound, including its zero-energy entries. -/
namespace ArtinMatthews
open Set
open scoped MatrixGroups BigOperators
noncomputable section

theorem gamma0Infinity_complementary_residual_cross_bound
    {ι : Type*} (N : ℕ) [NeZero N] (v : Finset ι) (α : ι → ℂ)
    (m : ι → ℤ) (hm : ∀ k, m k ≠ 0) (b : SL(2, ℤ))
    (n : ℤ) (hn : n ≠ 0) (h : SpectralEnergyTest)
    {a H : ℝ} (ha : 0 < a) (hH : 0 ≤ H)
    (hbound : ∀ l : Ici (0 : ℝ), 3/16 ≤ (l : ℝ) → (l : ℝ) ≤ 1/4 →
      ‖h l‖ ≤ H*a^(-2*Real.sqrt (1/4-(l : ℝ)))/
        Real.cos (Real.pi*Real.sqrt (1/4-(l : ℝ)))) :
    (∑ l ∈ gamma0ResidualEnergyWindow N,
      ∑ j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)),
        ‖h l*((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j b n hn *
          star (gamma0InfinityResidualPacketRho N l j v α m hm))‖) ≤
      H*Real.sqrt (gamma0InfinityResidualPacketMoment N v α m hm)*
        Real.sqrt (gamma0ResidualCosineExceptionalMoment N b n hn a) := by
  classical
  let J (l : Ici (0 : ℝ)) := Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))
  let u : Finset (Σ l : Ici (0 : ℝ), J l) :=
    (gamma0ResidualEnergyWindow N).sigma (fun _ => Finset.univ)
  let κ (i : Σ l : Ici (0 : ℝ), J l) := Real.sqrt (1/4-(i.1 : ℝ))
  let L (i : Σ l : Ici (0 : ℝ), J l) :=
    gamma0InfinityResidualPacketRho N i.1 i.2 v α m hm
  let R (i : Σ l : Ici (0 : ℝ), J l) :=
    (Real.sqrt |(n : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N i.1 i.2 b n hn
  have hcos (i : Σ l : Ici (0 : ℝ), J l) (_ : i ∈ u) :
      0 ≤ Real.cos (Real.pi*κ i) := by
    have hk₀ : 0 ≤ κ i := Real.sqrt_nonneg _
    have hl₀ : 0 ≤ (i.1 : ℝ) := i.1.property
    have hk : κ i ≤ 1/2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [hl₀]⟩
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  have hgap (i : Σ l : Ici (0 : ℝ), J l) (hL : L i ≠ 0) : 3/16 ≤ (i.1 : ℝ) := by
    by_contra hg
    apply hL
    change (∑ k ∈ v, star (α k)*((Real.sqrt |(m k : ℝ)| : ℂ)*
      gamma0ResidualABLSourceRho N i.1 i.2 1 (m k) (hm k))) = 0
    apply Finset.sum_eq_zero
    intro k _
    have hρ : gamma0ResidualABLSourceRho N i.1 i.2 1 (m k) (hm k) = 0 := by
      by_contra hρ
      exact hg (gamma0Infinity_residual_value_ge_three_sixteenths_of_rho
        N i.1 i.2 (m k) (hm k) hρ)
    simp only [hρ,mul_zero]
  have hb (i : Σ l : Ici (0 : ℝ), J l) (hi : i ∈ u) (hL : L i ≠ 0) :
      ‖h i.1‖ ≤ H*a^(-2*κ i)/Real.cos (Real.pi*κ i) := by
    have hl : i.1 ∈ gamma0ResidualEnergyWindow N := (Finset.mem_sigma.mp hi).1
    exact hbound i.1 (hgap i hL) ((mem_gamma0ResidualEnergyWindow N i.1).mp hl).1.2
  have hc := spectralComplementary_cosine_cross_finset u κ L R
    (fun i => h i.1) ha hH hcos hb
  simpa only [u,Finset.sum_sigma,κ,L,R,gamma0InfinityResidualPacketMoment,
    gamma0ResidualCosineExceptionalMoment] using hc

end
end ArtinMatthews
