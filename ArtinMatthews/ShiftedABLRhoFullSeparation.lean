module

public import ArtinMatthews.ShiftedABLRhoModulusSupport
public import ArtinMatthews.ShiftedABLRhoSignedSeparation
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Extend the separated common test to its actual full finite modulus
support. The added terms have zero original weight after integration. -/

noncomputable section
open Set MeasureTheory OAI
open scoped BigOperators
namespace ArtinMatthews

def shiftedABLFullSeparatedSignedSum (χ : SevenEighths.HeckeFamily.Character)
    (D m3 m4 F r L : ℕ) (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) (t : ℝ) : ℂ :=
  let R := (2 : ℝ)^i.1
  let n := shiftedABLFirstIndex m3 m4
  let u := t+shiftedABLRhoHeight z
  ∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter (fun ρ => shiftedABLSignedFrequencyIndex ρ = i),
    (shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z*shiftedABLRhoBlockPhase R u ρ)*
      ∑ c ∈ shiftedABLCommonModuli r L,
        shiftedABLMellinKloosterman (F*c) m3 m4 ρ/(c : ℂ)*
          shiftedABLRhoCommonTest (shiftedABLRhoBlockScale L n r R) u (shiftedABLRhoOrbitalArgument F n r ρ c)

theorem shiftedABLMellinSignedSum_full_rho_separation (χ : SevenEighths.HeckeFamily.Character)
    (D m3 m4 F r L : ℕ) (hne : m3 ≠ m4) (hF : 0 < F) (hr : 0 < r) (hL : 0 < L)
    (hcop : r.Coprime F) (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) :
    Integrable (fun t : ℝ => shiftedABLRhoFourierDensity t*
      shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t) ∧
    shiftedABLMellinSignedSum χ D m3 m4 F r L d i z =
      ∫ t : ℝ, shiftedABLRhoFourierDensity t*shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t := by
  let U := (shiftedABLDualFrequencies m3 m4 d).filter (fun ρ => shiftedABLSignedFrequencyIndex ρ = i)
  let C := shiftedABLCommonModuli r L
  let R := (2 : ℝ)^i.1
  let n := shiftedABLFirstIndex m3 m4
  let a := shiftedABLRhoBlockScale L n r R
  let x (ρ : ℤ) (c : ℕ) := shiftedABLRhoOrbitalArgument F n r ρ c
  let α (ρ : ℤ) := shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z
  let S (ρ : ℤ) (c : ℕ) := shiftedABLMellinKloosterman (F*c) m3 m4 ρ/(c : ℂ)
  let V (ρ : ℤ) (c : ℕ) (t : ℝ) :=
    shiftedABLRhoFourierDensity t*shiftedABLRhoBlockPhase R (t+shiftedABLRhoHeight z) ρ*
      shiftedABLRhoCommonTest a (t+shiftedABLRhoHeight z) (x ρ c)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hn : 0 < n := Int.natAbs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  have hV (ρ : ℤ) (c : ℕ) : Integrable (V ρ c) :=
    shiftedABLRhoFourierTest_integrable a (shiftedABLRhoLogShift R (ρ.natAbs : ℝ)) (x ρ c)
      (shiftedABLRhoHeight z)
  have hEq (ρ : ℤ) (hρu : ρ ∈ U) (c : ℕ) (hc : c ∈ C) :
      shiftedABLMellinModulusWeight F L z c = ∫ t : ℝ, V ρ c t := by
    have hc₀ : 0 < (c : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
    obtain ⟨hnz,hlo,hhi⟩ := shiftedABLRhoSignedBlock_band hρu
    exact shiftedABLMellinModulusWeight_rho_separation hF hL hn hr z hR hnz hlo hhi hc₀
  have hfun : (fun t : ℝ => shiftedABLRhoFourierDensity t*
      shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t) =
      fun t => ∑ ρ ∈ U, ∑ c ∈ C, (α ρ*S ρ c)*V ρ c t := by
    funext t
    unfold shiftedABLFullSeparatedSignedSum
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [← mul_assoc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [α,S,V,x,a,n,R]
    ring
  rw [hfun]
  have hI (ρ : ℤ) (c : ℕ) : Integrable (fun t => (α ρ*S ρ c)*V ρ c t) :=
    (hV ρ c).const_mul _
  refine ⟨integrable_finsetSum U (fun ρ _ => integrable_finsetSum C (fun c _ => hI ρ c)),?_⟩
  rw [integral_finsetSum U (fun ρ _ => integrable_finsetSum C (fun c _ => hI ρ c))]
  unfold shiftedABLMellinSignedSum
  have hCircle : shiftedABLMellinModuli F r L ⊆ C := shiftedABLMellinModuli_subset_common hF hL
  rw [Finset.sum_subset hCircle (fun c hc hout => by
    rw [shiftedABLMellinModulusWeight_zero_off_circle hF hL hcop (Finset.mem_filter.mp hc).2 hout,
      zero_div,zero_mul])]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρu
  rw [integral_finsetSum C (fun c _ => hI ρ c)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [integral_const_mul,← hEq ρ hρu c hc]
  dsimp only [α,S]
  ring

end ArtinMatthews
