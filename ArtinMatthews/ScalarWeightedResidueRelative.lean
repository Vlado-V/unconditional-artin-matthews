module

public import ArtinMatthews.ScalarWeightedBonferroni
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Relative finite-residue estimates with an explicit exponential cost budget. -/

namespace ArtinMatthews
open Finset
open OAI.Erdos970.NumberTheoryLean.BonferroniDensity
open scoped BigOperators
noncomputable section

theorem scalarWeightedResidue_relative (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (hf1 : ∀ p ∈ P, ∀ s < p, f p s ≤ 1)
    (r lo hi Q a : ℕ) (hlt : lo < hi) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q)
    (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hcap : ∀ p ∈ P, scalarWeightedResidueMean f p ≤ 2 / 3)
    (hsum : ∑ p ∈ P, scalarWeightedResidueMean f p ≤ Λ)
    (hthreshold : 5 * Λ ≤ ((r + 1 : ℕ) : ℝ) * Real.log 2 / 2) :
    let H := ((hi - lo : ℕ) : ℝ) / Q
    let V := ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)
    |scalarWeightedResidueCount P f lo hi Q a - H * V| / (H * V) ≤
      2 * Real.exp (-((r + 1 : ℕ) : ℝ) * Real.log 2 / 2) +
        scalarWeightedResidueEndpointMass P f (r + 1) / H * Real.exp (3 * Λ) := by
  let H := ((hi - lo : ℕ) : ℝ) / Q
  let V := ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)
  let E := scalarWeightedResidueEndpointMass P f (r + 1)
  let e := elementarySum P (scalarWeightedResidueMean f) (r + 1)
  let C := scalarWeightedResidueCount P f lo hi Q a
  have hH : 0 < H := div_pos (Nat.cast_pos.mpr (Nat.sub_pos_iff_lt.mpr hlt))
    (Nat.cast_pos.mpr hQ)
  have hg0 : ∀ p ∈ P, 0 ≤ scalarWeightedResidueMean f p :=
    fun p hp => scalarWeightedResidueMean_nonneg f (hf0 p hp)
  have hVlower : Real.exp (-3 * Λ) ≤ V :=
    exp_neg_three_mul_le_eulerProduct P _ hg0 hcap hsum
  have hV : 0 < V := (Real.exp_pos _).trans_le hVlower
  have hE : 0 ≤ E := sum_nonneg (fun k _ => elementarySum_nonneg P _
    (fun p hp => scalarWeightedResidueMass_nonneg f (hf0 p hp)) k)
  have htail : e / V ≤ Real.exp (-((r + 1 : ℕ) : ℝ) * Real.log 2 / 2) :=
    relative_elementarySum_le_exp_decay P _ hg0 hcap hΛ hsum (r + 1) hthreshold
  have hfinite := scalarWeightedResidue_error_by_layers P f hP hf0 hf1
    r lo hi Q a hlt.le hQ hcop
  change |C - H * V| ≤ 2 * H * e + E at hfinite
  have hend : E / H / V ≤ E / H * Real.exp (3 * Λ) := by
    calc
      _ ≤ E / H / Real.exp (-3 * Λ) :=
        div_le_div_of_nonneg_left (div_nonneg hE hH.le) (Real.exp_pos _) hVlower
      _ = _ := by
        rw [show -3 * Λ = -(3 * Λ) by ring, Real.exp_neg, div_inv_eq_mul]
  change |C - H * V| / (H * V) ≤ _
  calc
    _ ≤ (2 * H * e + E) / (H * V) :=
      div_le_div_of_nonneg_right hfinite (mul_pos hH hV).le
    _ = 2 * (e / V) + E / H / V := by field_simp [hH.ne', hV.ne']
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num)) hend

theorem scalarWeightedResidue_relative_exponential (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (hf1 : ∀ p ∈ P, ∀ s < p, f p s ≤ 1)
    (r lo hi Q a : ℕ) (hQ : 0 < Q) (hcop : ∀ p ∈ P, p.Coprime Q)
    (Λ L γ qcost ecost : ℝ) (hΛ : 0 ≤ Λ)
    (hcap : ∀ p ∈ P, scalarWeightedResidueMean f p ≤ 2 / 3)
    (hsum : ∑ p ∈ P, scalarWeightedResidueMean f p ≤ Λ)
    (hthreshold : 5 * Λ ≤ ((r + 1 : ℕ) : ℝ) * Real.log 2 / 2)
    (hlength : Real.exp (γ * L) ≤ ((hi - lo : ℕ) : ℝ))
    (hmodulus : (Q : ℝ) ≤ Real.exp qcost)
    (hcost : scalarWeightedResidueEndpointMass P f (r + 1) ≤ Real.exp ecost) :
    let H := ((hi - lo : ℕ) : ℝ) / Q
    let V := ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)
    |scalarWeightedResidueCount P f lo hi Q a - H * V| / (H * V) ≤
      2 * Real.exp (-((r + 1 : ℕ) : ℝ) * Real.log 2 / 2) +
        Real.exp (ecost + qcost + 3 * Λ - γ * L) := by
  let H := ((hi - lo : ℕ) : ℝ) / Q
  let E := scalarWeightedResidueEndpointMass P f (r + 1)
  have hlen : 0 < ((hi - lo : ℕ) : ℝ) := (Real.exp_pos _).trans_le hlength
  have hlt : lo < hi := Nat.sub_pos_iff_lt.mp (Nat.cast_pos.mp hlen)
  have hQ0 : 0 < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hnum : E * Q ≤ Real.exp ecost * Real.exp qcost :=
    mul_le_mul hcost hmodulus (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hratio : E * Q / ((hi - lo : ℕ) : ℝ) ≤
      (Real.exp ecost * Real.exp qcost) / Real.exp (γ * L) :=
    div_le_div₀ (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      hnum (Real.exp_pos _) hlength
  have hend : E / H * Real.exp (3 * Λ) ≤ Real.exp (ecost + qcost + 3 * Λ - γ * L) := by
    calc
      _ = (E * Q / ((hi - lo : ℕ) : ℝ)) * Real.exp (3 * Λ) := by
        dsimp [H]
        field_simp [hlen.ne', hQ0.ne']
      _ ≤ ((Real.exp ecost * Real.exp qcost) / Real.exp (γ * L)) * Real.exp (3 * Λ) :=
        mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg _)
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
        congr 1
        ring
  exact (scalarWeightedResidue_relative P f hP hf0 hf1 r lo hi Q a hlt hQ hcop
    Λ hΛ hcap hsum hthreshold).trans (add_le_add le_rfl hend)

theorem scalarWeightedResidue_relative_budget (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (hf1 : ∀ p ∈ P, ∀ s < p, f p s ≤ 1)
    (r lo hi Q a : ℕ) (hQ : 0 < Q) (hcop : ∀ p ∈ P, p.Coprime Q)
    (Λ L γ qcost ecost : ℝ) (hΛ : 0 ≤ Λ)
    (hcap : ∀ p ∈ P, scalarWeightedResidueMean f p ≤ 2 / 3)
    (hsum : ∑ p ∈ P, scalarWeightedResidueMean f p ≤ Λ)
    (hthreshold : 5 * Λ ≤ ((r + 1 : ℕ) : ℝ) * Real.log 2 / 2)
    (hlength : Real.exp (γ * L) ≤ ((hi - lo : ℕ) : ℝ))
    (hmodulus : (Q : ℝ) ≤ Real.exp qcost)
    (hcost : scalarWeightedResidueEndpointMass P f (r + 1) ≤ Real.exp ecost)
    (hbudget : ecost + qcost + 3 * Λ ≤ γ * L / 2) :
    let H := ((hi - lo : ℕ) : ℝ) / Q
    let V := ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)
    |scalarWeightedResidueCount P f lo hi Q a - H * V| / (H * V) ≤
      2 * Real.exp (-((r + 1 : ℕ) : ℝ) * Real.log 2 / 2) + Real.exp (-γ * L / 2) := by
  apply (scalarWeightedResidue_relative_exponential P f hP hf0 hf1 r lo hi Q a hQ hcop
    Λ L γ qcost ecost hΛ hcap hsum hthreshold hlength hmodulus hcost).trans
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  linarith

theorem scalarWeightedResidue_relative_budget_Ico (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (hf1 : ∀ p ∈ P, ∀ s < p, f p s ≤ 1)
    (r lo hi Q a : ℕ) (hlo1 : 1 ≤ lo) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q)
    (Λ L γ qcost ecost : ℝ) (hΛ : 0 ≤ Λ)
    (hcap : ∀ p ∈ P, scalarWeightedResidueMean f p ≤ 2 / 3)
    (hsum : ∑ p ∈ P, scalarWeightedResidueMean f p ≤ Λ)
    (hthreshold : 5 * Λ ≤ ((r + 1 : ℕ) : ℝ) * Real.log 2 / 2)
    (hlength : Real.exp (γ * L) ≤ ((hi - lo : ℕ) : ℝ))
    (hmodulus : (Q : ℝ) ≤ Real.exp qcost)
    (hcost : scalarWeightedResidueEndpointMass P f (r + 1) ≤ Real.exp ecost)
    (hbudget : ecost + qcost + 3 * Λ ≤ γ * L / 2) :
    let H := ((hi - lo : ℕ) : ℝ) / Q
    let V := ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)
    |scalarWeightedResidueCountIco P f lo hi Q a - H * V| / (H * V) ≤
      2 * Real.exp (-((r + 1 : ℕ) : ℝ) * Real.log 2 / 2) + Real.exp (-γ * L / 2) := by
  have hlt : lo < hi := Nat.sub_pos_iff_lt.mp
    (Nat.cast_pos.mp ((Real.exp_pos _).trans_le hlength))
  have hinterval : Ioc (lo - 1) (hi - 1) = Ico lo hi := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  have hlen : hi - 1 - (lo - 1) = hi - lo := by omega
  have hcount : scalarWeightedResidueCount P f (lo - 1) (hi - 1) Q a =
      scalarWeightedResidueCountIco P f lo hi Q a := by
    simp only [scalarWeightedResidueCount, scalarWeightedResidueCountIco,
      scalarForcedResidueInterval, hinterval]
  have hlength' : Real.exp (γ * L) ≤ ((hi - 1 - (lo - 1) : ℕ) : ℝ) := by
    simpa only [hlen] using hlength
  simpa only [hcount, hlen] using scalarWeightedResidue_relative_budget P f hP hf0 hf1
    r (lo - 1) (hi - 1) Q a hQ hcop Λ L γ qcost ecost hΛ hcap hsum hthreshold
      hlength' hmodulus hcost hbudget

theorem scalarWeightedRankDepth_exp (h : ℕ) (L A N : ℝ) (hL : 0 < L)
    (hdepth : 2 * A * N * Real.log L ≤ (h : ℝ) * Real.log 2) :
    Real.exp (-(h : ℝ) * Real.log 2 / 2) ≤ L ^ (-A * N) := by
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem scalarWeightedResidue_relative_rank_budget_Ico (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (hf1 : ∀ p ∈ P, ∀ s < p, f p s ≤ 1)
    (r lo hi Q a : ℕ) (hlo1 : 1 ≤ lo) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q)
    (Λ L γ qcost ecost A N : ℝ) (hΛ : 0 ≤ Λ) (hL : 0 < L)
    (hcap : ∀ p ∈ P, scalarWeightedResidueMean f p ≤ 2 / 3)
    (hsum : ∑ p ∈ P, scalarWeightedResidueMean f p ≤ Λ)
    (hthreshold : 5 * Λ ≤ ((r + 1 : ℕ) : ℝ) * Real.log 2 / 2)
    (hlength : Real.exp (γ * L) ≤ ((hi - lo : ℕ) : ℝ))
    (hmodulus : (Q : ℝ) ≤ Real.exp qcost)
    (hcost : scalarWeightedResidueEndpointMass P f (r + 1) ≤ Real.exp ecost)
    (hbudget : ecost + qcost + 3 * Λ ≤ γ * L / 2)
    (hdepth : 2 * A * N * Real.log L ≤ ((r + 1 : ℕ) : ℝ) * Real.log 2) :
    let H := ((hi - lo : ℕ) : ℝ) / Q
    let V := ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)
    |scalarWeightedResidueCountIco P f lo hi Q a - H * V| / (H * V) ≤
      2 * L ^ (-A * N) + Real.exp (-γ * L / 2) := by
  apply (scalarWeightedResidue_relative_budget_Ico P f hP hf0 hf1 r lo hi Q a hlo1 hQ hcop
    Λ L γ qcost ecost hΛ hcap hsum hthreshold hlength hmodulus hcost hbudget).trans
  exact add_le_add (mul_le_mul_of_nonneg_left
    (scalarWeightedRankDepth_exp (r + 1) L A N hL hdepth) (by norm_num : (0 : ℝ) ≤ 2)) le_rfl

end
end ArtinMatthews
