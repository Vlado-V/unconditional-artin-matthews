module

public import ArtinMatthews.GiantTwoSidedPatternDilationBound
public import ArtinMatthews.GiantTwoSidedPatternPathOffsets
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

/-! A fixed label path determines signed increments before a root is
chosen. The literal source moment length and actual prime ranges give
subpower bounds for every partial displacement. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section

def giantTwoSidedPermuteLabels {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (π : J → Equiv.Perm (Fin M)) (a : MarkedPhysicalMarking P M) : MarkedPhysicalMarking P M :=
  fun j i => a j (π j i)

def giantTwoSidedLabelIncrement {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
    (π : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) (i : Fin n) : ℤ :=
  step i*(giantTwoSidedPatternDilation (C i) (giantTwoSidedPermuteLabels (π i) (labels i.castSucc)) (aux i):ℤ)

theorem giantTwoSidedLabelIncrement_eq_physical {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)} {Z : Finset ℕ}
    (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z)
    (π : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) :
    giantTwoSidedLabelIncrement C (fun i => (s i).val.2) π aux step =
      giantTwoSidedPatternPathIncrement s π aux step := rfl

theorem giantTwoSidedPathOffset_abs_le {n : ℕ} (δ : Fin n → ℤ) {B : ℝ}
    (hB : 0 ≤ B) (hδ : ∀ i,|(δ i:ℝ)|≤B) (v : Fin (n+1)) :
    |(giantTwoSidedPathOffset δ v:ℝ)| ≤ (n:ℝ)*B := by
  classical
  unfold giantTwoSidedPathOffset
  rw [Int.cast_sum]
  calc
    _ ≤ ∑ i∈(univ : Finset (Fin n)).filter (fun i => i.val < v.val),|(δ i:ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈(univ : Finset (Fin n)).filter (fun i => i.val < v.val),B := sum_le_sum fun i _ => hδ i
    _ ≤ (n:ℝ)*B := by
      rw [sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast (card_filter_le univ (fun i : Fin n => i.val < v.val)).trans_eq (card_fin n)

def giantTwoSidedSourceMomentLength (x : ℝ) : ℕ := 2*⌈(Real.log x)^(13/25:ℝ)⌉₊

theorem giantTwoSidedSourceMomentLength_le {x : ℝ} (hL : 1≤Real.log x) :
    (giantTwoSidedSourceMomentLength x:ℝ) ≤ 4*(Real.log x)^(13/25:ℝ) := by
  have hy : 1 ≤ (Real.log x)^(13/25:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hc := (Nat.ceil_lt_add_one (Real.rpow_nonneg (zero_le_one.trans hL) (13/25:ℝ))).le
  unfold giantTwoSidedSourceMomentLength
  push_cast
  linarith

theorem giantCandidateLabelOffsets_subpower (k : ℕ) (C₂ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ (ell : ℕ) (C : Fin n → S → Finset (Fin k))
        (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
        (π : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) → ∀ v : Fin (n+1),
          |(giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) v:ℝ)| ≤ x^δ := by
  have hδ2 : 0<δ/2 := half_pos hδ
  have hpoly := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (13/25+C₂) (δ/2) hδ2).const_mul 4).comp
    Real.tendsto_log_atTop
  simp only [mul_zero] at hpoly
  filter_upwards [giantCandidatePatternDilation_subpower k hδ2,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
    hpoly.eventually (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))]
    with x hD hx hL hsmall
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  let n := giantTwoSidedSourceMomentLength x
  dsimp only
  intro ell C labels π aux step hstep v
  have hx0 : 0<x := zero_lt_one.trans hx
  have hL0 : 0<Real.log x := zero_lt_one.trans_le hL
  have hpolynomial : 4*(Real.log x)^(13/25+C₂) ≤ x^(δ/2) := by
    rw [Real.rpow_def_of_pos hx0]
    apply (div_le_one (Real.exp_pos _)).mp
    change 4*((Real.log x)^(13/25+C₂)*Real.exp (-(δ/2)*Real.log x))<1 at hsmall
    have hexp : Real.exp (-(δ/2)*Real.log x)=(Real.exp (Real.log x*(δ/2)))⁻¹ := by
      rw [show -(δ/2)*Real.log x=-(Real.log x*(δ/2)) by ring,Real.exp_neg]
    rw [hexp] at hsmall
    simpa only [div_eq_mul_inv,mul_assoc] using hsmall.le
  have hincr (i : Fin n) : |(giantTwoSidedLabelIncrement C labels π aux step i:ℝ)| ≤
      (Real.log x)^C₂*x^(δ/2) := by
    unfold giantTwoSidedLabelIncrement
    rw [Int.cast_mul,Int.cast_natCast,abs_mul]
    have hAbsD : |(giantTwoSidedPatternDilation (C i)
        (giantTwoSidedPermuteLabels (π i) (labels i.castSucc)) (aux i):ℝ)| =
        (giantTwoSidedPatternDilation (C i)
          (giantTwoSidedPermuteLabels (π i) (labels i.castSucc)) (aux i):ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [hAbsD]
    have habs : |(step i:ℝ)|=((step i).natAbs:ℝ) := by rw [Nat.cast_natAbs,Int.cast_abs]
    rw [habs]
    exact mul_le_mul (hstep i) (hD S ell (C i) (giantTwoSidedPermuteLabels (π i) (labels i.castSucc)) (aux i))
      (Nat.cast_nonneg _) (Real.rpow_nonneg hL0.le _)
  calc
    _ ≤ (n:ℝ)*((Real.log x)^C₂*x^(δ/2)) :=
      giantTwoSidedPathOffset_abs_le _ (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hx0.le _)) hincr v
    _ ≤ (4*(Real.log x)^(13/25:ℝ))*((Real.log x)^C₂*x^(δ/2)) :=
      mul_le_mul_of_nonneg_right (giantTwoSidedSourceMomentLength_le hL) (by positivity)
    _ = (4*(Real.log x)^(13/25+C₂))*x^(δ/2) := by rw [Real.rpow_add hL0]; ring
    _ ≤ x^(δ/2)*x^(δ/2) := mul_le_mul_of_nonneg_right hpolynomial (Real.rpow_nonneg hx0.le _)
    _ = x^δ := by rw [← Real.rpow_add hx0]; congr 1; ring

end
end ArtinMatthews
