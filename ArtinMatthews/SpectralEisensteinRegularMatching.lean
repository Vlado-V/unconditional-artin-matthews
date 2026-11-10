module

public import ArtinMatthews.SpectralEisensteinMatchedTruncated
public import ArtinMatthews.SpectralEisensteinForcingAnalytic
public import ArtinMatthews.SpectralEisensteinMatchingModes
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

/-! The actual matched families are analytic at parameters where the
truncated pencil and the finite matching determinant are regular. -/
noncomputable section
open Set Filter Topology Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0EisensteinMatchingRegular (N : ℕ) [NeZero N] (s : ℂ) : Prop :=
  s*(1-s)∉(gamma0EisensteinMatchingForm N).exceptional ∧
    (gamma0EisensteinMatchingMatrix N s).det≠0

theorem gamma0EisensteinMatchingResponse_analyticAt_nonexceptional (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : s*(1-s)∉(gamma0EisensteinMatchingForm N).exceptional) :
    AnalyticAt ℂ (gamma0EisensteinMatchingResponse N a) s := by
  let A := (gamma0EisensteinMatchingForm N).energyResolvent
  have hA : AnalyticAt ℂ (fun w : ℂ => A (w*(1-w))) s :=
    ((gamma0EisensteinMatchingForm N).energyResolvent_analyticAt (s*(1-s)) hs).comp
      (f := fun w : ℂ => w*(1-w)) (analyticAt_id.mul (analyticAt_const.sub analyticAt_id))
  exact spectralAnalytic_clmApply _ _ s hA (gamma0CuspEisensteinCompactForcingMass_analyticAt N a s)

theorem gamma0EisensteinMatchingDefect_analyticAt_nonexceptional (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : s*(1-s)∉(gamma0EisensteinMatchingForm N).exceptional) :
    AnalyticAt ℂ (gamma0EisensteinMatchingDefect N a) s := by
  let B := (gamma0EnergyMassAdjoint N).comp (gamma0EnergyInclusion N)
  have hU := gamma0EisensteinMatchingResponse_analyticAt_nonexceptional N a s hs
  have hB := (B.analyticAt _).comp hU
  have hscalar : AnalyticAt ℂ (fun w : ℂ => w*(1-w)+1) s :=
    (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).add analyticAt_const
  have hF := ((gamma0EnergyMassAdjoint N).analyticAt _).comp
    (gamma0CuspEisensteinCompactForcingMass_analyticAt N a s)
  exact (hU.sub (hscalar.smul hB)).sub hF

theorem gamma0EisensteinOutgoingDefect_analyticAt_nonexceptional (N : ℕ) [NeZero N]
    (s : ℂ) (hs : s*(1-s)∉(gamma0EisensteinMatchingForm N).exceptional)
    (j : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0EisensteinOutgoingDefect N w j) s := by
  have hq : (1-s)*(1-(1-s))∉(gamma0EisensteinMatchingForm N).exceptional := by
    rwa [gamma0Eisenstein_reflect_parameter]
  exact (gamma0EisensteinMatchingDefect_analyticAt_nonexceptional N
    (gamma0EisensteinCuspClassRepresentative N j) (1-s) hq).comp
      (f := fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id)

theorem spectralMatrixDet_analyticAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℂ → Matrix ι ι ℂ) (s : ℂ) (hA : ∀ i j, AnalyticAt ℂ (fun w => A w i j) s) :
    AnalyticAt ℂ (fun w => (A w).det) s := by
  simp_rw [Matrix.det_apply']
  exact Finset.univ.analyticAt_fun_sum (fun σ _ => analyticAt_const.mul
    (Finset.univ.analyticAt_fun_prod (fun j _ => hA (σ j) j)))

theorem gamma0EisensteinMatchingMatrix_entry_analyticAt_nonexceptional (N : ℕ) [NeZero N]
    (s : ℂ) (hs : s*(1-s)∉(gamma0EisensteinMatchingForm N).exceptional)
    (i j : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0EisensteinMatchingMatrix N w i j) s :=
  ((innerSL ℂ (gamma0EisensteinOutgoingDefect N 2 i)).analyticAt _).comp
    (gamma0EisensteinOutgoingDefect_analyticAt_nonexceptional N s hs j)

theorem gamma0EisensteinMatchingMatrix_det_analyticAt_nonexceptional (N : ℕ) [NeZero N]
    (s : ℂ) (hs : s*(1-s)∉(gamma0EisensteinMatchingForm N).exceptional) :
    AnalyticAt ℂ (fun w => (gamma0EisensteinMatchingMatrix N w).det) s :=
  spectralMatrixDet_analyticAt _ s (gamma0EisensteinMatchingMatrix_entry_analyticAt_nonexceptional N s hs)

theorem gamma0EisensteinMatchingCandidate_analyticAt_regular (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) (i : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0EisensteinMatchingCandidate N a w i) s := by
  have hcol : AnalyticAt ℂ (fun w => ((gamma0EisensteinMatchingMatrix N w).updateCol i
      (gamma0EisensteinMatchingRhs N a w)).det) s := by
    apply spectralMatrixDet_analyticAt
    intro j k
    by_cases h : k=i
    · have hr : AnalyticAt ℂ (fun w => inner ℂ (gamma0EisensteinOutgoingDefect N 2 j)
          (gamma0EisensteinMatchingDefect N a w)) s :=
        ((innerSL ℂ (gamma0EisensteinOutgoingDefect N 2 j)).analyticAt _).comp
          (gamma0EisensteinMatchingDefect_analyticAt_nonexceptional N a s hs.1)
      have hn : AnalyticAt ℂ (fun w => -inner ℂ (gamma0EisensteinOutgoingDefect N 2 j)
          (gamma0EisensteinMatchingDefect N a w)) s := hr.neg
      simpa only [Matrix.updateCol_apply,ite_eq_left h,gamma0EisensteinMatchingRhs] using hn
    · simpa only [Matrix.updateCol_apply,ite_eq_right h] using
        gamma0EisensteinMatchingMatrix_entry_analyticAt_nonexceptional N s hs.1 j k
  have hd := gamma0EisensteinMatchingMatrix_det_analyticAt_nonexceptional N s hs.1
  simpa only [gamma0EisensteinMatchingCandidate,Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply,Pi.inv_apply] using
    (hd.inv hs.2).fun_mul hcol

theorem gamma0CuspScatteringMeromorphic_analyticAt_regular (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) :
    AnalyticAt ℂ (gamma0CuspScatteringMeromorphic N r a) s := by
  apply (gamma0EisensteinMatchingCandidate_analyticAt_regular N a s hs (gamma0EisensteinCuspClass N r)).congr
  have hd := gamma0EisensteinMatchingMatrix_det_analyticAt_nonexceptional N s hs.1
  filter_upwards [hd.continuousAt.eventually_ne hs.2] with w hw
  by_cases h : w∈gamma0EisensteinContinuationDomain
  · rw [gamma0CuspScatteringMeromorphic_eq_offcut N r a w h,gamma0EisensteinMatchingCandidate_eq_true N a w h hw]
    exact (gamma0CuspScatteringContinued_equivalent_target N r _ a
      (gamma0EisensteinCuspClassRepresentative_equivalent N r) w h).symm
  · simp only [gamma0CuspScatteringMeromorphic,ite_eq_right h]

theorem gamma0EisensteinMatchedDefect_analyticAt_regular (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) :
    AnalyticAt ℂ (gamma0EisensteinMatchedDefect N a) s :=
  (gamma0EisensteinMatchingDefect_analyticAt_nonexceptional N a s hs.1).add
    (Finset.univ.analyticAt_fun_sum (fun j _ =>
      (gamma0CuspScatteringMeromorphic_analyticAt_regular N (gamma0EisensteinCuspClassRepresentative N j) a s hs).smul
        (gamma0EisensteinOutgoingDefect_analyticAt_nonexceptional N s hs.1 j)))

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_regular (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0CuspEisensteinMatchedTruncatedEnergy N a s)=
      gamma0EnergyMassAdjoint N (gamma0EisensteinMatchedForcing N a s) := by
  have hc := (gamma0EisensteinMatchedDefect_analyticAt_regular N a s hs).continuousAt
  have hz : Tendsto (gamma0EisensteinMatchedDefect N a) (𝓝[≠] s) (𝓝 (0:gamma0EnergySpace N)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [gamma0EisensteinMatchedDefect_eventually_zero N a s] with w hw
    exact hw.symm
  have he := tendsto_nhds_unique hc.continuousWithinAt.tendsto hz
  have hp := gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_defect N a s
  rw [he,neg_zero] at hp
  exact sub_eq_zero.mp hp

end ArtinMatthews
