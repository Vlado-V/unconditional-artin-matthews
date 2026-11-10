module

public import ArtinMatthews.SpectralEisensteinMeromorphicScattering
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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

/-! The actual meromorphic truncated part and full weak defect after
matching. The defect is identically zero as a meromorphic germ, by its
proved equality on the original open resolvent domain. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0EisensteinMatchedCoefficient (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (i : Gamma0EisensteinCuspClasses N) : ℂ :=
  gamma0CuspScatteringMeromorphic N (gamma0EisensteinCuspClassRepresentative N i) a s

theorem gamma0EisensteinMatchedCoefficient_meromorphic (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (i : Gamma0EisensteinCuspClasses N) :
    Meromorphic (fun s => gamma0EisensteinMatchedCoefficient N a s i) :=
  gamma0CuspScatteringMeromorphic_meromorphic N _ a

theorem gamma0EisensteinMatchedCoefficient_eq_offcut (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) (i : Gamma0EisensteinCuspClasses N) :
    gamma0EisensteinMatchedCoefficient N a s i=gamma0EisensteinMatchingTrueCoefficient N a s i :=
  gamma0CuspScatteringMeromorphic_eq_offcut N _ a s hs

def gamma0CuspEisensteinMatchedTruncatedEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) : gamma0EnergySpace N :=
  -gamma0EisensteinMatchingResponse N a s-
    ∑ i, gamma0EisensteinMatchedCoefficient N a s i •
      gamma0EisensteinMatchingResponse N (gamma0EisensteinCuspClassRepresentative N i) (1-s)

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_meromorphic (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) : Meromorphic (gamma0CuspEisensteinMatchedTruncatedEnergy N a) := by
  intro s
  have hreflect (i : Gamma0EisensteinCuspClasses N) : MeromorphicAt
      (fun w => gamma0EisensteinMatchingResponse N (gamma0EisensteinCuspClassRepresentative N i) (1-w)) s :=
    (gamma0EisensteinMatchingResponse_meromorphic N (gamma0EisensteinCuspClassRepresentative N i)
      (1-s)).comp_analyticAt (g := fun w : ℂ => 1-w) (x := s) (analyticAt_const.sub analyticAt_id)
  exact (gamma0EisensteinMatchingResponse_meromorphic N a s).neg.fun_sub
    (MeromorphicAt.fun_sum (fun i _ => (gamma0EisensteinMatchedCoefficient_meromorphic N a i s).fun_smul
      (hreflect i)))

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_mem (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) :
    gamma0CuspEisensteinMatchedTruncatedEnergy N a s ∈ (gamma0EisensteinMatchingForm N).subspace := by
  let S := (gamma0EisensteinMatchingForm N).subspace
  exact S.sub_mem (S.neg_mem (gamma0EisensteinMatchingResponse_mem N a s))
    (S.sum_mem (fun i _ => S.smul_mem _ (gamma0EisensteinMatchingResponse_mem N _ _)))

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_eq_offcut (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0CuspEisensteinMatchedTruncatedEnergy N a s=gamma0EisensteinMatchingResponseCombination N a s := by
  simp only [gamma0CuspEisensteinMatchedTruncatedEnergy,gamma0EisensteinMatchingResponseCombination,
    gamma0EisensteinMatchedCoefficient_eq_offcut N a s hs]

def gamma0EisensteinMatchedForcing (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    Gamma0RegionL2 N :=
  -gamma0CuspEisensteinCompactForcingMass N a s-
    ∑ i, gamma0EisensteinMatchedCoefficient N a s i •
      gamma0CuspEisensteinCompactForcingMass N (gamma0EisensteinCuspClassRepresentative N i) (1-s)

def gamma0EisensteinMatchedDefect (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    gamma0EnergySpace N :=
  gamma0EisensteinMatchingDefect N a s+
    ∑ i, gamma0EisensteinMatchedCoefficient N a s i • gamma0EisensteinOutgoingDefect N s i

theorem gamma0EisensteinMatchedDefect_meromorphic (N : ℕ) [NeZero N] (a : SL(2,ℤ)) :
    Meromorphic (gamma0EisensteinMatchedDefect N a) := by
  intro s
  have hreflect (i : Gamma0EisensteinCuspClasses N) : MeromorphicAt
      (fun w => gamma0EisensteinOutgoingDefect N w i) s :=
    (gamma0EisensteinMatchingDefect_meromorphic N (gamma0EisensteinCuspClassRepresentative N i)
      (1-s)).comp_analyticAt (g := fun w : ℂ => 1-w) (x := s) (analyticAt_const.sub analyticAt_id)
  exact (gamma0EisensteinMatchingDefect_meromorphic N a s).fun_add
    (MeromorphicAt.fun_sum (fun i _ => (gamma0EisensteinMatchedCoefficient_meromorphic N a i s).fun_smul
      (hreflect i)))

theorem gamma0EisensteinMatchedDefect_eq_zero_offcut (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EisensteinMatchedDefect N a s=0 := by
  simp only [gamma0EisensteinMatchedDefect,gamma0EisensteinMatchedCoefficient_eq_offcut N a s hs]
  exact gamma0EisensteinMatching_offcut_defect N a s hs

theorem gamma0EisensteinMatchedDefect_eventually_zero (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s, gamma0EisensteinMatchedDefect N a w=0 := by
  have hmer : MeromorphicOn (gamma0EisensteinMatchedDefect N a) univ :=
    fun w _ => gamma0EisensteinMatchedDefect_meromorphic N a w
  have h0 : meromorphicOrderAt (gamma0EisensteinMatchedDefect N a) (2:ℂ)=⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hD := gamma0EisensteinContinuationDomain_open.mem_nhds
      (gamma0EisensteinContinuationDomain_initial 2 (by norm_num))
    filter_upwards [nhdsWithin_le_nhds hD] with w hw
    exact gamma0EisensteinMatchedDefect_eq_zero_offcut N a w hw
  exact meromorphicOrderAt_eq_top_iff.mp
    (hmer.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ _) h0)

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_defect (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0CuspEisensteinMatchedTruncatedEnergy N a s)-
      gamma0EnergyMassAdjoint N (gamma0EisensteinMatchedForcing N a s)=
      -gamma0EisensteinMatchedDefect N a s := by
  simp only [gamma0CuspEisensteinMatchedTruncatedEnergy,gamma0EisensteinMatchedForcing,
    gamma0EisensteinMatchedDefect,gamma0EisensteinOutgoingDefect,gamma0EisensteinMatchingDefect,
    gamma0Eisenstein_reflect_parameter,map_sub,map_neg,map_sum,map_smul,smul_sub,Finset.sum_sub_distrib]
  abel

theorem gamma0CuspEisensteinMatchedTruncatedEnergy_eventually_pencil (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s,
      gamma0EnergyResolventPencil N (w*(1-w)) (gamma0CuspEisensteinMatchedTruncatedEnergy N a w)=
        gamma0EnergyMassAdjoint N (gamma0EisensteinMatchedForcing N a w) := by
  filter_upwards [gamma0EisensteinMatchedDefect_eventually_zero N a s] with w hw
  have h := gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_defect N a w
  rw [hw,neg_zero] at h
  exact sub_eq_zero.mp h

end ArtinMatthews
