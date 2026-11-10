module

public import ArtinMatthews.SpectralEisensteinMatchingOffCut
public import ArtinMatthews.SpectralMeromorphicFormMaps
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

/-! A finite meromorphic matching system. Its test vectors are the actual
outgoing defects at the negative energy s(1-s)=-2. The matrix there is
their genuine Gram matrix, so its determinant is not identically zero. -/
noncomputable section
open Set Filter Topology Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

section Determinant
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spectralMatrixDet_meromorphicAt (A : ℂ → Matrix ι ι ℂ) (s : ℂ)
    (hA : ∀ i j, MeromorphicAt (fun w => A w i j) s) :
    MeromorphicAt (fun w => (A w).det) s := by
  simp_rw [Matrix.det_apply']
  exact MeromorphicAt.fun_sum fun σ _ => (MeromorphicAt.const _ s).fun_mul
    (MeromorphicAt.fun_prod fun i _ => hA (σ i) i)

end Determinant

def gamma0EisensteinMatchingMatrix (N : ℕ) [NeZero N] (s : ℂ) :
    Matrix (Gamma0EisensteinCuspClasses N) (Gamma0EisensteinCuspClasses N) ℂ :=
  fun i j => inner ℂ (gamma0EisensteinOutgoingDefect N 2 i) (gamma0EisensteinOutgoingDefect N s j)

def gamma0EisensteinMatchingRhs (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (i : Gamma0EisensteinCuspClasses N) : ℂ :=
  -inner ℂ (gamma0EisensteinOutgoingDefect N 2 i) (gamma0EisensteinMatchingDefect N a s)

theorem gamma0EisensteinMatchingMatrix_entry_meromorphic (N : ℕ) [NeZero N]
    (i j : Gamma0EisensteinCuspClasses N) :
    Meromorphic (fun s => gamma0EisensteinMatchingMatrix N s i j) := by
  intro s
  let a := gamma0EisensteinCuspClassRepresentative N j
  have h := (gamma0EisensteinMatchingDefect_meromorphic N a (1-s)).comp_analyticAt
    (g := fun w : ℂ => 1-w) (x := s) (analyticAt_const.sub analyticAt_id)
  exact spectralMeromorphicAt_comp_clm (innerSL ℂ (gamma0EisensteinOutgoingDefect N 2 i)) h

theorem gamma0EisensteinMatchingRhs_meromorphic (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (i : Gamma0EisensteinCuspClasses N) : Meromorphic (fun s => gamma0EisensteinMatchingRhs N a s i) := by
  intro s
  exact (spectralMeromorphicAt_comp_clm (innerSL ℂ (gamma0EisensteinOutgoingDefect N 2 i))
    (gamma0EisensteinMatchingDefect_meromorphic N a s)).neg

theorem gamma0EisensteinMatchingMatrix_det_meromorphic (N : ℕ) [NeZero N] :
    Meromorphic (fun s => (gamma0EisensteinMatchingMatrix N s).det) :=
  fun s => spectralMatrixDet_meromorphicAt _ s
    (fun i j => gamma0EisensteinMatchingMatrix_entry_meromorphic N i j s)

theorem gamma0EisensteinMatchingMatrix_det_base_ne_zero (N : ℕ) [NeZero N] :
    (gamma0EisensteinMatchingMatrix N 2).det≠0 :=
  spectralGram_det_ne_zero_of_sum (gamma0EisensteinOutgoingDefect N 2)
    (gamma0EisensteinOutgoingDefect_sum_eq_zero_imp N 2
      (gamma0EisensteinContinuationDomain_initial 2 (by norm_num)))

theorem gamma0EisensteinMatchingMatrix_det_continuousAt_base (N : ℕ) [NeZero N] :
    ContinuousAt (fun s => (gamma0EisensteinMatchingMatrix N s).det) (2:ℂ) := by
  have hs := (gamma0EisensteinContinuationDomain_initial 2 (by norm_num)).2
  have hq : (((1:ℂ)-2)*(1-(1-2))).re<‖((1:ℂ)-2)*(1-(1-2))‖ := by
    rw [gamma0Eisenstein_reflect_parameter]
    exact hs
  have hentry (i j : Gamma0EisensteinCuspClasses N) :
      AnalyticAt ℂ (fun w => gamma0EisensteinMatchingMatrix N w i j) (2:ℂ) := by
    let a := gamma0EisensteinCuspClassRepresentative N j
    have he : AnalyticAt ℂ (fun s : ℂ => gamma0EisensteinMatchingDefect N a (1-s)) (2:ℂ) :=
      (gamma0EisensteinMatchingDefect_analyticAt N a (1-2) hq).comp
        (f := fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id)
    exact ((innerSL ℂ (gamma0EisensteinOutgoingDefect N 2 i)).analyticAt _).comp he
  have hd : AnalyticAt ℂ (fun w => (gamma0EisensteinMatchingMatrix N w).det) (2:ℂ) := by
    simp_rw [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ => analyticAt_const.mul
      (Finset.univ.analyticAt_fun_prod (fun j _ => hentry (σ j) j)))
  exact hd.continuousAt

theorem gamma0EisensteinMatchingMatrix_det_eventually_ne_zero (N : ℕ) [NeZero N] (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s, (gamma0EisensteinMatchingMatrix N w).det≠0 := by
  let f := fun w => (gamma0EisensteinMatchingMatrix N w).det
  have hmer : MeromorphicOn f univ := fun w _ => gamma0EisensteinMatchingMatrix_det_meromorphic N w
  have h0 : meromorphicOrderAt f (2:ℂ)≠⊤ := by
    intro h
    have hzero := meromorphicOrderAt_eq_top_iff.mp h
    have hn : ∀ᶠ w in 𝓝[≠] (2:ℂ), f w≠0 := nhdsWithin_le_nhds
      ((gamma0EisensteinMatchingMatrix_det_continuousAt_base N).eventually_ne
        (gamma0EisensteinMatchingMatrix_det_base_ne_zero N))
    obtain ⟨w,hw,h'w⟩ := (hzero.and hn).exists
    exact h'w hw
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmer s (mem_univ _))).mp
    (hmer.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ _) h0)

theorem gamma0EisensteinMatchingMatrix_equation (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    (gamma0EisensteinMatchingMatrix N s).mulVec (gamma0EisensteinMatchingTrueCoefficient N a s)=
      gamma0EisensteinMatchingRhs N a s := by
  funext i
  have h := congrArg (innerSL ℂ (gamma0EisensteinOutgoingDefect N 2 i))
    (gamma0EisensteinMatching_offcut_defect N a s hs)
  simp only [map_add,map_sum,map_smul,map_zero,innerSL_apply_apply,smul_eq_mul] at h
  simp only [gamma0EisensteinMatchingMatrix,gamma0EisensteinMatchingRhs,Matrix.mulVec,dotProduct]
  simp_rw [mul_comm _ (gamma0EisensteinMatchingTrueCoefficient N a s _)]
  linear_combination h

end ArtinMatthews
