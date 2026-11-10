module

public import ArtinMatthews.SpectralEisensteinCriticalLine
public import Mathlib.Analysis.Meromorphic.NormalForm
public import ArtinMatthews.SpectralEisensteinCriticalEnergy
public import ArtinMatthews.SpectralEisensteinCriticalNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Bounded regular critical entries rule out every critical pole. The
normal-form family gives the actual removable values at exceptional points. -/
noncomputable section
open Set Filter Topology Matrix
namespace ArtinMatthews

theorem gamma0CuspScatteringMatrix_entry_norm_le_one_regular (N : ℕ) [NeZero N]
    (s : ℂ) (hs : s.re=1/2) (ht : s.im≠0) (hr : gamma0EisensteinMatchingRegular N s)
    (i j : Gamma0EisensteinCuspClasses N) : ‖gamma0CuspScatteringMatrix N s i j‖≤1 := by
  classical
  let M := gamma0CuspScatteringMatrix N s
  have h := gamma0CuspScatteringMatrix_norm_sq_regular N s hs ht hr
    (Pi.single j (1:ℂ))
  rw [Matrix.mulVec_single_one] at h
  have hOne : (∑ k : Gamma0EisensteinCuspClasses N,‖(Pi.single j (1:ℂ) : Gamma0EisensteinCuspClasses N → ℂ) k‖^2)=1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  have hsq : ‖M i j‖^2≤1 := by
    rw [← hOne,← h]
    exact Finset.single_le_sum (f:=fun k => ‖M k j‖^2)
      (fun k _ => sq_nonneg ‖M k j‖) (Finset.mem_univ i)
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (hsq.trans_eq (by norm_num))

theorem gamma0CuspScatteringMatrix_entry_meromorphic (N : ℕ) [NeZero N]
    (i j : Gamma0EisensteinCuspClasses N) :
    Meromorphic (fun s => gamma0CuspScatteringMatrix N s i j) :=
  gamma0CuspScatteringMeromorphic_meromorphic N
    (gamma0EisensteinCuspClassRepresentative N i) (gamma0EisensteinCuspClassRepresentative N j)

theorem gamma0CuspScatteringMatrix_entry_analyticAt_regular (N : ℕ) [NeZero N]
    (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) (i j : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0CuspScatteringMatrix N w i j) s :=
  gamma0CuspScatteringMeromorphic_analyticAt_regular N
    (gamma0EisensteinCuspClassRepresentative N i) (gamma0EisensteinCuspClassRepresentative N j) s hs

theorem gamma0CuspScatteringMatrix_entry_order_critical (N : ℕ) [NeZero N]
    (t : ℝ) (i j : Gamma0EisensteinCuspClasses N) :
    0 ≤ meromorphicOrderAt (fun s => gamma0CuspScatteringMatrix N s i j) (eisensteinCriticalPoint t) := by
  by_contra h
  have hBlow := (tendsto_norm_atTop_iff_cobounded.mpr
    (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge h))).comp
    (eisensteinCriticalPoint_tendsto_punctured t)
  have hgt : ∀ᶠ u in 𝓝[≠] t,1<‖gamma0CuspScatteringMatrix N (eisensteinCriticalPoint u) i j‖ :=
    hBlow.eventually_gt_atTop 1
  obtain ⟨u,hu,hr,hn⟩ := (hgt.and (gamma0EisensteinMatchingRegular_critical_eventually N t)).exists
  exact (not_lt_of_ge (gamma0CuspScatteringMatrix_entry_norm_le_one_regular N _
    (eisensteinCriticalPoint_re u) (by simpa only [eisensteinCriticalPoint_im] using hn) hr i j)) hu

def gamma0CuspScatteringCanonical (N : ℕ) [NeZero N] (s : ℂ) :
    Matrix (Gamma0EisensteinCuspClasses N) (Gamma0EisensteinCuspClasses N) ℂ :=
  fun i j => toMeromorphicNFOn (fun w => gamma0CuspScatteringMatrix N w i j) univ s

theorem gamma0CuspScatteringCanonical_entry_analyticAt_critical (N : ℕ) [NeZero N]
    (t : ℝ) (i j : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun s => gamma0CuspScatteringCanonical N s i j) (eisensteinCriticalPoint t) := by
  let f (s : ℂ) := gamma0CuspScatteringMatrix N s i j
  have h := meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ (eisensteinCriticalPoint t))
  apply h.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn
    (fun s _ => gamma0CuspScatteringMatrix_entry_meromorphic N i j s) (mem_univ _)]
  exact gamma0CuspScatteringMatrix_entry_order_critical N t i j

theorem gamma0CuspScatteringCanonical_entry_eq_of_analytic (N : ℕ) [NeZero N]
    (s : ℂ) (i j : Gamma0EisensteinCuspClasses N)
    (h : AnalyticAt ℂ (fun w => gamma0CuspScatteringMatrix N w i j) s) :
    gamma0CuspScatteringCanonical N s i j=gamma0CuspScatteringMatrix N s i j := by
  unfold gamma0CuspScatteringCanonical
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt
    (fun w _ => gamma0CuspScatteringMatrix_entry_meromorphic N i j w) (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr h.meromorphicNFAt]

theorem gamma0CuspScatteringCanonical_eq_regular (N : ℕ) [NeZero N] (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s) :
    gamma0CuspScatteringCanonical N s=gamma0CuspScatteringMatrix N s := by
  ext i j
  exact gamma0CuspScatteringCanonical_entry_eq_of_analytic N s i j
    (gamma0CuspScatteringMatrix_entry_analyticAt_regular N s hs i j)

theorem gamma0CuspScatteringCanonical_initial (N : ℕ) [NeZero N] (s : ℂ) (hs : 1<s.re)
    (i j : Gamma0EisensteinCuspClasses N) :
    gamma0CuspScatteringCanonical N s i j=gamma0CuspScattering N
      (gamma0EisensteinCuspClassRepresentative N i) (gamma0EisensteinCuspClassRepresentative N j) s := by
  rw [gamma0CuspScatteringCanonical_entry_eq_of_analytic N s i j
    (gamma0CuspScatteringMeromorphic_analyticAt_offcut N _ _ s (gamma0EisensteinContinuationDomain_initial s hs))]
  exact gamma0CuspScatteringMeromorphic_initial N _ _ s hs

end ArtinMatthews
