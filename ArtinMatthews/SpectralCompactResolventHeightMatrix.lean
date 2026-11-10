module

public import ArtinMatthews.SpectralCompactResolventActualDecomposition
public import ArtinMatthews.SpectralEisensteinForcingAnalytic
public import ArtinMatthews.SpectralEisensteinRegularMatching
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

/-! The arbitrary-height finite matching matrix comes from testing
the actual outgoing defects. Its determinant is genuinely nonzero at
the negative spectral parameter, by independence of the outgoing tails. -/
noncomputable section
open Set Filter Topology Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0HeightOutgoingDefect (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (s : ℂ) (i : Gamma0EisensteinCuspClasses N) : gamma0EnergySpace N :=
  gamma0HeightMatchingDefect N Y hY s (gamma0CuspChannelForcing N (1-s) i)

theorem gamma0HeightOutgoingDefect_sum_eq_zero_imp (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y) (s : ℂ)
    (hs : s∈gamma0EisensteinContinuationDomain) (c : Gamma0EisensteinCuspClasses N → ℂ)
    (hc : (∑ i,c i • gamma0HeightOutgoingDefect N Y hY s i)=0) : c=0 := by
  let r := gamma0EisensteinCuspClassRepresentative N
  let q := 1-s
  let hq := gamma0Eisenstein_reflect_realPart hs.1
  let F := ∑ i,c i • gamma0CuspChannelForcing N q i
  let U := gamma0HeightMatchingResponse N Y hY s F
  let W := ∑ i,c i • gamma0CuspOutgoingCutoffEnergy N (r i) q hq
  let P := gamma0EnergyResolventPencil N (s*(1-s))
  let J := gamma0EnergyMassAdjoint N
  have hd : gamma0HeightMatchingDefect N Y hY s F=0 := by
    simpa only [F,map_sum,map_smul,gamma0HeightOutgoingDefect,q] using hc
  have hPU : P U=J F := sub_eq_zero.mp hd
  have hPW : P W=J F := by
    simp only [W,F,P,J,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← gamma0Eisenstein_reflect_parameter s]
    exact congrArg (fun u : gamma0EnergySpace N => c i • u)
      (gamma0CuspOutgoingCutoffEnergy_pencil N (r i) q hq)
  have he : U=W := gamma0EisensteinMatchingPencil_injective N _ hs.2 (hPU.trans hPW.symm)
  have hm := gamma0HeightMatchingResponse_mem N Y hY s F
  change U∈(gamma0TruncatedFormData N Y hY).subspace at hm
  rw [he] at hm
  exact gamma0CuspOutgoingCutoffEnergy_sum_mem_atHeight_imp_zero N q hq c Y hY hmin hm

def gamma0HeightMatchingMatrix (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y) (s : ℂ) :
    Matrix (Gamma0EisensteinCuspClasses N) (Gamma0EisensteinCuspClasses N) ℂ :=
  fun i j => inner ℂ (gamma0HeightOutgoingDefect N Y hY 2 i) (gamma0HeightOutgoingDefect N Y hY s j)

def gamma0HeightMatchingRhs (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y) (s : ℂ)
    (F : Gamma0RegionL2 N) (i : Gamma0EisensteinCuspClasses N) : ℂ :=
  inner ℂ (gamma0HeightOutgoingDefect N Y hY 2 i) (gamma0HeightMatchingDefect N Y hY s F)

theorem gamma0HeightMatchingMatrix_entry_meromorphic (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y)
    (i j : Gamma0EisensteinCuspClasses N) :
    Meromorphic (fun s => gamma0HeightMatchingMatrix N Y hY s i j) := by
  intro s
  have h := (gamma0CuspEisensteinCompactForcingMass_analyticAt N
    (gamma0EisensteinCuspClassRepresentative N j) (1-s)).comp
    (f := fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id)
  exact spectralMeromorphicAt_comp_clm (innerSL ℂ (gamma0HeightOutgoingDefect N Y hY 2 i))
    (gamma0HeightMatchingDefect_apply_meromorphicAt N Y hY _ s h)

theorem gamma0HeightMatchingMatrix_entry_analyticAt (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y)
    (s : ℂ) (hs : s*(1-s)∉(gamma0TruncatedFormData N Y hY).exceptional)
    (i j : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0HeightMatchingMatrix N Y hY w i j) s := by
  have h := (gamma0CuspEisensteinCompactForcingMass_analyticAt N
    (gamma0EisensteinCuspClassRepresentative N j) (1-s)).comp
    (f := fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id)
  exact ((innerSL ℂ (gamma0HeightOutgoingDefect N Y hY 2 i)).analyticAt _).comp
    (gamma0HeightMatchingDefect_apply_analyticAt N Y hY _ s hs h)

theorem gamma0HeightMatchingMatrix_det_meromorphic (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y) :
    Meromorphic (fun s => (gamma0HeightMatchingMatrix N Y hY s).det) :=
  fun s => spectralMatrixDet_meromorphicAt _ s
    (fun i j => gamma0HeightMatchingMatrix_entry_meromorphic N Y hY i j s)

theorem gamma0HeightMatchingMatrix_det_analyticAt (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y)
    (s : ℂ) (hs : s*(1-s)∉(gamma0TruncatedFormData N Y hY).exceptional) :
    AnalyticAt ℂ (fun w => (gamma0HeightMatchingMatrix N Y hY w).det) s :=
  spectralMatrixDet_analyticAt _ s (gamma0HeightMatchingMatrix_entry_analyticAt N Y hY s hs)

theorem gamma0HeightMatchingMatrix_det_base_ne_zero (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y) :
    (gamma0HeightMatchingMatrix N Y hY 2).det≠0 :=
  spectralGram_det_ne_zero_of_sum (gamma0HeightOutgoingDefect N Y hY 2)
    (gamma0HeightOutgoingDefect_sum_eq_zero_imp N Y hY hmin 2
      (gamma0EisensteinContinuationDomain_initial 2 (by norm_num)))

theorem gamma0HeightMatchingMatrix_det_eventually_ne_zero (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s,(gamma0HeightMatchingMatrix N Y hY w).det≠0 := by
  let f := fun w => (gamma0HeightMatchingMatrix N Y hY w).det
  have hmer : MeromorphicOn f univ := fun w _ => gamma0HeightMatchingMatrix_det_meromorphic N Y hY w
  have h2 := gamma0EisensteinContinuationDomain_initial 2 (by norm_num)
  have ha := gamma0HeightMatchingMatrix_det_analyticAt N Y hY 2
    (gamma0HeightMatchingForm_not_exceptional N Y hY _ h2.2)
  have h0 : meromorphicOrderAt f (2:ℂ)≠⊤ := by
    intro h
    have hzero := meromorphicOrderAt_eq_top_iff.mp h
    have hn : ∀ᶠ w in 𝓝[≠] (2:ℂ),f w≠0 := nhdsWithin_le_nhds
      (ha.continuousAt.eventually_ne (gamma0HeightMatchingMatrix_det_base_ne_zero N Y hY hmin))
    obtain ⟨w,hw,h'w⟩ := (hzero.and hn).exists
    exact h'w hw
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmer s (mem_univ _))).mp
    (hmer.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ _) h0)

end ArtinMatthews
