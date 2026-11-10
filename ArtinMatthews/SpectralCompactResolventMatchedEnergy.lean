module

public import ArtinMatthews.SpectralCompactResolventMatchingCoefficient
public import ArtinMatthews.SpectralEisensteinForcingAnalytic
public import ArtinMatthews.SpectralEisensteinMeromorphicScattering
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

/-! The compact-forcing matched energy and its full weak equation.
Its full defect vanishes as a germ by the exact actual off-cut identity. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CompactForcingMatchedCoefficient (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) : Gamma0EisensteinCuspClasses N → ℂ :=
  gamma0HeightMatchingCoefficient N A.height A.pos s (gamma0SmoothSeedMass N ψ)

def gamma0CompactForcingMatchedEnergy (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) : gamma0EnergySpace N :=
  gamma0HeightMatchingResponse N A.height A.pos s
    (gamma0CompactForcingCorrectedMass N ψ s (gamma0CompactForcingMatchedCoefficient N ψ A s))

theorem gamma0CompactForcingMatchedEnergy_expand (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) :
    gamma0CompactForcingMatchedEnergy N ψ A s =
      gamma0HeightMatchingResponse N A.height A.pos s (gamma0SmoothSeedMass N ψ)-
      ∑ i,gamma0CompactForcingMatchedCoefficient N ψ A s i •
        gamma0HeightMatchingResponse N A.height A.pos s (gamma0CuspChannelForcing N (1-s) i) := by
  simp only [gamma0CompactForcingMatchedEnergy,gamma0CompactForcingCorrectedMass,map_sub,map_sum,map_smul]

theorem gamma0CompactForcingMatchedEnergy_mem (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) :
    gamma0CompactForcingMatchedEnergy N ψ A s∈(gamma0TruncatedFormData N A.height A.pos).subspace :=
  gamma0HeightMatchingResponse_mem N A.height A.pos s _

theorem gamma0CompactForcingMatchedCoefficient_meromorphic (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (i : Gamma0EisensteinCuspClasses N) :
    Meromorphic (fun s => gamma0CompactForcingMatchedCoefficient N ψ A s i) :=
  fun s => gamma0HeightMatchingCoefficient_meromorphicAt N A.height A.pos _ s analyticAt_const i

theorem gamma0CompactForcingMatchedCoefficient_analyticAt (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (hs : gamma0HeightMatchingRegular N A.height A.pos s)
    (i : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0CompactForcingMatchedCoefficient N ψ A w i) s :=
  gamma0HeightMatchingCoefficient_analyticAt N A.height A.pos _ s hs analyticAt_const i

theorem gamma0CuspChannelForcing_reflect_analyticAt (N : ℕ) [NeZero N]
    (s : ℂ) (i : Gamma0EisensteinCuspClasses N) :
    AnalyticAt ℂ (fun w => gamma0CuspChannelForcing N (1-w) i) s :=
  (gamma0CuspEisensteinCompactForcingMass_analyticAt N (gamma0EisensteinCuspClassRepresentative N i) (1-s)).comp
    (f := fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id)

theorem gamma0CompactForcingMatchedEnergy_meromorphic (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) :
    Meromorphic (gamma0CompactForcingMatchedEnergy N ψ A) := by
  intro s
  rw [funext (gamma0CompactForcingMatchedEnergy_expand N ψ A)]
  have hR := gamma0HeightMatchingResponse_meromorphic N A.height A.pos s
  refine (spectralMeromorphicAt_clmApply _ (fun _ => gamma0SmoothSeedMass N ψ) s hR analyticAt_const).fun_sub
    (MeromorphicAt.fun_sum (fun i _ => ?_))
  exact (gamma0CompactForcingMatchedCoefficient_meromorphic N ψ A i s).fun_smul
    (spectralMeromorphicAt_clmApply _ _ s hR (gamma0CuspChannelForcing_reflect_analyticAt N s i))

theorem gamma0CompactForcingMatchedEnergy_analyticAt (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (hs : gamma0HeightMatchingRegular N A.height A.pos s) :
    AnalyticAt ℂ (gamma0CompactForcingMatchedEnergy N ψ A) s := by
  rw [funext (gamma0CompactForcingMatchedEnergy_expand N ψ A)]
  have hR := gamma0HeightMatchingResponse_analyticAt N A.height A.pos s hs.1
  refine (spectralAnalytic_clmApply _ (fun _ => gamma0SmoothSeedMass N ψ) s hR analyticAt_const).sub
    (Finset.univ.analyticAt_fun_sum (fun i _ => ?_))
  exact (gamma0CompactForcingMatchedCoefficient_analyticAt N ψ A s hs i).smul
    (spectralAnalytic_clmApply _ _ s hR (gamma0CuspChannelForcing_reflect_analyticAt N s i))

def gamma0CompactForcingMatchedDefect (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) : gamma0EnergySpace N :=
  gamma0HeightMatchingDefect N A.height A.pos s
    (gamma0CompactForcingCorrectedMass N ψ s (gamma0CompactForcingMatchedCoefficient N ψ A s))

theorem gamma0CompactForcingMatchedDefect_expand (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) :
    gamma0CompactForcingMatchedDefect N ψ A s =
      gamma0HeightMatchingDefect N A.height A.pos s (gamma0SmoothSeedMass N ψ)-
      ∑ i,gamma0CompactForcingMatchedCoefficient N ψ A s i •
        gamma0HeightOutgoingDefect N A.height A.pos s i := by
  simp only [gamma0CompactForcingMatchedDefect,gamma0CompactForcingCorrectedMass,
    gamma0HeightOutgoingDefect,map_sub,map_sum,map_smul]

theorem gamma0CompactForcingMatchedDefect_meromorphic (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) :
    Meromorphic (gamma0CompactForcingMatchedDefect N ψ A) := by
  intro s
  rw [funext (gamma0CompactForcingMatchedDefect_expand N ψ A)]
  refine (gamma0HeightMatchingDefect_apply_meromorphicAt N A.height A.pos
    (fun _ => gamma0SmoothSeedMass N ψ) s analyticAt_const).fun_sub (MeromorphicAt.fun_sum (fun i _ => ?_))
  exact (gamma0CompactForcingMatchedCoefficient_meromorphic N ψ A i s).fun_smul
    (gamma0HeightMatchingDefect_apply_meromorphicAt N A.height A.pos _ s
      (gamma0CuspChannelForcing_reflect_analyticAt N s i))

theorem gamma0CompactForcingMatchedDefect_analyticAt (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (hs : gamma0HeightMatchingRegular N A.height A.pos s) :
    AnalyticAt ℂ (gamma0CompactForcingMatchedDefect N ψ A) s := by
  rw [funext (gamma0CompactForcingMatchedDefect_expand N ψ A)]
  refine (gamma0HeightMatchingDefect_apply_analyticAt N A.height A.pos
    (fun _ => gamma0SmoothSeedMass N ψ) s hs.1 analyticAt_const).sub
    (Finset.univ.analyticAt_fun_sum (fun i _ => ?_))
  exact (gamma0CompactForcingMatchedCoefficient_analyticAt N ψ A s hs i).smul
    (gamma0HeightMatchingDefect_apply_analyticAt N A.height A.pos _ s hs.1
      (gamma0CuspChannelForcing_reflect_analyticAt N s i))

theorem gamma0CompactForcingMatchedDefect_eq_zero_offcut (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain)
    (hd : (gamma0HeightMatchingMatrix N A.height A.pos s).det≠0) :
    gamma0CompactForcingMatchedDefect N ψ A s=0 := by
  rw [gamma0CompactForcingMatchedDefect,gamma0CompactForcingMatchedCoefficient,
    gamma0CompactForcingResolventMatchingCoefficient_eq_true N ψ A s hs hd]
  exact gamma0CompactForcingResolventActualDefect_zero N ψ A s hs

theorem gamma0CompactForcingMatchedDefect_eventually_zero (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s,gamma0CompactForcingMatchedDefect N ψ A w=0 := by
  let f := gamma0CompactForcingMatchedDefect N ψ A
  have hmer : MeromorphicOn f univ := fun w _ => gamma0CompactForcingMatchedDefect_meromorphic N ψ A w
  have h0 : meromorphicOrderAt f (2:ℂ)=⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hD := gamma0EisensteinContinuationDomain_open.mem_nhds
      (gamma0EisensteinContinuationDomain_initial 2 (by norm_num))
    filter_upwards [nhdsWithin_le_nhds hD,
      gamma0HeightMatchingMatrix_det_eventually_ne_zero N A.height A.pos A.matching_le 2] with w hw hd
    exact gamma0CompactForcingMatchedDefect_eq_zero_offcut N ψ A w hw hd
  exact meromorphicOrderAt_eq_top_iff.mp
    (hmer.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ _) h0)

theorem gamma0CompactForcingMatchedEnergy_pencil_regular (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (hs : gamma0HeightMatchingRegular N A.height A.pos s) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0CompactForcingMatchedEnergy N ψ A s)=
      gamma0EnergyMassAdjoint N
        (gamma0CompactForcingCorrectedMass N ψ s (gamma0CompactForcingMatchedCoefficient N ψ A s)) := by
  have hc := (gamma0CompactForcingMatchedDefect_analyticAt N ψ A s hs).continuousAt
  have he : gamma0CompactForcingMatchedDefect N ψ A =ᶠ[𝓝[≠] s] fun _ => 0 :=
    gamma0CompactForcingMatchedDefect_eventually_zero N ψ A s
  have hz : Tendsto (gamma0CompactForcingMatchedDefect N ψ A) (𝓝[≠] s) (𝓝 (0:gamma0EnergySpace N)) :=
    tendsto_const_nhds.congr' he.symm
  exact sub_eq_zero.mp (tendsto_nhds_unique hc.continuousWithinAt.tendsto hz)

theorem gamma0CompactForcingResolventEnergy_eq_matched (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain)
    (hd : (gamma0HeightMatchingMatrix N A.height A.pos s).det≠0) :
    gamma0CompactForcingResolventEnergy N ψ s hs=
      gamma0CompactForcingMatchedEnergy N ψ A s+gamma0CompactForcingResolventActualOutgoing N ψ A s hs := by
  have h := gamma0CompactForcingResolventActualTruncated_eq_response N ψ A s hs
  rw [gamma0CompactForcingResolventActualTruncated,sub_eq_iff_eq_add] at h
  rw [gamma0CompactForcingMatchedEnergy,gamma0CompactForcingMatchedCoefficient,
    gamma0CompactForcingResolventMatchingCoefficient_eq_true N ψ A s hs hd]
  exact h

end ArtinMatthews
