module

public import ArtinMatthews.SpectralCompactResolventMatchedEnergy
public import ArtinMatthews.SpectralEisensteinCutoffCompactTesting
public import ArtinMatthews.SpectralEisensteinCutoffAutomorphy
public import ArtinMatthews.SpectralGamma0MassRepresentativeUnfolding
public import ArtinMatthews.SpectralMeromorphicFormMaps
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

/-! The actual full ambient resolvent has meromorphic compact smooth test
pairings in the cusp spectral parameter. The original off-cut values
are retained exactly. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0CuspOutgoingCutoffEnergy_test (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N φ) (gamma0EnergyInclusion N (gamma0CuspOutgoingCutoffEnergy N a q hq))=
      (2:ℂ)*gamma0EisensteinCutoffCompactTest N a φ q := by
  rw [gamma0CuspOutgoingCutoffEnergy_mass]
  exact gamma0Mass_inner_unfold_representative N (gamma0CuspOutgoingCutoffMass N a q hq)
    (gamma0CuspEisensteinCutoff N a q) (gamma0CuspOutgoingCutoff_continuous N a q)
    (gamma0CuspEisensteinCutoff_automorphy N a q) (gamma0CuspOutgoingCutoffMass_ae N a q hq) φ

def gamma0CompactForcingMatchedTest (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) : ℂ :=
  inner ℂ (gamma0SmoothSeedMass N φ)
    (gamma0EnergyInclusion N (gamma0CompactForcingMatchedEnergy N ψ A s))+
    ∑ j,gamma0CompactForcingMatchedCoefficient N ψ A s j *
      ((2:ℂ)*gamma0EisensteinCutoffCompactTest N (gamma0EisensteinCuspClassRepresentative N j) φ (1-s))

theorem gamma0EisensteinCutoffCompactTest_reflect_analyticAt (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (φ : h2SmoothCompactSeeds) (s : ℂ) :
    AnalyticAt ℂ (fun w => (2:ℂ)*gamma0EisensteinCutoffCompactTest N a φ (1-w)) s :=
  analyticAt_const.mul ((gamma0EisensteinCutoffCompactTest_analyticAt N a φ (1-s)).comp
    (f := fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id))

theorem gamma0CompactForcingMatchedTest_meromorphic (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) :
    Meromorphic (gamma0CompactForcingMatchedTest N ψ φ A) := by
  intro s
  let L := (innerSL ℂ (gamma0SmoothSeedMass N φ)).comp (gamma0EnergyInclusion N)
  have hL := spectralMeromorphicAt_comp_clm L (gamma0CompactForcingMatchedEnergy_meromorphic N ψ A s)
  exact hL.fun_add (MeromorphicAt.fun_sum fun j _ =>
    (gamma0CompactForcingMatchedCoefficient_meromorphic N ψ A j s).fun_mul
      (gamma0EisensteinCutoffCompactTest_reflect_analyticAt N (gamma0EisensteinCuspClassRepresentative N j) φ s).meromorphicAt)

theorem gamma0CompactForcingMatchedTest_analyticAt (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ)
    (hs : gamma0HeightMatchingRegular N A.height A.pos s) :
    AnalyticAt ℂ (gamma0CompactForcingMatchedTest N ψ φ A) s := by
  let L := (innerSL ℂ (gamma0SmoothSeedMass N φ)).comp (gamma0EnergyInclusion N)
  have hL := (L.analyticAt _).comp (gamma0CompactForcingMatchedEnergy_analyticAt N ψ A s hs)
  exact hL.add (Finset.univ.analyticAt_fun_sum fun j _ =>
    (gamma0CompactForcingMatchedCoefficient_analyticAt N ψ A s hs j).mul
      (gamma0EisensteinCutoffCompactTest_reflect_analyticAt N (gamma0EisensteinCuspClassRepresentative N j) φ s))

theorem gamma0CompactForcingMatchedTest_eq_actual (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ)
    (hs : s∈gamma0EisensteinContinuationDomain)
    (hd : (gamma0HeightMatchingMatrix N A.height A.pos s).det≠0) :
    gamma0CompactForcingMatchedTest N ψ φ A s=
      inner ℂ (gamma0SmoothSeedMass N φ) (gamma0AmbientResolventFamily N (s*(1-s)) (gamma0SmoothSeedMass N ψ)) := by
  let L := (innerSL ℂ (gamma0SmoothSeedMass N φ)).comp (gamma0EnergyInclusion N)
  rw [← gamma0CompactForcingResolventEnergy_mass N ψ s hs]
  change gamma0CompactForcingMatchedTest N ψ φ A s=L (gamma0CompactForcingResolventEnergy N ψ s hs)
  rw [gamma0CompactForcingResolventEnergy_eq_matched N ψ A s hs hd,map_add,
    gamma0CompactForcingResolventActualOutgoing,map_sum]
  simp_rw [map_smul]
  unfold gamma0CompactForcingMatchedTest
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [gamma0CompactForcingMatchedCoefficient,gamma0CompactForcingResolventMatchingCoefficient_eq_true N ψ A s hs hd]
  change gamma0CompactForcingResolventTrueCoefficient N ψ A s hs j *
    ((2:ℂ)*gamma0EisensteinCutoffCompactTest N (gamma0EisensteinCuspClassRepresentative N j) φ (1-s))=
      gamma0CompactForcingResolventTrueCoefficient N ψ A s hs j *
        inner ℂ (gamma0SmoothSeedMass N φ) (gamma0EnergyInclusion N
          (gamma0CuspOutgoingCutoffEnergy N (gamma0EisensteinCuspClassRepresentative N j)
            (1-s) (gamma0Eisenstein_reflect_realPart hs.1)))
  rw [gamma0CuspOutgoingCutoffEnergy_test]

def gamma0CompactForcingResolventMeromorphicTest (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ) : ℂ := by
  classical
  exact if s∈gamma0EisensteinContinuationDomain then
    inner ℂ (gamma0SmoothSeedMass N φ) (gamma0AmbientResolventFamily N (s*(1-s)) (gamma0SmoothSeedMass N ψ))
    else gamma0CompactForcingMatchedTest N ψ φ A s

theorem gamma0CompactForcingResolventMeromorphicTest_offcut (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ)
    (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0CompactForcingResolventMeromorphicTest N ψ φ A s=
      inner ℂ (gamma0SmoothSeedMass N φ) (gamma0AmbientResolventFamily N (s*(1-s)) (gamma0SmoothSeedMass N ψ)) := by
  simp only [gamma0CompactForcingResolventMeromorphicTest,ite_eq_left hs]

theorem gamma0CompactForcingResolventMeromorphicTest_eq_matched_of_det (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ)
    (hd : (gamma0HeightMatchingMatrix N A.height A.pos s).det≠0) :
    gamma0CompactForcingResolventMeromorphicTest N ψ φ A s=gamma0CompactForcingMatchedTest N ψ φ A s := by
  by_cases hs : s∈gamma0EisensteinContinuationDomain
  · rw [gamma0CompactForcingResolventMeromorphicTest_offcut N ψ φ A s hs,
      gamma0CompactForcingMatchedTest_eq_actual N ψ φ A s hs hd]
  · simp only [gamma0CompactForcingResolventMeromorphicTest,ite_eq_right hs]

theorem gamma0CompactForcingResolventMeromorphicTest_meromorphic (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) :
    Meromorphic (gamma0CompactForcingResolventMeromorphicTest N ψ φ A) := by
  intro s
  apply (gamma0CompactForcingMatchedTest_meromorphic N ψ φ A s).congr
  filter_upwards [gamma0HeightMatchingMatrix_det_eventually_ne_zero N A.height A.pos A.matching_le s] with w hw
  exact (gamma0CompactForcingResolventMeromorphicTest_eq_matched_of_det N ψ φ A w hw).symm

theorem gamma0CompactForcingResolventMeromorphicTest_analyticAt_regular (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (s : ℂ)
    (hs : gamma0HeightMatchingRegular N A.height A.pos s) :
    AnalyticAt ℂ (gamma0CompactForcingResolventMeromorphicTest N ψ φ A) s := by
  apply (gamma0CompactForcingMatchedTest_analyticAt N ψ φ A s hs).congr
  have h := (gamma0HeightMatchingMatrix_det_analyticAt N A.height A.pos s hs.1).continuousAt.eventually_ne hs.2
  filter_upwards [h] with w hw
  exact (gamma0CompactForcingResolventMeromorphicTest_eq_matched_of_det N ψ φ A w hw).symm

end ArtinMatthews
