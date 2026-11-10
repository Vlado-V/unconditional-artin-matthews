module

public import ArtinMatthews.SpectralCompactResolventMatchedEnergy
public import ArtinMatthews.SpectralEisensteinCriticalEnergy
public import ArtinMatthews.SpectralEisensteinMeromorphicTests
public import ArtinMatthews.SpectralEisensteinUpperCompactTesting
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

/-! The actual compact upper truncations for the forced resolvent and
for an incoming Eisenstein combination at the same arbitrary upper scale. -/
noncomputable section
open Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0CuspUpperEnergyCombination (N : ℕ) [NeZero N] (q : ℂ) (A : ℝ) (hA : 0<A)
    (c : Gamma0EisensteinCuspClasses N → ℂ) : gamma0EnergySpace N :=
  ∑ j,c j • gamma0CuspUpperTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N j) q A hA

def gamma0CuspUpperForcingCombination (N : ℕ) [NeZero N] (q : ℂ) (A : ℝ) (hA : 0<A)
    (c : Gamma0EisensteinCuspClasses N → ℂ) : Gamma0RegionL2 N :=
  ∑ j,c j • gamma0CuspUpperCutoffForcingMass N (gamma0EisensteinCuspClassRepresentative N j) q A hA

theorem gamma0CuspUpperEnergyCombination_pencil (N : ℕ) [NeZero N] (q : ℂ)
    (A : ℝ) (hA : 0<A) (hA2 : A≤1/2) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    gamma0EnergyResolventPencil N (q*(1-q)) (gamma0CuspUpperEnergyCombination N q A hA c)=
      gamma0EnergyMassAdjoint N
        ((∑ j,c j • gamma0CuspChannelForcing N q j)-gamma0CuspUpperForcingCombination N q A hA c) :=
  gamma0CuspUpperTruncatedEnergy_sum_pencil N q A hA hA2 c

def gamma0CompactForcingUpperEnergy (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (A : ℝ) (hA : 0<A) : gamma0EnergySpace N :=
  gamma0CompactForcingMatchedEnergy N ψ Y s+
    gamma0CuspUpperEnergyCombination N (1-s) A hA (gamma0CompactForcingMatchedCoefficient N ψ Y s)

def gamma0CompactForcingUpperForce (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (A : ℝ) (hA : 0<A) : Gamma0RegionL2 N :=
  gamma0CuspUpperForcingCombination N (1-s) A hA (gamma0CompactForcingMatchedCoefficient N ψ Y s)

theorem gamma0CompactForcingUpperEnergy_pencil (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (s : ℂ) (hs : gamma0HeightMatchingRegular N Y.height Y.pos s)
    (A : ℝ) (hA : 0<A) (hA2 : A≤1/2) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0CompactForcingUpperEnergy N ψ Y s A hA)=
      gamma0EnergyMassAdjoint N (gamma0SmoothSeedMass N ψ-gamma0CompactForcingUpperForce N ψ Y s A hA) := by
  have h := gamma0CuspUpperEnergyCombination_pencil N (1-s) A hA hA2
    (gamma0CompactForcingMatchedCoefficient N ψ Y s)
  rw [gamma0Eisenstein_reflect_parameter] at h
  rw [gamma0CompactForcingUpperEnergy,map_add,gamma0CompactForcingMatchedEnergy_pencil_regular N ψ Y s hs,h,
    ← map_add]
  congr 1
  unfold gamma0CompactForcingCorrectedMass gamma0CompactForcingUpperForce
  abel

def gamma0EisensteinUpperCombination (N : ℕ) [NeZero N] (s : ℂ)
    (A : ℝ) (hA : 0<A) (c : Gamma0EisensteinCuspClasses N → ℂ) : gamma0EnergySpace N :=
  gamma0EisensteinCriticalBaseEnergy N s c+
    gamma0CuspUpperEnergyCombination N s A hA c+
    gamma0CuspUpperEnergyCombination N (1-s) A hA ((gamma0CuspScatteringMatrix N s).mulVec c)

def gamma0EisensteinUpperForceCombination (N : ℕ) [NeZero N] (s : ℂ)
    (A : ℝ) (hA : 0<A) (c : Gamma0EisensteinCuspClasses N → ℂ) : Gamma0RegionL2 N :=
  gamma0CuspUpperForcingCombination N s A hA c+
    gamma0CuspUpperForcingCombination N (1-s) A hA ((gamma0CuspScatteringMatrix N s).mulVec c)

theorem gamma0EisensteinUpperCombination_pencil (N : ℕ) [NeZero N] (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s) (A : ℝ) (hA : 0<A) (hA2 : A≤1/2)
    (c : Gamma0EisensteinCuspClasses N → ℂ) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0EisensteinUpperCombination N s A hA c)=
      gamma0EnergyMassAdjoint N (-gamma0EisensteinUpperForceCombination N s A hA c) := by
  have hi := gamma0CuspUpperEnergyCombination_pencil N s A hA hA2 c
  have ho := gamma0CuspUpperEnergyCombination_pencil N (1-s) A hA hA2 ((gamma0CuspScatteringMatrix N s).mulVec c)
  rw [gamma0Eisenstein_reflect_parameter] at ho
  rw [gamma0EisensteinUpperCombination,map_add,map_add,gamma0EisensteinCriticalBaseEnergy_pencil N s hs c,
    hi,ho,← map_add,← map_add]
  congr 1
  unfold gamma0EisensteinUpperForceCombination gamma0CuspChannelForcing
  rw [neg_add_rev]
  abel

theorem gamma0EisensteinUpperCombination_test (N : ℕ) [NeZero N] (s : ℂ)
    (φ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N φ)
    (A : ℝ) (hA : 0<A) (hcut : Y.height≤1/A) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    inner ℂ (gamma0SmoothSeedMass N φ) (gamma0EnergyInclusion N (gamma0EisensteinUpperCombination N s A hA c))=
      ∑ i,c i * gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) φ s := by
  let r := gamma0EisensteinCuspClassRepresentative N
  let M := gamma0CuspScatteringMatrix N s
  let L := (innerSL ℂ (gamma0SmoothSeedMass N φ)).comp (gamma0EnergyInclusion N)
  let T (q : ℂ) (j : Gamma0EisensteinCuspClasses N) :=
    (2:ℂ)*gamma0EisensteinCutoffCompactTest N (r j) φ q
  have hT (q : ℂ) (j : Gamma0EisensteinCuspClasses N) :
      L (gamma0CuspUpperTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N j) q A hA)=T q j :=
    gamma0CuspUpperTruncatedEnergy_test_eq_cutoff N φ Y (r j) q A hA hcut
  change L (gamma0EisensteinUpperCombination N s A hA c)=_
  simp only [gamma0EisensteinUpperCombination,gamma0EisensteinCriticalBaseEnergy,
    gamma0CuspUpperEnergyCombination,map_add,map_sum,map_smul]
  simp_rw [hT]
  let E (j : Gamma0EisensteinCuspClasses N) := gamma0CuspEisensteinMatchedTruncatedEnergy N (r j) s
  change (∑ j,c j • L (E j))+(∑ j,c j • T s j)+(∑ j,M.mulVec c j • T (1-s) j)=
    ∑ i,c i • (T s i+L (E i)+∑ j,M j i • T (1-s) j)
  simp only [smul_add,Finset.sum_add_distrib,spectralSum_smul_matrix_mulVec M c (T (1-s))]
  abel

end ArtinMatthews
