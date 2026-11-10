module

public import ArtinMatthews.SpectralEisensteinMatchingDefects
public import ArtinMatthews.SpectralEisensteinScatteringAnalytic
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

/-! Exact off-cut matching for the actual original continuation. Subtract
the genuine outgoing cutoffs with the actual scattering coefficients;
the remainder has zero cusp tails and solves the truncated equation. -/
noncomputable section
open Set
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0EisensteinMatchingTrueCoefficient (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (i : Gamma0EisensteinCuspClasses N) : ℂ :=
  gamma0CuspScatteringContinued N (gamma0EisensteinCuspClassRepresentative N i) a s

def gamma0EisensteinMatchingActualEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : s∈gamma0EisensteinContinuationDomain) : gamma0EnergySpace N :=
  gamma0AmbientWeakResolvent N (s*(1-s)) hs.2 (-gamma0CuspEisensteinCompactForcingMass N a s)

def gamma0EisensteinMatchingActualOutgoing (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : s∈gamma0EisensteinContinuationDomain) : gamma0EnergySpace N :=
  ∑ i, gamma0EisensteinMatchingTrueCoefficient N a s i •
    gamma0CuspOutgoingCutoffEnergy N (gamma0EisensteinCuspClassRepresentative N i)
      (1-s) (gamma0Eisenstein_reflect_realPart hs.1)

def gamma0EisensteinMatchingActualTruncated (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : s∈gamma0EisensteinContinuationDomain) : gamma0EnergySpace N :=
  gamma0EisensteinMatchingActualEnergy N a s hs-gamma0EisensteinMatchingActualOutgoing N a s hs

def gamma0EisensteinMatchingForcingCombination (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    Gamma0RegionL2 N :=
  -gamma0CuspEisensteinCompactForcingMass N a s-
    ∑ i, gamma0EisensteinMatchingTrueCoefficient N a s i •
      gamma0CuspEisensteinCompactForcingMass N (gamma0EisensteinCuspClassRepresentative N i) (1-s)

def gamma0EisensteinMatchingResponseCombination (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    gamma0EnergySpace N :=
  -gamma0EisensteinMatchingResponse N a s-
    ∑ i, gamma0EisensteinMatchingTrueCoefficient N a s i •
      gamma0EisensteinMatchingResponse N (gamma0EisensteinCuspClassRepresentative N i) (1-s)

theorem gamma0EisensteinMatchingActualEnergy_mass (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EnergyInclusion N (gamma0EisensteinMatchingActualEnergy N a s hs)=
      gamma0CuspEisensteinContinuedRemainder N a s := by
  rw [gamma0CuspEisensteinContinuedRemainder,gamma0AmbientResolventFamily_eq N (s*(1-s)) hs.2]
  rfl

theorem gamma0EisensteinMatchingActualTruncated_mem (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EisensteinMatchingActualTruncated N a s hs∈(gamma0EisensteinMatchingForm N).subspace := by
  apply (gamma0EisensteinMatchingForm_mem_iff N _).mpr
  intro i
  rw [gamma0EisensteinMatchingActualTruncated,map_sub,map_sub,gamma0EisensteinMatchingActualEnergy_mass,
    gamma0CuspEisensteinContinuedRemainder_matching_mode N _ a s hs (gamma0Eisenstein_reflect_realPart hs.1),
    gamma0EisensteinMatchingActualOutgoing,gamma0CuspOutgoingCutoffEnergy_sum_matching_mode,
    gamma0EisensteinCuspClassRepresentative_class]
  exact sub_self _

theorem gamma0EisensteinMatchingActualTruncated_pencil (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0EisensteinMatchingActualTruncated N a s hs)=
      gamma0EnergyMassAdjoint N (gamma0EisensteinMatchingForcingCombination N a s) := by
  rw [gamma0EisensteinMatchingActualTruncated,map_sub,gamma0EisensteinMatchingActualEnergy,
    gamma0AmbientWeakResolvent_pencil,gamma0EisensteinMatchingForcingCombination,map_sub]
  congr 1
  simp only [gamma0EisensteinMatchingActualOutgoing,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← gamma0Eisenstein_reflect_parameter s,gamma0CuspOutgoingCutoffEnergy_pencil]

theorem gamma0EisensteinMatchingResponse_reflected (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    gamma0EisensteinMatchingResponse N a (1-s)=
      (gamma0EisensteinMatchingForm N).energyResolvent (s*(1-s))
        (gamma0CuspEisensteinCompactForcingMass N a (1-s)) := by
  rw [gamma0EisensteinMatchingResponse,gamma0Eisenstein_reflect_parameter]

theorem gamma0EisensteinMatchingResponseCombination_resolvent (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) :
    (gamma0EisensteinMatchingForm N).energyResolvent (s*(1-s))
      (gamma0EisensteinMatchingForcingCombination N a s)=
        gamma0EisensteinMatchingResponseCombination N a s := by
  simp only [gamma0EisensteinMatchingForcingCombination,gamma0EisensteinMatchingResponseCombination,
    map_sub,map_neg,map_sum,map_smul,gamma0EisensteinMatchingResponse_reflected]
  rfl

theorem gamma0EisensteinMatchingActualTruncated_eq_response (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EisensteinMatchingActualTruncated N a s hs=gamma0EisensteinMatchingResponseCombination N a s := by
  rw [← gamma0EisensteinMatchingResponseCombination_resolvent]
  apply (gamma0EisensteinMatchingForm N).energyResolvent_unique _
    (gamma0EisensteinMatchingForm_not_exceptional N _ hs.2) _ _
    (gamma0EisensteinMatchingActualTruncated_mem N a s hs)
  intro v _
  let u := gamma0EisensteinMatchingActualTruncated N a s hs
  let F := gamma0EisensteinMatchingForcingCombination N a s
  have he := congrArg (fun w : gamma0EnergySpace N => inner ℂ v w)
    (gamma0EisensteinMatchingActualTruncated_pencil N a s hs)
  change inner ℂ v (gamma0EnergyResolventPencil N (s*(1-s)) u)=
    inner ℂ v (gamma0EnergyMassAdjoint N F) at he
  rw [gamma0EnergyResolventPencil_inner,gamma0EnergyMassAdjoint_inner] at he
  change inner ℂ v u-(s*(1-s)+1)*inner ℂ (gamma0EnergyInclusion N v) (gamma0EnergyInclusion N u)=
    inner ℂ (gamma0EnergyInclusion N v) F
  rw [gamma0FormEnergy_inner]
  linear_combination he

theorem gamma0EisensteinMatching_offcut_energy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EisensteinMatchingActualEnergy N a s hs=
      gamma0EisensteinMatchingResponseCombination N a s+gamma0EisensteinMatchingActualOutgoing N a s hs := by
  rw [← gamma0EisensteinMatchingActualTruncated_eq_response N a s hs,
    gamma0EisensteinMatchingActualTruncated,sub_add_cancel]

theorem gamma0EisensteinMatching_offcut_defect (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EisensteinMatchingDefect N a s +
      (∑ i, gamma0EisensteinMatchingTrueCoefficient N a s i • gamma0EisensteinOutgoingDefect N s i)=0 := by
  have he := gamma0EisensteinMatchingActualTruncated_pencil N a s hs
  rw [gamma0EisensteinMatchingActualTruncated_eq_response N a s hs] at he
  calc
    _ = gamma0EnergyMassAdjoint N (gamma0EisensteinMatchingForcingCombination N a s)-
      gamma0EnergyResolventPencil N (s*(1-s)) (gamma0EisensteinMatchingResponseCombination N a s) := by
        simp only [gamma0EisensteinMatchingDefect,gamma0EisensteinOutgoingDefect,
          gamma0EisensteinMatchingForcingCombination,gamma0EisensteinMatchingResponseCombination,
          gamma0Eisenstein_reflect_parameter,map_sub,map_neg,map_sum,map_smul,smul_sub,Finset.sum_sub_distrib]
        abel
    _=0 := sub_eq_zero.mpr he.symm

end ArtinMatthews
