module

public import ArtinMatthews.SpectralCompactResolventOutgoingMode
public import ArtinMatthews.SpectralCompactResolventHeightResponse
public import ArtinMatthews.SpectralCompactResolventHeightModes
public import ArtinMatthews.SpectralEisensteinMatchingDefects
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

/-! Exact decomposition of the full ambient resolvent of an actual
compact seed into its truncated energy response and its genuine outgoing
tails at the chosen cutoff. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspChannelForcing (N : ℕ) [NeZero N] (q : ℂ) (i : Gamma0EisensteinCuspClasses N) :
    Gamma0RegionL2 N :=
  gamma0CuspEisensteinCompactForcingMass N (gamma0EisensteinCuspClassRepresentative N i) q

def gamma0CompactForcingResolventTrueCoefficient (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) (i : Gamma0EisensteinCuspClasses N) : ℂ :=
  Classical.choose (gamma0CompactForcingResolvent_normalized_outgoing_mode N ψ A
    (gamma0EisensteinCuspClassRepresentative N i) s hs)

theorem gamma0CompactForcingResolventTrueCoefficient_mode (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) (i : Gamma0EisensteinCuspClasses N) :
    let r := gamma0EisensteinCuspClassRepresentative N i
    gamma0CuspConstantTerm N r A.height A.pos
      (gamma0EnergyInclusion N (gamma0CompactForcingResolventEnergy N ψ s hs))=
      gamma0CompactForcingResolventTrueCoefficient N ψ A s hs i •
        gamma0CuspOutgoingTailAt N r (1-s) (gamma0Eisenstein_reflect_realPart hs.1) A.height A.pos := by
  dsimp only
  let r := gamma0EisensteinCuspClassRepresentative N i
  let hq := gamma0Eisenstein_reflect_realPart hs.1
  let B := gamma0CompactForcingResolventTrueCoefficient N ψ A s hs i
  let M := gamma0AmbientResolventFamily N (s*(1-s)) (gamma0SmoothSeedMass N ψ)
  have hRaw : gamma0GlobalCuspConstantTerm N r M
      =ᵐ[volume.restrict (Ioi A.height)] fun y => B*((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^(1-s) :=
    Classical.choose_spec (gamma0CompactForcingResolvent_normalized_outgoing_mode N ψ A r s hs)
  have hMode := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) A.pos).mpr hRaw
  have hConst := (gamma0GlobalCuspConstantTerm_ae N r M A.height A.pos).symm.trans hMode
  rw [gamma0CompactForcingResolventEnergy_mass N ψ s hs]
  apply Lp.ext
  filter_upwards [hConst,gamma0CuspOutgoingTailAt_ae N r (1-s) hq A.height A.pos (A.high r),
    Lp.coeFn_smul B (gamma0CuspOutgoingTailAt N r (1-s) hq A.height A.pos)] with y hy ht hh
  change (gamma0CuspConstantTerm N r A.height A.pos M) y =
    (B • gamma0CuspOutgoingTailAt N r (1-s) hq A.height A.pos) y
  rw [hy,hh,Pi.smul_apply,ht,smul_eq_mul]

def gamma0CompactForcingCorrectedMass (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (s : ℂ) (c : Gamma0EisensteinCuspClasses N → ℂ) : Gamma0RegionL2 N :=
  gamma0SmoothSeedMass N ψ-∑ i,c i • gamma0CuspChannelForcing N (1-s) i

def gamma0CompactForcingResolventActualOutgoing (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) : gamma0EnergySpace N :=
  ∑ i,gamma0CompactForcingResolventTrueCoefficient N ψ A s hs i •
    gamma0CuspOutgoingCutoffEnergy N (gamma0EisensteinCuspClassRepresentative N i)
      (1-s) (gamma0Eisenstein_reflect_realPart hs.1)

def gamma0CompactForcingResolventActualTruncated (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) : gamma0EnergySpace N :=
  gamma0CompactForcingResolventEnergy N ψ s hs-gamma0CompactForcingResolventActualOutgoing N ψ A s hs

theorem gamma0CompactForcingResolventActualTruncated_mem (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0CompactForcingResolventActualTruncated N ψ A s hs∈
      (gamma0TruncatedFormData N A.height A.pos).subspace := by
  apply (gamma0TruncatedFormData_mem_iff_cusp_representatives N A.height A.pos _).mpr
  intro i
  let r := gamma0EisensteinCuspClassRepresentative N i
  change gamma0CuspConstantTerm N r A.height A.pos _=0
  rw [gamma0CompactForcingResolventActualTruncated,map_sub,map_sub,
    gamma0CompactForcingResolventTrueCoefficient_mode N ψ A s hs i,
    gamma0CompactForcingResolventActualOutgoing,
    gamma0CuspOutgoingCutoffEnergy_sum_atHeight_mode N r _ _ _ A.height A.pos (A.high r)]
  have hclass : gamma0EisensteinCuspClass N r=i := gamma0EisensteinCuspClassRepresentative_class N i
  rw [hclass,sub_self]

theorem gamma0CompactForcingResolventActualTruncated_pencil (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0CompactForcingResolventActualTruncated N ψ A s hs)=
      gamma0EnergyMassAdjoint N (gamma0CompactForcingCorrectedMass N ψ s
        (gamma0CompactForcingResolventTrueCoefficient N ψ A s hs)) := by
  rw [gamma0CompactForcingResolventActualTruncated,map_sub,
    gamma0CompactForcingResolventEnergy_pencil N ψ s hs,gamma0CompactForcingCorrectedMass,map_sub]
  congr 1
  simp only [gamma0CompactForcingResolventActualOutgoing,map_sum,map_smul,gamma0CuspChannelForcing]
  apply Finset.sum_congr rfl
  intro i _
  rw [← gamma0Eisenstein_reflect_parameter s,gamma0CuspOutgoingCutoffEnergy_pencil]

theorem gamma0CompactForcingResolventActualTruncated_eq_response (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0CompactForcingResolventActualTruncated N ψ A s hs=
      gamma0HeightMatchingResponse N A.height A.pos s (gamma0CompactForcingCorrectedMass N ψ s
        (gamma0CompactForcingResolventTrueCoefficient N ψ A s hs)) :=
  gamma0HeightMatchingResponse_unique_of_pencil N A.height A.pos s
    (gamma0HeightMatchingForm_not_exceptional N A.height A.pos _ hs.2) _ _
    (gamma0CompactForcingResolventActualTruncated_mem N ψ A s hs)
    (gamma0CompactForcingResolventActualTruncated_pencil N ψ A s hs)

theorem gamma0CompactForcingResolventActualDefect_zero (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0HeightMatchingDefect N A.height A.pos s (gamma0CompactForcingCorrectedMass N ψ s
      (gamma0CompactForcingResolventTrueCoefficient N ψ A s hs))=0 := by
  change gamma0EnergyResolventPencil N (s*(1-s)) (gamma0HeightMatchingResponse N A.height A.pos s _)-
    gamma0EnergyMassAdjoint N _=0
  rw [← gamma0CompactForcingResolventActualTruncated_eq_response N ψ A s hs,
    gamma0CompactForcingResolventActualTruncated_pencil N ψ A s hs,sub_self]

end ArtinMatthews
