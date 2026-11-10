module

public import ArtinMatthews.GiantSignedAmbientClean
public import ArtinMatthews.GiantSignedTotalPhase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}

/-- The original positive total product and its independently signed translation step. -/
def giantSignedTotalStepCleanPattern {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (C : B → Finset (Fin k)) (θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) : ℂ := by
  classical
  exact ∑ aux : GiantTwoSidedPatternAuxiliary PB C, (idealAuxiliaryMass auxLaw aux : ℂ) *
    ∑ b : MarkedPhysicalMarking PB (k + ell), if IdealCopied C a b then
      let D := d * (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
      (idealFreshTargetMass freshLaw C b : ℂ) * K a b aux *
        (D : ℂ) ^ ((ζ : ℂ) * Complex.I) * idealAdditivePhase θ D *
          f (giantTwoSidedResidueTranslate (κ * (D : ℤ)) y) b (giantSignedMemoryTranslate (κ * (D : ℤ)) m)
    else 0

/-- Exact total-product row adapter with the original integer transfer retained. -/
theorem giantSignedTotalStepCleanPattern_eq {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (C : B → Finset (Fin k)) (θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) :
    giantSignedTotalStepCleanPattern PS freshLaw auxLaw C θ ζ K d κ f y a m =
      (d : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        giantSignedAmbientCleanPattern PS freshLaw auxLaw C (θ * (d : ℝ)) ζ K (κ * (d : ℤ)) f y a m := by
  classical
  unfold giantSignedTotalStepCleanPattern giantSignedAmbientCleanPattern
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aux _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : IdealCopied C a b
  · simp only [hab, ite_true]
    rw [giantSignedTotalD_cpow, idealAdditivePhase_totalD]
    have hshift (D : ℕ) : κ * ((d * D : ℕ) : ℤ) = (D : ℤ) * (κ * (d : ℤ)) := by
      push_cast
      ring
    rw [hshift]
    ring
  · simp only [hab, ite_false, mul_zero]

/-- Both original pending half-dampings and slot averages surround the total clean row. -/
def giantSignedTotalStepCleanApply {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) : ℂ :=
  (giantSignedPendingDamping ρ m : ℂ) * idealSlotAverage
    (fun b => ∑ v ∈ patterns, giantSignedTotalStepCleanPattern PS freshLaw auxLaw (C v) θ ζ (K v) d κ
      (fun y' b' m' => idealSlotAverage (fun a' => (giantSignedPendingDamping ρ m' : ℂ) * f y' a' m') b')
      y b m) a

/-- Exact full-apply adapter, retaining both rho halves and both slot averages. -/
theorem giantSignedTotalStepCleanApply_eq {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) :
    giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ f y a m =
      (d : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C (θ * (d : ℝ)) ζ ρ K (κ * (d : ℤ)) f y a m := by
  classical
  unfold giantSignedTotalStepCleanApply giantSignedAmbientCleanApply
  simp_rw [giantSignedTotalStepCleanPattern_eq, ← Finset.mul_sum]
  rw [giantSignedActiveMultiplier_slotAverage]
  ring

/-- The fixed small spectral phase preserves the literal row norm. -/
theorem giantSignedTotalStepCleanApply_norm {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℕ) (hd : 0 < d) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) :
    ‖giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ f y a m‖ =
      ‖giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C (θ * (d : ℝ)) ζ ρ K (κ * (d : ℤ)) f y a m‖ := by
  rw [giantSignedTotalStepCleanApply_eq, norm_mul, giantSignedSmallD_cpow_norm d hd ζ, one_mul]

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val]

omit [∀ (g : B) (p : PB g), NeZero p.val] in
/-- The actual ambient energy is unchanged by the total-product adapter. -/
theorem giantSignedTotalStepCleanApply_energy_eq {I : Type*} {k ell : ℕ}
    (ν freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℕ) (hd : 0 < d) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ) :
    giantSignedAmbientEnergy PS ν (giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ f) =
      giantSignedAmbientEnergy PS ν
        (giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C (θ * (d : ℝ)) ζ ρ K (κ * (d : ℤ)) f) := by
  unfold giantSignedAmbientEnergy
  apply tsum_congr
  intro m
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  rw [giantSignedTotalStepCleanApply_norm PS freshLaw auxLaw patterns C θ ζ ρ K d hd κ f y a m]

end
end ArtinMatthews
