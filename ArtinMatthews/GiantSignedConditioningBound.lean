module

public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSmallConditioningNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The finite small-map estimate is summed over all original big active
labels and all pending memory degrees with their factorial measures. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedSmallConditioning_energy_of_bound {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (q L : ℝ) (hL : 0 ≤ L)
    (hSmall : ∀ f : GiantTwoSidedResidueState PS (k+ell) → ℂ,
      (∑ d : MarkedPhysicalMarking PS k,
        giantSmallResidueEnergy (giantSmallConditioningMap PS k ell q d f)) ≤
          L * giantSmallStateEnergy f)
    (w : GiantSignedState PS PB (k+ell) → ℂ) :
    (∑ d : MarkedPhysicalMarking PS k,
      giantSignedAmbientEnergy PS ν (giantSignedSmallConditioning PS q d w)) ≤
        ENNReal.ofReal L * giantSignedStateEnergy PS ν w := by
  classical
  have hsmall (a : MarkedPhysicalMarking PB (k+ell)) (m : GiantSignedMemory PB) :
      (∑ d : MarkedPhysicalMarking PS k,
        ENNReal.ofReal (giantSmallResidueEnergy
          (giantSmallConditioningMap PS k ell q d (fun s => w (s, a, m))))) ≤
        ENNReal.ofReal L * ENNReal.ofReal (giantSmallStateEnergy (fun s => w (s, a, m))) := by
    have hpos (d : MarkedPhysicalMarking PS k) : 0 ≤
        giantSmallResidueEnergy (giantSmallConditioningMap PS k ell q d (fun s => w (s, a, m))) :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun d _ => hpos d), ← ENNReal.ofReal_mul hL]
    exact ENNReal.ofReal_le_ofReal (hSmall (fun s => w (s, a, m)))
  simp_rw [giantSignedAmbientEnergy_smallFibers PS ν hν]
  rw [giantSignedStateEnergy_smallFibers PS hV ν hν]
  have hcomm : (∑ d : MarkedPhysicalMarking PS k,
      ∑' m : GiantSignedMemory PB, ∑ a : MarkedPhysicalMarking PB (k+ell),
        ENNReal.ofReal (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) *
          ENNReal.ofReal (giantSmallResidueEnergy (fun y => giantSignedSmallConditioning PS q d w y a m))) =
      ∑' m : GiantSignedMemory PB, ∑ a : MarkedPhysicalMarking PB (k+ell),
        ∑ d : MarkedPhysicalMarking PS k,
          ENNReal.ofReal (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) *
            ENNReal.ofReal (giantSmallResidueEnergy (fun y => giantSignedSmallConditioning PS q d w y a m)) := by
    calc
      _ = ∑' d : MarkedPhysicalMarking PS k,
          ∑' m : GiantSignedMemory PB, ∑ a : MarkedPhysicalMarking PB (k+ell),
            ENNReal.ofReal (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) *
              ENNReal.ofReal (giantSmallResidueEnergy (fun y => giantSignedSmallConditioning PS q d w y a m)) :=
        (tsum_fintype _).symm
      _ = ∑' m : GiantSignedMemory PB, ∑' d : MarkedPhysicalMarking PS k,
          ∑ a : MarkedPhysicalMarking PB (k+ell),
            ENNReal.ofReal (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) *
              ENNReal.ofReal (giantSmallResidueEnergy (fun y => giantSignedSmallConditioning PS q d w y a m)) :=
        ENNReal.tsum_comm
      _ = _ := by
        simp only [tsum_fintype]
        apply tsum_congr
        intro m
        exact Finset.sum_comm
  rw [hcomm, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro m
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  calc
    _ = ENNReal.ofReal (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) *
        ∑ d : MarkedPhysicalMarking PS k,
          ENNReal.ofReal (giantSmallResidueEnergy
            (giantSmallConditioningMap PS k ell q d (fun s => w (s, a, m)))) := by
      rw [Finset.mul_sum]
      rfl
    _ ≤ ENNReal.ofReal (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) *
        (ENNReal.ofReal L * ENNReal.ofReal (giantSmallStateEnergy (fun s => w (s, a, m)))) :=
      mul_le_mul_right (hsmall a m) _
    _ = _ := by ac_rfl

theorem giantSignedSmallConditioning_energy {k ell : ℕ}
    (hP : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (q B₀ : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hB : 0 ≤ B₀)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ B₀)
    (w : GiantSignedState PS PB (k+ell) → ℂ) :
    (∑ d : MarkedPhysicalMarking PS k,
      giantSignedAmbientEnergy PS ν (giantSignedSmallConditioning PS q d w)) ≤
        ENNReal.ofReal (B₀ ^ Fintype.card S) * giantSignedStateEnergy PS ν w :=
  giantSignedSmallConditioning_energy_of_bound PS hV ν hν q (B₀ ^ Fintype.card S)
    (pow_nonneg hB _) (giantSmallConditioning_norm_sum hP hdis hV hq hq1 hB hbudget) w

end
end ArtinMatthews
