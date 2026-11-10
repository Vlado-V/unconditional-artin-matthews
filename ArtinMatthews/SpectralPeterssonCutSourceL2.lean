module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralPeterssonCutPacket
public import ArtinMatthews.SpectralPeterssonHilbert
public import ArtinMatthews.SpectralPeterssonCutMeasurable
public import ArtinMatthews.SpectralPeterssonCutPacketNorm
public import ArtinMatthews.SpectralPeterssonPhysicalCauchy
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized single cut vectors belong to the native
Petersson L2 space at infinity and at every exact-divisor cusp. -/
noncomputable section
open Set Matrix MeasureTheory UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

private theorem cutPacket_unit_eq (N k : ℕ) [NeZero N] (a : SL(2, ℤ))
    (n : ℕ+) (A : ℝ) :
    gamma0PeterssonCutPacket N a k (Finset.univ : Finset Unit) (fun _ => (1 : ℂ)) (fun _ => n) A =
      fun z => (spectralPeterssonNormalization k n : ℂ)*gamma0PeterssonTruncatedPoincare N a k n A z := by
  funext z
  simp [gamma0PeterssonCutPacket]

theorem gamma0PeterssonCutSourceInfinity_memLp (N k : ℕ) [NeZero N] (hk : 2 ≤ k)
    (n : ℕ+) (A : ℝ) (hA : 0 < A) :
    MemLp (spectralPeterssonHilbertProfile k (fun z =>
      (spectralPeterssonNormalization k n : ℂ)*gamma0PeterssonTruncatedPoincare N 1 k n A z)) 2
      (volume.restrict (gamma0InteriorRegion N)) := by
  have hinj : Set.InjOn (fun _ : Unit => n) ((Finset.univ : Finset Unit) : Set Unit) :=
    fun _ _ _ _ _ => Subsingleton.elim _ _
  have hI := (gamma0PeterssonCutPacket_infinity_norm N k hk (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) hA (show 0 < (n : ℝ) by positivity) hinj (fun _ _ => le_rfl)).1
  have hm := gamma0PeterssonCutPacket_measurable N 1 k (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) hA
  apply spectralPeterssonHilbertProfile_memLp_of_integrable N k _
  · simpa only [cutPacket_unit_eq] using hm
  · simpa [gamma0PeterssonCutPacket] using! hI

theorem gamma0PeterssonCutSourceAtkin_memLp (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (k : ℕ) (hk : 2 ≤ k) (n : ℕ+) (A : ℝ) (hA : 0 < A) :
    MemLp (spectralPeterssonHilbertProfile k (fun z =>
      (spectralPeterssonNormalization k n : ℂ)*
        gamma0PeterssonTruncatedPoincare (r*s) (gamma0CuspOneOver s) k n A z)) 2
      (volume.restrict (gamma0InteriorRegion (r*s))) := by
  have hinj : Set.InjOn (fun _ : Unit => n) ((Finset.univ : Finset Unit) : Set Unit) :=
    fun _ _ _ _ _ => Subsingleton.elim _ _
  have hI := (gamma0PeterssonCutPacket_mixed_norm r s hcop k hk (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) hA (show 0 < (n : ℝ) by positivity) hinj (fun _ _ => le_rfl)).1
  have hm := gamma0PeterssonCutPacket_measurable (r*s) (gamma0CuspOneOver s) k (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) hA
  apply spectralPeterssonHilbertProfile_memLp_of_integrable (r*s) k _
  · simpa only [cutPacket_unit_eq] using hm
  · simpa [gamma0PeterssonCutPacket] using! hI

end ArtinMatthews
