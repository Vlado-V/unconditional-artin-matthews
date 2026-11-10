module

public import ArtinMatthews.MarkedMinorArcDirtyAnchor
public import ArtinMatthews.MarkedMinorArcRawGoodFirst
public import ArtinMatthews.MarkedMinorArcBanNeighbors
public import ArtinMatthews.MarkedMinorArcDirtyRawAnchor
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Actual primitive target coordinates, not hypothesized integer anchors. -/
namespace ArtinMatthews

theorem markedRawDirty_target_anchor_residue_unique {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    {Q : Finset Nat.Primes} (a : MarkedRawParticle Q)
    (hban : ∀ j k, (source j k).1 ≠ a.1.1)
    (D₁ D₂ Z₁ Z₂ T₁ T₂ : ℤ) (z w v₁ v₂ : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1)
    (hv₁ : IsCoprime v₁.1 v₁.2) (hv₂ : IsCoprime v₂.1 v₂.2)
    (hj₁ : markedMinorIntegerDet z v₁=markedMinorDirtyDeterminant
      (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₁ (a.1.1:ℕ) Z₁ T₁)
    (hj₂ : markedMinorIntegerDet z v₂=markedMinorDirtyDeterminant
      (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₂ (a.1.1:ℕ) Z₂ T₂)
    (ha : MarkedRawParticleHits Q v₁ hv₁ a) (hb : MarkedRawParticleHits Q v₂ hv₂ a) :
    (markedMinorIntegerDet v₁ w : ZMod (a.1.1:ℕ))=
      (markedMinorIntegerDet v₂ w : ZMod (a.1.1:ℕ)) := by
  have hl := markedRawParticleHits_same_line a v₁ v₂ hv₁ hv₂ ha hb
  have he₁ := markedBan_neighbor_decomposition z w v₁ hd
  have he₂ := markedBan_neighbor_decomposition z w v₂ hd
  rw [hj₁] at he₁
  rw [hj₂] at he₂
  have hl' : MarkedMinorSamePrimeLine (a.1.1:ℕ)
      (markedMinorDirtyPosition z w (markedMinorIntegerDet v₁ w) (markedMinorDirtyDeterminant
        (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₁ (a.1.1:ℕ) Z₁ T₁))
      (markedMinorDirtyPosition z w (markedMinorIntegerDet v₂ w) (markedMinorDirtyDeterminant
        (markedSourceFullProduct (markedRawNumericActive source):ℤ) D₂ (a.1.1:ℕ) Z₂ T₂)) := by
    rw [← he₁,← he₂]
    exact hl
  exact markedMinorDirty_anchor_residue_unique a.1.1.2 _ D₁ D₂ Z₁ Z₂ T₁ T₂ _ _
    (markedRawSourceFull_not_dvd_of_cross_ban source a hban) z w hd hl'

theorem markedRawDirty_target_anchor_proximity {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    {Q : Finset Nat.Primes} (a : MarkedRawParticle Q)
    (D Z T hstar : ℤ) (z w v : ℤ × ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hj : markedMinorIntegerDet z v=markedMinorDirtyDeterminant
      (markedSourceFullProduct (markedRawNumericActive source):ℤ) D (a.1.1:ℕ) Z T)
    (hh : Int.ModEq ((a.1.1:ℕ):ℤ) (markedMinorIntegerDet v w) hstar)
    (hbox : |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) :
    ‖(((D:ℝ)*Z*T*(markedMinorIntegerTau r w/markedMinorIntegerTau r z)-
      (((markedSourceFullProduct (markedRawNumericActive source):ℤ):ℝ)*
        (markedMinorIntegerTau r w/markedMinorIntegerTau r z)+hstar)/(a.1.1:ℕ):ℝ):AddCircle (1:ℝ))‖ ≤
      16/(a.1.1:ℕ) := by
  apply markedMinorDirty_anchor_proximity _ D Z T (markedMinorIntegerDet v w) hstar a.1.1.2.pos
    (markedMinorIntegerTau r w/markedMinorIntegerTau r z) hh
  rw [← hj,markedBan_neighbor_tau_identity r z w v hd hz]
  exact hbox

end ArtinMatthews
