module

public import ArtinMatthews.MarkedMinorArcSharedLattice
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Canonical actual shared-lattice coordinates, including exact scaled
determinant transport. -/
namespace ArtinMatthews

/-- Literal coordinates in Z*z+Z*D*w; divisibility will be proved from the
actual preserved prime-line tuple. -/
def markedMinorSharedCoordinates (D : ℕ) (z w v : ℤ × ℤ) : ℤ × ℤ :=
  (markedMinorIntegerDet v w,markedMinorIntegerDet z v/(D : ℤ))

theorem markedMinorSharedCoordinates_decompose {D : ℕ} (hD : D ≠ 0)
    (z w v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hv : (D : ℤ) ∣ markedMinorIntegerDet z v) :
    v.1=(markedMinorSharedCoordinates D z w v).1*z.1+
      (D : ℤ)*(markedMinorSharedCoordinates D z w v).2*w.1 ∧
    v.2=(markedMinorSharedCoordinates D z w v).1*z.2+
      (D : ℤ)*(markedMinorSharedCoordinates D z w v).2*w.2 := by
  obtain ⟨l,hl⟩ := hv
  have hDn : (D : ℤ) ≠ 0 := by exact_mod_cast hD
  have hj : markedMinorIntegerDet z v/(D : ℤ)=l := by
    rw [hl,Int.mul_ediv_cancel_left _ hDn]
  have hb := markedMinorIntegerBasis_decompose z w v hd
  rw [hl] at hb
  simpa only [markedMinorSharedCoordinates,hj] using hb

/-- On the genuine shared lattice, the canonical coordinates are injective. -/
theorem markedMinorSharedCoordinates_inj {D : ℕ} (hD : D ≠ 0)
    (z w u v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hu : (D : ℤ) ∣ markedMinorIntegerDet z u) (hv : (D : ℤ) ∣ markedMinorIntegerDet z v)
    (he : markedMinorSharedCoordinates D z w u=markedMinorSharedCoordinates D z w v) : u=v := by
  have h₁ := markedMinorSharedCoordinates_decompose hD z w u hd hu
  have h₂ := markedMinorSharedCoordinates_decompose hD z w v hd hv
  rw [he] at h₁
  exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)

/-- The actual position determinant divided by the shared product D is
exactly the ordinary determinant in the canonical integer coordinates. -/
theorem markedMinorSharedCoordinates_determinant {D : ℕ} (hD : D ≠ 0)
    (z w u v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hu : (D : ℤ) ∣ markedMinorIntegerDet z u) (hv : (D : ℤ) ∣ markedMinorIntegerDet z v) :
    markedMinorIntegerDet u v/(D : ℤ)=markedMinorIntegerDet
      (markedMinorSharedCoordinates D z w u) (markedMinorSharedCoordinates D z w v) := by
  have h₁ := markedMinorSharedCoordinates_decompose hD z w u hd hu
  have h₂ := markedMinorSharedCoordinates_decompose hD z w v hd hv
  have he : markedMinorIntegerDet u v=(D : ℤ)*markedMinorIntegerDet
      (markedMinorSharedCoordinates D z w u) (markedMinorSharedCoordinates D z w v)*
        markedMinorIntegerDet z w := by
    unfold markedMinorIntegerDet
    rw [h₁.1,h₁.2,h₂.1,h₂.2]
    ring
  rw [he,hd,mul_one,Int.mul_ediv_cancel_left _ (by exact_mod_cast hD : (D : ℤ)≠0)]

end ArtinMatthews
