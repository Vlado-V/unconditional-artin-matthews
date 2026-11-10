module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace OAI

/-! Primary Eisenstein elements, residue characters, Gauss sums and first-moment target definitions. -/

section

noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def omega : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

def eisensteinRing : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {omega}
abbrev Eisenstein := eisensteinRing

def omegaE : Eisenstein :=
  ⟨omega, Algebra.subset_adjoin (Set.mem_singleton omega)⟩

def norm (a : Eisenstein) : ℝ := Complex.normSq (a : ℂ)

def normNat (a : Eisenstein) : ℕ := ⌊norm a⌋₊

def primary (a : Eisenstein) : Prop := (3 : Eisenstein) ∣ a - 1

def primaryPrime (a : Eisenstein) : Prop := primary a ∧ Prime a

def modulus (a : Eisenstein) : Ideal Eisenstein := Ideal.span {a}

abbrev Residues (a : Eisenstein) := Eisenstein ⧸ modulus a

def residueRepresentative (a : Eisenstein) (v : Residues a) : Eisenstein :=
  Classical.choose (Ideal.Quotient.mk_surjective v)

def cubicSymbolAtPrime (p v : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus p) v) then
    if h : ∃ j : Fin 3,
        Ideal.Quotient.mk (modulus p) (v ^ ((normNat p - 1) / 3)) =
          Ideal.Quotient.mk (modulus p) (omegaE ^ (j : ℕ)) then
      omega ^ ((Classical.choose h : Fin 3) : ℕ)
    else 0
  else 0

def additivePhase (p v : Eisenstein) : ℂ :=
  let z : ℂ := (v : ℂ) / (p : ℂ)
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z + star z))

def gaussAtPrime (p : Eisenstein) : ℂ :=
  (Real.sqrt (norm p) : ℂ)⁻¹ *
    ∑' v : Residues p,
      cubicSymbolAtPrime p (residueRepresentative p v) *
        additivePhase p (residueRepresentative p v)

def cStar : ℝ := (2 * Real.pi) ^ (2 / 3 : ℝ) / (3 * Real.Gamma (2 / 3))

def primeCutoffSum (f : Eisenstein → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Eisenstein, if primaryPrime p ∧ norm p ≤ X then f p else 0

def firstMomentScale (X : ℝ) : ℝ := X ^ (5 / 6 : ℝ) / Real.log X

def FirstMomentStatement : Prop :=
  Asymptotics.IsLittleO Filter.atTop
    (fun X : ℝ => primeCutoffSum gaussAtPrime X -
      (((6 / 5 : ℝ) * cStar * firstMomentScale X : ℝ) : ℂ))
    firstMomentScale

def theta (ℓ : ℤ) (a : Eisenstein) : ℂ := ((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ^ ℓ

def AngularComparisonStatement : Prop :=
  ∀ ℓ : ℤ, Asymptotics.IsLittleO Filter.atTop
    (primeCutoffSum (fun p => theta ℓ p *
       (gaussAtPrime p - ((cStar * norm p ^ (-1 / 6 : ℝ) : ℝ) : ℂ))))
    firstMomentScale

def AngularCancellationStatement : Prop :=
  ∀ ℓ : ℤ, ℓ ≠ 0 → Asymptotics.IsLittleO Filter.atTop
    (primeCutoffSum (fun p => theta ℓ p * gaussAtPrime p)) firstMomentScale

end CubicFirstMoment
end
end

end OAI
