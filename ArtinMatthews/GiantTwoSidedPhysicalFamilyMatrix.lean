module

public import ArtinMatthews.GiantTwoSidedResiduePathExpansion
public import ArtinMatthews.GiantTwoSidedPatternAdjoint
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

/-! The source physical operator on a finite slice is the literal
pattern family with the two normalized endpoint slot averages. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell : ℕ} {Z : Finset ℕ} {patterns : Finset I} {C : I → J → Finset (Fin k)}

def giantTwoSidedPhysicalChoiceCoefficient (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (choice : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell)
    (s t : GiantTwoSidedEndpointState P (k+ell) Z) : ℂ :=
  giantTwoSidedPatternPhysicalCoefficient step q ζ (K choice.1.val)
    (giantTwoSidedEndpointPermute choice.2.1 s)
    (giantTwoSidedEndpointPermute choice.2.2.1 t) choice.2.2.2

def giantTwoSidedPhysicalFamilyMatrix (patterns : Finset I) (C : I → J → Finset (Fin k))
    (step : ℤ) (q ζ : ℝ) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) :
    Matrix (GiantTwoSidedEndpointState P (k+ell) Z) (GiantTwoSidedEndpointState P (k+ell) Z) ℂ :=
  fun s t =>
    (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ) *
      ∑ choice : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell,
        giantTwoSidedPhysicalChoiceCoefficient step q ζ K choice s t

theorem giantTwoSidedPhysicalFamilyMatrix_adjoint
    (hP : ∀ j p, p ∈ P j → p.Prime) (patterns : Finset I) (C : I → J → Finset (Fin k))
    (step : ℤ) (q ζ : ℝ) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) :
    (giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns C step q ζ K)ᴴ =
      giantTwoSidedPhysicalFamilyMatrix (Z := Z) patterns C (-step) q (-ζ)
        (fun p a b aux => conj (K p b a aux)) := by
  let Choice := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell
  let e : Choice ≃ Choice :=
    { toFun := fun c => ⟨c.1,c.2.2.1,c.2.1,c.2.2.2⟩
      invFun := fun c => ⟨c.1,c.2.2.1,c.2.1,c.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  ext s t : 2
  change conj ((giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ) *
    ∑ c : Choice, giantTwoSidedPhysicalChoiceCoefficient step q ζ K c t s) = _
  simp only [map_mul, Complex.conj_ofReal, map_sum, giantTwoSidedPhysicalFamilyMatrix]
  congr 1
  rw [← e.sum_comp (fun c => giantTwoSidedPhysicalChoiceCoefficient (-step) q (-ζ)
    (fun p a b aux => conj (K p b a aux)) c s t)]
  apply Finset.sum_congr rfl
  intro c _
  exact giantTwoSidedPatternPhysicalCoefficient_conj hP step q ζ (K c.1.val)
    (giantTwoSidedEndpointPermute c.2.1 t) (giantTwoSidedEndpointPermute c.2.2.1 s) c.2.2.2

end
end ArtinMatthews
