module

public import ArtinMatthews.SourceReflectionPowerful
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField
open scoped NumberField Classical
noncomputable section

private def halfExponents {ι : Type*} (e : ι →₀ ℕ) : ι →₀ ℕ :=
  e.mapRange (fun n => n / 2) (by decide)

private def exponentSquarePartsEquiv (ι : Type*) :
    (ι →₀ ℕ) ≃ {e : ι →₀ ℕ // sourceReflectionIsSquarefree e} × (ι →₀ ℕ) where
  toFun e := (⟨sourceReflectionParity e, sourceReflectionParity_squarefree e⟩, halfExponents e)
  invFun p := p.1.val + 2 • p.2
  left_inv e := by
    ext P
    simp only [sourceReflectionParity, halfExponents, Finsupp.mapRange_apply, Finsupp.add_apply,
      Finsupp.smul_apply, Nat.nsmul_eq_mul]
    omega
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      ext P
      simp only [sourceReflectionParity, Finsupp.mapRange_apply, Finsupp.add_apply,
        Finsupp.smul_apply, Nat.nsmul_eq_mul]
      have h := p.1.property P
      omega
    · ext P
      simp only [halfExponents, Finsupp.mapRange_apply, Finsupp.add_apply,
        Finsupp.smul_apply, Nat.nsmul_eq_mul]
      have h := p.1.property P
      omega

variable (F : Type) [Field F] [NumberField F]

private def squarefreeExponentEquiv :
    {e : ProbePrime F →₀ ℕ // sourceReflectionIsSquarefree e} ≃
      {I : Ideal (𝓞 F) // Squarefree I} where
  toFun e := ⟨sourceFullExponentIdeal F e.val, (sourceFullExponentIdeal_squarefree_iff F _).2 e.property⟩
  invFun I := ⟨sourceFullIdealExponents F I.val, (sourceFullExponentIdeal_squarefree_iff F _).1
    (by rw [sourceFullIdealExponents_recover F I.val I.property.ne_zero]; exact I.property)⟩
  left_inv e := Subtype.ext ((sourceFullExponentIdealEquiv F).left_inv e.val)
  right_inv I := Subtype.ext (sourceFullIdealExponents_recover F I.val I.property.ne_zero)

/-- Unique squarefree-times-square factorization of the nonzero integral ideals. -/
def sourceQuadraticIdealSquareParts :
    {I : Ideal (𝓞 F) // I ≠ ⊥} ≃
      {I : Ideal (𝓞 F) // Squarefree I} × {I : Ideal (𝓞 F) // I ≠ ⊥} :=
  (sourceFullExponentIdealEquiv F).symm.trans
    ((exponentSquarePartsEquiv (ProbePrime F)).trans
      ((squarefreeExponentEquiv F).prodCongr (sourceFullExponentIdealEquiv F)))

theorem sourceQuadraticIdealSquareParts_symm_val
    (p : {I : Ideal (𝓞 F) // Squarefree I} × {I : Ideal (𝓞 F) // I ≠ ⊥}) :
    ((sourceQuadraticIdealSquareParts F).symm p).val = p.1.val * p.2.val ^ 2 := by
  change sourceFullExponentIdeal F
    (sourceFullIdealExponents F p.1.val + 2 • sourceFullIdealExponents F p.2.val) = _
  rw [sourceFullExponentIdeal_add, sourceFullExponentIdeal_nsmul,
    sourceFullIdealExponents_recover F _ p.1.property.ne_zero,
    sourceFullIdealExponents_recover F _ p.2.property]

theorem sourceQuadraticIdealSquareParts_val (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
    ((sourceQuadraticIdealSquareParts F I).1.val) *
      ((sourceQuadraticIdealSquareParts F I).2.val) ^ 2 = I.val := by
  rw [← sourceQuadraticIdealSquareParts_symm_val, Equiv.symm_apply_apply]

end
end ArtinMatthews.SourceEulerAssembly
