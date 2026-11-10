module

public import ArtinMatthews.SourceFiniteKPMultipliers
public import ArtinMatthews.SourceKubotaDefect
public import ArtinMatthews.SourceKubotaGL2Generation
public import ArtinMatthews.SourceKubotaMultipliers
public import ArtinMatthews.SourceKubotaTriangularDefect
public import ArtinMatthews.SourceKubotaWeylSymbol
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The full arbitrary-matrix cocycle law for the literal determinant
modified Kubota multiplier, and its specialization to actual local
cubic reciprocity. No abstract cover or cocycle is an input. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F : Type*} [Field F] {A : Type*} [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))

theorem sourceKP2Defect_right_mul_formula (g h k l : GL (Fin 2) F) :
    sourceKP2Defect B g h (k * l) =
      sourceKP2Defect B g h k * sourceKP2Defect B g (h * k) l * sourceKP2Defect B h k l /
        sourceKP2Defect B (g * h) k l := by
  unfold sourceKP2Defect
  simp only [mul_assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_div, ofMul_mul]
  abel

theorem sourceKP2Defect_right_mul {k l : GL (Fin 2) F}
    (hk : ∀ g h, sourceKP2Defect B g h k = 1) (hl : ∀ g h, sourceKP2Defect B g h l = 1)
    (g h : GL (Fin 2) F) : sourceKP2Defect B g h (k * l) = 1 := by
  rw [sourceKP2Defect_right_mul_formula, hk, hl, hl, hl, one_mul, one_mul, div_self']

theorem sourceKP2Defect_eq_one (hdiag : ∀ x, B x x = 1)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (hsteinberg : ∀ x : Fˣ, ∀ hx : 1 - (x : F) ≠ 0, B x (Units.mk0 _ hx) = 1)
    (g h k : GL (Fin 2) F) : sourceKP2Defect B g h k = 1 := by
  have htri (z : GL (Fin 2) F) (hz : z 1 0 = 0) : ∀ a b, sourceKP2Defect B a b z = 1 := by
    obtain ⟨x, u, d, hfactor⟩ := sourceGL2_triangular_factor z hz
    rw [hfactor]
    exact sourceKP2Defect_right_mul B
      (sourceKP2Defect_right_mul B (fun a b => sourceKP2Defect_right_upper B hdiag a b x)
        (fun a b => sourceKP2Defect_right_diagonal B hdiag hminus a b u))
      (fun a b => sourceKP2Defect_right_scalar B hdiag a b d)
  by_cases hk : k 1 0 = 0
  · exact htri k hk g h
  · obtain ⟨b, x, hb, hfactor⟩ := sourceGL2_weyl_factor k hk
    rw [hfactor]
    exact sourceKP2Defect_right_mul B
      (sourceKP2Defect_right_mul B (htri b hb) (sourceKP2Defect_right_weyl B hdiag hminus hsteinberg))
      (fun a b => sourceKP2Defect_right_upper B hdiag a b x) g h

theorem sourceKP2Multiplier_cocycle (hdiag : ∀ x, B x x = 1)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (hsteinberg : ∀ x : Fˣ, ∀ hx : 1 - (x : F) ≠ 0, B x (Units.mk0 _ hx) = 1)
    (g h k : GL (Fin 2) F) :
    sourceKP2Multiplier B g h * sourceKP2Multiplier B (g * h) k =
      sourceKP2Multiplier B g (h * k) * sourceKP2Multiplier B h k :=
  (sourceKP2Defect_eq_one_iff B g h k).mp (sourceKP2Defect_eq_one B hdiag hminus hsteinberg g h k)

theorem sourceKP2Multiplier_one_left (g : GL (Fin 2) F) : sourceKP2Multiplier B 1 g = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_one]

theorem sourceKP2Multiplier_one_right (g : GL (Fin 2) F) : sourceKP2Multiplier B g 1 = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_one]

open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceFiniteKP2Multiplier_cocycle (g h k : GL (Fin 2) (P.adicCompletion K)) :
    sourceFiniteKP2Multiplier K hζ P g h * sourceFiniteKP2Multiplier K hζ P (g * h) k =
      sourceFiniteKP2Multiplier K hζ P g (h * k) * sourceFiniteKP2Multiplier K hζ P h k :=
  sourceKP2Multiplier_cocycle (sourceFiniteKPHilbert K hζ P)
    (sourceFiniteKPHilbert_diag K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P)
    (sourceFiniteKPHilbert_steinberg K hζ P) g h k

theorem sourceFiniteKP2Multiplier_one_left (g : GL (Fin 2) (P.adicCompletion K)) :
    sourceFiniteKP2Multiplier K hζ P 1 g = 1 := sourceKP2Multiplier_one_left _ g

theorem sourceFiniteKP2Multiplier_one_right (g : GL (Fin 2) (P.adicCompletion K)) :
    sourceFiniteKP2Multiplier K hζ P g 1 = 1 := sourceKP2Multiplier_one_right _ g

end
end ArtinMatthews
