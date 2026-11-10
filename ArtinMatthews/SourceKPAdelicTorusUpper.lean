module

public import ArtinMatthews.SourceKPAdelicCubeTorus
public import ArtinMatthews.SourceKPAdelicUpper
public import ArtinMatthews.SourceKubotaMultipliers
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

/-! The exact torus action on the canonical upper-root splitting of
the actual cubic adelic projective cover. The compact cochain cancels
at every finite place, including the places above six. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

theorem sourceKPDiagonalHom_upper {R : Type*} [CommRing R] (a : Rˣ) (x : R) :
    sourceKPDiagonalHom R a * sourceKPUpperMatrix R x =
      sourceKPUpperMatrix R ((a : R) * x) * sourceKPDiagonalHom R a := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPDiagonalHom, sourceKPUpperMatrix, Matrix.mul_apply, Fin.sum_univ_two]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteTwistedMultiplier_upper_diagonal
    (P : HeightOneSpectrum (𝓞 K)) (a : (P.adicCompletion K)ˣ) (x : P.adicCompletion K) :
    sourceKPFiniteTwistedMultiplier K hζ P (sourceGL2Upper x) (sourceGL2Diagonal a) = 1 := by
  have hphase : sourceKPFinitePhase K hζ P (sourceGL2Upper x * sourceGL2Diagonal a) = 1 :=
    sourceKPFinitePhase_zero_left K hζ P _
      (by simp [sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two])
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist,
    sourceKPFinitePhase_upper, sourceKPFinitePhase_diagonal, hphase,
    one_mul, one_mul, div_one]
  exact sourceKP2Multiplier_upper_diagonal (sourceFiniteKPHilbert K hζ P) x a

theorem sourceKPFiniteTwistedMultiplier_diagonal_upper
    (P : HeightOneSpectrum (𝓞 K)) (a : (P.adicCompletion K)ˣ) (x : P.adicCompletion K) :
    sourceKPFiniteTwistedMultiplier K hζ P (sourceGL2Diagonal a) (sourceGL2Upper x) = 1 := by
  have hphase : sourceKPFinitePhase K hζ P (sourceGL2Diagonal a * sourceGL2Upper x) = 1 :=
    sourceKPFinitePhase_zero_left K hζ P _
      (by simp [sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two])
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist,
    sourceKPFinitePhase_diagonal, sourceKPFinitePhase_upper, hphase,
    one_mul, one_mul, div_one]
  exact sourceKP2Multiplier_diagonal_upper (sourceFiniteKPHilbert K hζ P) x a

theorem sourceKPAdeleMultiplier_upper_diagonal (a : 𝔸ᶠ[K]ˣ) (x : 𝔸ᶠ[K]) :
    sourceKPAdeleMultiplier K hζ (sourceKPUpperMatrix 𝔸ᶠ[K] x)
      (sourceKPDiagonalHom 𝔸ᶠ[K] a) = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt_upper, sourceKPAdeleMatrixAt,
    sourceKPDiagonalHom_map, sourceKPDiagonalHom_field,
    sourceKPFiniteTwistedMultiplier_upper_diagonal, map_one]

theorem sourceKPAdeleMultiplier_diagonal_upper (a : 𝔸ᶠ[K]ˣ) (x : 𝔸ᶠ[K]) :
    sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] a)
      (sourceKPUpperMatrix 𝔸ᶠ[K] x) = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt_upper, sourceKPAdeleMatrixAt,
    sourceKPDiagonalHom_map, sourceKPDiagonalHom_field,
    sourceKPFiniteTwistedMultiplier_diagonal_upper, map_one]

theorem sourceKPFiniteAdeleProjectiveDiagonalLift_upper (a : 𝔸ᶠ[K]ˣ) (x : 𝔸ᶠ[K]) :
    sourceKPFiniteAdeleProjectiveDiagonalLift K hζ a * sourceKPFiniteAdeleUpperLift K hζ x =
      sourceKPFiniteAdeleUpperLift K hζ ((a : 𝔸ᶠ[K]) * x) *
        sourceKPFiniteAdeleProjectiveDiagonalLift K hζ a := by
  change sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] a) *
      sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPUpperMatrix 𝔸ᶠ[K] x) =
    sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPUpperMatrix 𝔸ᶠ[K] ((a : 𝔸ᶠ[K]) * x)) *
      sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] a)
  rw [sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _
      (sourceKPAdeleMultiplier_diagonal_upper K hζ a x),
    sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _
      (sourceKPAdeleMultiplier_upper_diagonal K hζ a ((a : 𝔸ᶠ[K]) * x)),
    sourceKPDiagonalHom_upper]

theorem sourceKPAdelicProjectiveDiagonalLift_upper (a : IdeleGroup (𝓞 K) K) (x : 𝔸[K]) :
    sourceKPAdelicProjectiveDiagonalLift K hζ a * sourceKPAdelicUpperLift K hζ x =
      sourceKPAdelicUpperLift K hζ ((a : 𝔸[K]) * x) *
        sourceKPAdelicProjectiveDiagonalLift K hζ a := by
  apply Prod.ext
  · change ProjGenLinGroup.mk (sourceKPDiagonalHom (InfiniteAdeleRing K)
          (sourceKPIdeleInfiniteUnit K a)) *
        ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x.1) =
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K)
          ((sourceKPIdeleInfiniteUnit K a : InfiniteAdeleRing K) * x.1)) *
        ProjGenLinGroup.mk (sourceKPDiagonalHom (InfiniteAdeleRing K)
          (sourceKPIdeleInfiniteUnit K a))
    rw [← map_mul, ← map_mul, sourceKPDiagonalHom_upper]
  · exact sourceKPFiniteAdeleProjectiveDiagonalLift_upper K hζ (sourceKPIdeleFiniteUnit K a) x.2

theorem sourceKPAdelicProjectiveDiagonalLift_conj_upper (a : IdeleGroup (𝓞 K) K) (x : 𝔸[K]) :
    sourceKPAdelicProjectiveDiagonalLift K hζ a * sourceKPAdelicUpperLift K hζ x *
      (sourceKPAdelicProjectiveDiagonalLift K hζ a)⁻¹ =
        sourceKPAdelicUpperLift K hζ ((a : 𝔸[K]) * x) := by
  rw [sourceKPAdelicProjectiveDiagonalLift_upper, mul_inv_cancel_right]

theorem sourceKPAdelicTorus_upper_of_projection (g : SourceKPAdelicProjective K hζ)
    (a : IdeleGroup (𝓞 K) K)
    (hg : sourceKPAdelicProjectiveProjection K hζ g = sourceKPProjectiveDiagonalHom 𝔸[K] a)
    (x : 𝔸[K]) :
    g * sourceKPAdelicUpperLift K hζ x =
      sourceKPAdelicUpperLift K hζ ((a : 𝔸[K]) * x) * g := by
  have hker : g * (sourceKPAdelicProjectiveDiagonalLift K hζ a)⁻¹ ∈
      (sourceKPAdelicProjectiveProjection K hζ).ker := by
    change sourceKPAdelicProjectiveProjection K hζ
      (g * (sourceKPAdelicProjectiveDiagonalLift K hζ a)⁻¹) = 1
    rw [map_mul, map_inv, sourceKPAdelicProjectiveDiagonalLift_projection, hg, mul_inv_cancel]
  rw [← sourceKPAdelicProjective_exact K hζ] at hker
  obtain ⟨z, hz⟩ := hker
  have hfactor : g = sourceKPAdelicProjectiveCenter K hζ z *
      sourceKPAdelicProjectiveDiagonalLift K hζ a := by
    rw [hz, inv_mul_cancel_right]
  rw [hfactor, mul_assoc, sourceKPAdelicProjectiveDiagonalLift_upper,
    ← mul_assoc, (sourceKPAdelicProjectiveCenter_commute K hζ z
      (sourceKPAdelicUpperLift K hζ ((a : 𝔸[K]) * x))).eq, mul_assoc]

end
end ArtinMatthews
