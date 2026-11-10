module

public import ArtinMatthews.SourceKPRetainedDiagonalSplit
public import ArtinMatthews.SourceKPAdelicRootSupportDecomposition
public import ArtinMatthews.SourceKPResidualUnitInitial
public import ArtinMatthews.SourceKPAdelicTorusUpper
public import ArtinMatthews.SourceKPRetainedExteriorProduct
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
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! Transport a rational diagonal through the literal seed average.
The original cubic phase is a single central factor outside the sum. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "Z" => sourceKPFiniteAdeleProjectiveCenter K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "B" => sourceKPRetainedFiniteBase K hζ
local notation "unitAt" => sourceKPRetainedUnitAt K
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "rUnit" => FiniteAdeleRing.unitEmbedding (𝓞 K) K

theorem sourceKPRetainedUnitAt_rational (P : Pr) (m : Kˣ) :
    unitAt P (rUnit m) = Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom m := by
  apply Units.ext
  rfl

theorem sourceKPRetainedResidualUnitTranslate_diagonal (m : Kˣ) (qf : Gf) :
    sourceKPCuspResidualUnitTranslate K hζ m qf = D (rUnit m)*qf := by
  change sourceKPFiniteAdeleProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m)*qf = _
  rw [sourceKPFiniteAdeleProjectiveRationalLift_diagonal]

private theorem exterior_diagonal_commute_seedTranslate
    (S : Finset Pr) (R M : S → ℕ) (a : 𝔸ᶠ[K]ˣ) (a₀ : A) (i : SourceKPRetainedSeedIndex K S R M) :
    Commute (D (sourceKPRetainedExteriorUnitPart K S a))
      (sourceKPRetainedSeedTranslate K hζ S R M (tuple 1 a₀ S).2 i) := by
  let b := sourceKPRetainedExteriorUnitPart K S a
  have ht : Commute (D b) (tuple 1 a₀ S).2 := by
    apply Commute.symm
    apply sourceKPRetainedExteriorTuple_commute K hζ a₀ S
    intro P hP
    rw [sourceKPRetainedFiniteBase_diagonal,
      sourceKPRetainedExteriorUnitPart_unitAt_mem K S a ⟨P,hP⟩, map_one]
  have hu (u : ∀ P : S, P.val.adicCompletion K) :
      Commute (D b) (Nf (∑ P : S, sourceKPFiniteAdditiveSingle K P.val (u P))) := by
    change D b * Nf _ = Nf _ * D b
    rw [sourceKPFiniteAdeleProjectiveDiagonalLift_upper,
      sourceKPRetainedExteriorUnit_mul_upperSum K S a u]
  rw [sourceKPRetainedSeedTranslate]
  exact (hu _).mul_right ht

theorem sourceKPRetainedDiagonal_mul_seedTranslate
    (S : Finset Pr) (R M : S → ℕ) (a : 𝔸ᶠ[K]ˣ) (a₀ : A)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ) (i : SourceKPRetainedSeedIndex K S R M) :
    let q₀ := (tuple 1 a₀ S).2
    let t := sourceKPRetainedSeedTranslate K hζ S R M q₀ i
    let b := sourceKPRetainedExteriorUnitPart K S a
    let r := sourceKPRetainedUnitPart K S a
    let v := sourceKPRetainedDiagonalUnit K S z
    let w := sourceKPRetainedDiagonalUnit K S (fun P => unitAt P.val a*z P)
    D a * D v * t = Z (sourceKPRetainedDiagonalPhase K hζ r v) * ((D w*t)*D b) := by
  intro q₀ t b r v w
  have hs : D a = D r * D b := sourceKPRetainedDiagonalLift_split K hζ S a
  have hv : Commute (D b) (D v) := sourceKPRetainedExteriorDiagonal_commute K hζ S a z
  have ht : Commute (D b) t := exterior_diagonal_commute_seedTranslate K hζ S R M a a₀ i
  have hrw : r*v = w := sourceKPRetainedDiagonalUnit_mul K S _ _
  calc
    _ = (D r*D v)*(t*D b) := by
      rw [hs, mul_assoc (D r), hv.eq, ← mul_assoc (D r), mul_assoc (D r*D v), ht.eq]
    _ = Z (sourceKPRetainedDiagonalPhase K hζ r v) * ((D w*t)*D b) := by
      rw [sourceKPRetainedDiagonalLift_mul_phase, hrw]
      simp only [mul_assoc]

end
end ArtinMatthews
