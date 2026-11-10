module

public import ArtinMatthews.SourceFiniteKP2Cover
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The rank-one torus inside the actual local cubic cover. Its
ordinary diagonal section has precisely the square of the actual
cubic Hilbert symbol as multiplier. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

def sourceGL2DiagonalHom (F : Type*) [Field F] : Fˣ →* GL (Fin 2) F where
  toFun := sourceGL2Diagonal
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sourceGL2Diagonal]
  map_mul' y z := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceGL2Diagonal_eq_det {F : Type*} [Field F] (g : GL (Fin 2) F)
    (hg : g ∈ (sourceGL2DiagonalHom F).range) :
    g = sourceGL2Diagonal (GeneralLinearGroup.det g) := by
  obtain ⟨y, rfl⟩ := hg
  change sourceGL2Diagonal y = sourceGL2Diagonal (GeneralLinearGroup.det (sourceGL2Diagonal y))
  rw [sourceGL2Diagonal_det]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceFiniteKPRankOneSubgroup : Subgroup (SourceFiniteKP2Cover K hζ P) :=
  (sourceGL2DiagonalHom (P.adicCompletion K)).range.comap (sourceFiniteKP2Projection K hζ P)

abbrev SourceFiniteKPRankOneTorus := sourceFiniteKPRankOneSubgroup K hζ P

def sourceFiniteKPRankOneBase : SourceFiniteKPRankOneTorus K hζ P →* (P.adicCompletion K)ˣ :=
  GeneralLinearGroup.det.comp ((sourceFiniteKP2Projection K hζ P).comp
    (sourceFiniteKPRankOneSubgroup K hζ P).subtype)

theorem sourceFiniteKPRankOne_base_eq (g : SourceFiniteKPRankOneTorus K hζ P) :
    g.val.base = sourceGL2Diagonal (sourceFiniteKPRankOneBase K hζ P g) :=
  sourceGL2Diagonal_eq_det g.val.base g.property

def sourceFiniteKPRankOneLift (y : (P.adicCompletion K)ˣ) : SourceFiniteKPRankOneTorus K hζ P :=
  ⟨sourceFiniteKP2Lift K hζ P (sourceGL2Diagonal y), ⟨y, rfl⟩⟩

theorem sourceFiniteKPRankOneLift_base (y : (P.adicCompletion K)ˣ) :
    sourceFiniteKPRankOneBase K hζ P (sourceFiniteKPRankOneLift K hζ P y) = y :=
  sourceGL2Diagonal_det y

def sourceFiniteKPRankOneCenter : rootsOfUnity 3 (P.adicCompletion K) →* SourceFiniteKPRankOneTorus K hζ P :=
  (sourceFiniteKP2Center K hζ P).codRestrict _ (fun _ => ⟨1, map_one _⟩)

theorem sourceFiniteKPRankOneCenter_base (z : rootsOfUnity 3 (P.adicCompletion K)) :
    sourceFiniteKPRankOneBase K hζ P (sourceFiniteKPRankOneCenter K hζ P z) = 1 := by
  change GeneralLinearGroup.det (1 : GL (Fin 2) (P.adicCompletion K)) = 1
  exact map_one _

theorem sourceFiniteKP2Multiplier_rankOne (y z : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal y) (sourceGL2Diagonal z) =
      sourceFiniteKPHilbert K hζ P y z ^ 2 := by
  have hm : sourceGL2Diagonal (y * z) = sourceGL2Diagonal y * sourceGL2Diagonal z :=
    (sourceGL2DiagonalHom (P.adicCompletion K)).map_mul y z
  have hx : sourceKubotaX (sourceGL2Diagonal y * sourceGL2Diagonal z) = 1 := by
    rw [← hm, sourceKubotaX_diagonal]
  simp [sourceFiniteKP2Multiplier, sourceKP2Multiplier, hx, sourceKubotaX_diagonal, sourceGL2Diagonal_det]

theorem sourceFiniteKPRankOne_mul_central (x y : SourceFiniteKPRankOneTorus K hζ P) :
    (x * y).val.central = x.val.central * y.val.central *
      sourceFiniteKPHilbert K hζ P (sourceFiniteKPRankOneBase K hζ P x)
        (sourceFiniteKPRankOneBase K hζ P y) ^ 2 := by
  change x.val.central * y.val.central * sourceFiniteKP2Multiplier K hζ P x.val.base y.val.base = _
  rw [sourceFiniteKPRankOne_base_eq K hζ P x, sourceFiniteKPRankOne_base_eq K hζ P y,
    sourceFiniteKP2Multiplier_rankOne]

end
end ArtinMatthews
