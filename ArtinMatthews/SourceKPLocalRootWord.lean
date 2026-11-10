module

public import ArtinMatthews.SourceFiniteKP2Projective
public import ArtinMatthews.SourceKPCompactDiagonal
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

/-! The actual upper and lower root lifts generate lifts of square
projective diagonals. Their central phases are kept as elements of the
proved cubic kernel. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceKPLocalRootWeyl_matrix {F : Type*} [Field F] (u : Fˣ) :
    sourceGL2Upper (u : F) * sourceGL2Lower (-(u : F)⁻¹) * sourceGL2Upper (u : F) =
      sourceGL2Diagonal (u^2) * GeneralLinearGroup.scalar (Fin 2) u⁻¹ *
        (sourceGL2Upper (1 : F) * sourceGL2Lower (-1 : F) * sourceGL2Upper (1 : F)) := by
  let w := sourceGL2Upper (1 : F)*sourceGL2Lower (-1 : F)*sourceGL2Upper (1 : F)
  change _ = sourceGL2Diagonal (u^2)*GeneralLinearGroup.scalar (Fin 2) u⁻¹*w
  rw [mul_assoc (sourceGL2Diagonal (u^2)), GeneralLinearGroup.scalar_commute u⁻¹ w,
    ← mul_assoc (sourceGL2Diagonal (u^2)) w]
  apply GeneralLinearGroup.ext
  intro i j
  rw [sourceGL2_right_scalar_apply]
  fin_cases i <;> fin_cases j <;>
    simp [w, sourceGL2Upper, sourceGL2Lower, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, u.ne_zero] <;> (try field_simp [u.ne_zero]) <;> ring

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P
local notation "p₀" => sourceFiniteKP2ProjectiveProjection K hζ P
local notation "n₀" => fun x : L => l₀ (sourceGL2Upper x)
local notation "u₀" => fun x : L => l₀ (sourceGL2Lower x)

def sourceKPLocalRootSubgroup : Subgroup G :=
  Subgroup.closure (Set.range n₀ ∪ Set.range u₀)

def sourceKPLocalRootWeylWord (u : Lˣ) : G :=
  n₀ (u : L) * u₀ (-(u : L)⁻¹) * n₀ (u : L)

def sourceKPLocalRootDiagonalWord (u : Lˣ) : G :=
  sourceKPLocalRootWeylWord K hζ P u * (sourceKPLocalRootWeylWord K hζ P 1)⁻¹

theorem sourceKPLocalRootWeylWord_mem (u : Lˣ) :
    sourceKPLocalRootWeylWord K hζ P u ∈ sourceKPLocalRootSubgroup K hζ P := by
  let H := sourceKPLocalRootSubgroup K hζ P
  have hn (x : L) : n₀ x ∈ H := Subgroup.subset_closure (Or.inl ⟨x,rfl⟩)
  have hu (x : L) : u₀ x ∈ H := Subgroup.subset_closure (Or.inr ⟨x,rfl⟩)
  exact H.mul_mem (H.mul_mem (hn _) (hu _)) (hn _)

theorem sourceKPLocalRootDiagonalWord_mem (u : Lˣ) :
    sourceKPLocalRootDiagonalWord K hζ P u ∈ sourceKPLocalRootSubgroup K hζ P :=
  (sourceKPLocalRootSubgroup K hζ P).mul_mem
    (sourceKPLocalRootWeylWord_mem K hζ P u)
    ((sourceKPLocalRootSubgroup K hζ P).inv_mem (sourceKPLocalRootWeylWord_mem K hζ P 1))

theorem sourceKPLocalRootWeylWord_projection (u : Lˣ) :
    p₀ (sourceKPLocalRootWeylWord K hζ P u) =
      ProjGenLinGroup.mk (sourceGL2Upper (u : L)*sourceGL2Lower (-(u : L)⁻¹)*sourceGL2Upper (u : L)) := by
  simp only [sourceKPLocalRootWeylWord, map_mul]
  rfl

theorem sourceKPLocalRootDiagonalWord_projection (u : Lˣ) :
    p₀ (sourceKPLocalRootDiagonalWord K hζ P u) = ProjGenLinGroup.mk (sourceGL2Diagonal (u^2)) := by
  rw [sourceKPLocalRootDiagonalWord, map_mul, map_inv, sourceKPLocalRootWeylWord_projection K hζ P u,
    sourceKPLocalRootWeylWord_projection K hζ P 1, sourceKPLocalRootWeyl_matrix u,
    map_mul, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  simp only [Units.val_one, inv_one, mul_inv_cancel_right]

theorem sourceKPLocalRootDiagonalWord_eq_center_mul (u : Lˣ) :
    ∃ z : rootsOfUnity 3 L, sourceKPLocalRootDiagonalWord K hζ P u =
      z₀ z*l₀ (sourceGL2Diagonal (u^2)) := by
  let A := sourceKPLocalRootDiagonalWord K hζ P u
  let B := l₀ (sourceGL2Diagonal (u^2))
  have hk : A*B⁻¹ ∈ (p₀).ker := by
    change p₀ (A*B⁻¹) = 1
    rw [map_mul,map_inv,sourceKPLocalRootDiagonalWord_projection K hζ P]
    exact mul_inv_cancel _
  rw [← sourceFiniteKP2Projective_exact K hζ P] at hk
  obtain ⟨z,hz⟩ := hk
  refine ⟨z,?_⟩
  change A = z₀ z*B
  rw [hz, inv_mul_cancel_right]

end
end ArtinMatthews
