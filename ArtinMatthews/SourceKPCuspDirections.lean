module

public import ArtinMatthews.SourceKPCuspPrincipalQuotient
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

/-! Coordinate lines are the actual directions of the scaled Minkowski integral basis. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free Topology
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

lemma sourceKPCuspCoordinates_basis (i j : I) :
    sourceKPCuspCoordinates K d hd (sourceKPCuspLatticeBasis K d hd i) j =
      if i = j then 1 else 0 :=
  (sourceKPCuspLatticeBasis K d hd).equivFun_self i j

lemma sourceKPCuspTorusHom_coordinate_line (x : E) (i : I) (u : ℝ) :
    sourceKPCuspTorusHom K d hd
      (x + (u - sourceKPCuspCoordinates K d hd x i) • sourceKPCuspLatticeBasis K d hd i) =
    Function.update (sourceKPCuspTorusHom K d hd x) i (u : UnitAddCircle) := by
  ext j
  rw [sourceKPCuspTorusHom_apply]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (((sourceKPCuspCoordinates K d hd x) j +
    (u - sourceKPCuspCoordinates K d hd x i) *
      sourceKPCuspCoordinates K d hd (sourceKPCuspLatticeBasis K d hd i) j : ℝ) : UnitAddCircle) = _
  rw [sourceKPCuspCoordinates_basis]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Function.update_of_ne (Ne.symm hij), sourceKPCuspTorusHom_apply]

lemma sourceKPCuspPrincipalTorusHomeomorph_arch (x : E) :
    sourceKPCuspPrincipalTorusHomeomorph K d hd (sourceKPCuspArchQuotientMap K d x) =
      sourceKPCuspTorusHom K d hd x := by
  change sourceKPCuspTorusEquiv K d hd
    ((sourceKPCuspArchQuotientEquiv K d hd).symm (sourceKPCuspArchQuotientMap K d x)) = _
  rw [← sourceKPCuspArchQuotientEquiv_mk K d hd x, AddEquiv.symm_apply_apply,
    sourceKPCuspTorusEquiv_mk]

lemma sourceKPCuspPrincipalTorusHomeomorph_symm_arch (x : E) :
    (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm (sourceKPCuspTorusHom K d hd x) =
      sourceKPCuspArchQuotientMap K d x := by
  apply (sourceKPCuspPrincipalTorusHomeomorph K d hd).injective
  rw [ContinuousAddEquiv.apply_symm_apply, sourceKPCuspPrincipalTorusHomeomorph_arch]

lemma sourceKPCuspPrincipalTorusHomeomorph_line (x : E) (i : I) (u : ℝ) :
    (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm
      (Function.update (sourceKPCuspTorusHom K d hd x) i (u : UnitAddCircle)) =
    sourceKPCuspArchQuotientMap K d
      ((x - sourceKPCuspCoordinates K d hd x i • sourceKPCuspLatticeBasis K d hd i) +
        u • sourceKPCuspLatticeBasis K d hd i) := by
  rw [← sourceKPCuspTorusHom_coordinate_line K d hd x i u,
    sourceKPCuspPrincipalTorusHomeomorph_symm_arch]
  apply congrArg (sourceKPCuspArchQuotientMap K d)
  rw [sub_smul]
  abel

end
end ArtinMatthews
