module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.Henselian
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

/-! The actual Minkowski lattice obtained by scaling the integral basis by a nonzero integer. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free Topology
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0)

local notation "E" => mixedEmbedding.mixedSpace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

def sourceKPCuspScaleUnit : Eˣ :=
  Units.map (mixedEmbedding K).toMonoidHom (Units.mk0 (d : K) (by exact_mod_cast hd))

def sourceKPCuspScale : E ≃ₗ[ℝ] E :=
  (sourceKPCuspScaleUnit K d hd).mulLeftLinearEquiv ℝ E

omit [NumberField K] in
lemma sourceKPCuspScale_apply (x : E) :
    sourceKPCuspScale K d hd x = mixedEmbedding K (d : K) * x := rfl

def sourceKPCuspLatticeBasis : Basis I ℝ E :=
  (mixedEmbedding.latticeBasis K).map (sourceKPCuspScale K d hd)

def sourceKPCuspLattice : Submodule ℤ E :=
  Submodule.span ℤ (Set.range (sourceKPCuspLatticeBasis K d hd))

lemma sourceKPCuspLattice_map :
    sourceKPCuspLattice K d hd = (mixedEmbedding.integerLattice K).map
      ((sourceKPCuspScale K d hd).toLinearMap.restrictScalars ℤ) := by
  unfold sourceKPCuspLattice sourceKPCuspLatticeBasis
  rw [Basis.coe_map, Set.range_comp]
  change Submodule.span ℤ
      (((sourceKPCuspScale K d hd).toLinearMap.restrictScalars ℤ) '' Set.range (mixedEmbedding.latticeBasis K)) = _
  rw [← Submodule.map_span, mixedEmbedding.span_latticeBasis]

lemma sourceKPCuspLattice_mem (x : E) :
    x ∈ sourceKPCuspLattice K d hd ↔
      ∃ r : 𝓞 K, mixedEmbedding K ((d * r : 𝓞 K) : K) = x := by
  rw [sourceKPCuspLattice_map, Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨r, hr⟩, hy⟩
    refine ⟨r, ?_⟩
    rw [← hy, ← hr]
    change mixedEmbedding K ((d * r : 𝓞 K) : K) = mixedEmbedding K (d : K) * mixedEmbedding K (r : K)
    rw [← map_mul]
    rfl
  · rintro ⟨r, hr⟩
    refine ⟨mixedEmbedding K (r : K), ⟨r, rfl⟩, ?_⟩
    change mixedEmbedding K (d : K) * mixedEmbedding K (r : K) = x
    rw [← map_mul]
    exact hr

lemma sourceKPCuspLatticeBasis_apply (i : I) :
    sourceKPCuspLatticeBasis K d hd i = mixedEmbedding K ((d : K) * integralBasis K i) := by
  rw [sourceKPCuspLatticeBasis, Basis.map_apply, sourceKPCuspScale_apply,
    mixedEmbedding.latticeBasis_apply, ← map_mul]

instance sourceKPCuspLattice_discrete : DiscreteTopology (sourceKPCuspLattice K d hd) := by
  let e := (sourceKPCuspScale K d hd).toContinuousLinearEquiv
  have hmem (x : sourceKPCuspLattice K d hd) : e.symm (x : E) ∈ mixedEmbedding.integerLattice K := by
    have hx : (x : E) ∈ (mixedEmbedding.integerLattice K).map
        ((sourceKPCuspScale K d hd).toLinearMap.restrictScalars ℤ) := by
      rw [← sourceKPCuspLattice_map]
      exact x.property
    obtain ⟨y, hy, he⟩ := hx
    change e y = (x : E) at he
    rw [← he, e.symm_apply_apply]
    exact hy
  let f : sourceKPCuspLattice K d hd → mixedEmbedding.integerLattice K :=
    fun x => ⟨e.symm x.val, hmem x⟩
  have hf : Continuous f := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  exact DiscreteTopology.of_continuous_injective hf (fun x y h =>
    Subtype.ext (e.symm.injective (congrArg Subtype.val h)))

def sourceKPCuspCoordinates : E ≃L[ℝ] (I → ℝ) :=
  (sourceKPCuspLatticeBasis K d hd).equivFunL

end
end ArtinMatthews
