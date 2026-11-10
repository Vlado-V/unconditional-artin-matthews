module

public import ArtinMatthews.SourceKPArchDoubleQuotient
public import ArtinMatthews.SourceKPArchUpperAction
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

/-! The arithmetic quotient in literal product upper-half-space coordinates,
with its map to the actual compact automorphic quotient. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPArithmeticUpperMulAction (b : SourceKPFiniteLevelFiber K hζ) :
    MulAction (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K) := by
  letI := sourceKPArchUpperMulAction K hζ
  exact MulAction.compHom _ (sourceKPArchComponentSubgroup K hζ b).subtype

@[simp] theorem sourceKPArithmeticUpper_smul (b : SourceKPFiniteLevelFiber K hζ)
    (γ : sourceKPArchComponentSubgroup K hζ b) (p : SourceKPArchUpperHalfSpace K) :
    γ • p = sourceKPArchUpperAction K hζ γ.val p := rfl

instance sourceKPArithmeticUpper_continuousConst (b : SourceKPFiniteLevelFiber K hζ) :
    ContinuousConstSMul (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K) :=
  ⟨fun γ => sourceKPArchUpperAction_continuous K hζ γ.val⟩

theorem sourceKPArithmeticSymmetricToUpper_equivariant
    (b : SourceKPFiniteLevelFiber K hζ) (γ : sourceKPArchComponentSubgroup K hζ b)
    (p : SourceKPArchSymmetricSpace K hζ) :
    sourceKPArchSymmetricHomeomorph K hζ (γ • p) =
      γ • sourceKPArchSymmetricHomeomorph K hζ p :=
  sourceKPArchSymmetricHomeomorph_smul K hζ γ.val p

abbrev SourceKPArithmeticUpperQuotient (b : SourceKPFiniteLevelFiber K hζ) :=
  Quotient (MulAction.orbitRel (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K))

def sourceKPArithmeticUpperQuotientHomeomorph (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArithmeticSymmetricQuotient K hζ b ≃ₜ SourceKPArithmeticUpperQuotient K hζ b :=
  Homeomorph.Quotient.congr (sourceKPArchSymmetricHomeomorph K hζ) (by
    intro x y
    constructor
    · intro hxy
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨γ,(sourceKPArithmeticSymmetricToUpper_equivariant K hζ b γ y).symm.trans
        (congrArg (sourceKPArchSymmetricHomeomorph K hζ) hγ)⟩
    · intro hxy
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨γ,(sourceKPArchSymmetricHomeomorph K hζ).injective ?_⟩
      exact (sourceKPArithmeticSymmetricToUpper_equivariant K hζ b γ y).trans hγ)

@[simp] theorem sourceKPArithmeticUpperQuotientHomeomorph_mk
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchSymmetricSpace K hζ) :
    sourceKPArithmeticUpperQuotientHomeomorph K hζ b (Quotient.mk _ p) =
      Quotient.mk _ (sourceKPArchSymmetricHomeomorph K hζ p) := rfl

def sourceKPArithmeticUpperComponentHomeomorph (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArithmeticUpperQuotient K hζ b ≃ₜ
      (sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹' {sourceKPFiniteOrbitMk K hζ b} :=
  (sourceKPArithmeticUpperQuotientHomeomorph K hζ b).symm.trans
    (sourceKPArithmeticSymmetricComponentHomeomorph K hζ b)

@[simp] theorem sourceKPArithmeticUpperComponentHomeomorph_mk
    (b : SourceKPFiniteLevelFiber K hζ) (a : PGL(2, InfiniteAdeleRing K)) :
    (sourceKPArithmeticUpperComponentHomeomorph K hζ b
      (Quotient.mk _ (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a))) :
        SourceKPAutomorphicCompactLevel K hζ) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentPoint K hζ b a) := by
  change (sourceKPArithmeticSymmetricComponentHomeomorph K hζ b
    ((sourceKPArithmeticUpperQuotientHomeomorph K hζ b).symm
      (sourceKPArithmeticUpperQuotientHomeomorph K hζ b
        (Quotient.mk _ (QuotientGroup.mk a)))) : SourceKPAutomorphicCompactLevel K hζ) = _
  rw [Homeomorph.symm_apply_apply]
  exact sourceKPArithmeticSymmetricComponentHomeomorph_mk K hζ b a

instance sourceKPArithmeticUpper_properlyDiscontinuous (b : SourceKPFiniteLevelFiber K hζ) :
    ProperlyDiscontinuousSMul (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K) := by
  constructor
  intro U V hU hV
  have hU' := (sourceKPArchSymmetricHomeomorph K hζ).isCompact_preimage.mpr hU
  have hV' := (sourceKPArchSymmetricHomeomorph K hζ).isCompact_preimage.mpr hV
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := sourceKPArchComponentSubgroup K hζ b) hU' hV'
  apply hf.subset
  rintro γ ⟨_,⟨y,hy,rfl⟩,hγy⟩
  refine ⟨γ • (sourceKPArchSymmetricHomeomorph K hζ).symm y,⟨_,?_,rfl⟩,?_⟩
  · change sourceKPArchSymmetricHomeomorph K hζ
      ((sourceKPArchSymmetricHomeomorph K hζ).symm y) ∈ U
    simpa only [Homeomorph.apply_symm_apply] using hy
  · change sourceKPArchSymmetricHomeomorph K hζ
      (γ • (sourceKPArchSymmetricHomeomorph K hζ).symm y) ∈ V
    rw [sourceKPArithmeticSymmetricToUpper_equivariant, Homeomorph.apply_symm_apply]
    exact hγy

theorem sourceKPArithmeticUpper_finite_stabilizer (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p :
      Set (sourceKPArchComponentSubgroup K hζ b)).Finite :=
  ProperlyDiscontinuousSMul.finite_stabilizer p

theorem sourceKPArithmeticUpper_disjoint_neighborhood (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    ∃ U ∈ 𝓝 p, ∀ γ : sourceKPArchComponentSubgroup K hζ b,
      γ • p ≠ p → Disjoint ((γ • ·) '' U) U := by
  let : LocallyCompactSpace (SourceKPArchUpperHalfSpace K) :=
    (sourceKPArchSymmetricHomeomorph K hζ).locallyCompactSpace_iff.mp inferInstance
  let : T2Space (SourceKPArchUpperHalfSpace K) :=
    T2Space.of_injective_continuous (sourceKPArchSymmetricHomeomorph K hζ).symm.injective
      (sourceKPArchSymmetricHomeomorph K hζ).symm.continuous
  exact ProperlyDiscontinuousSMul.exists_nhds_disjoint_image
    (sourceKPArchComponentSubgroup K hζ b) p

end
end ArtinMatthews
