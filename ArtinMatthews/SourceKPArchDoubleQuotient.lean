module

public import ArtinMatthews.SourceKPArchRightAction
public import ArtinMatthews.SourceKPArithmeticLocalQuotient
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

/-! The compact quotient of each actual automorphic component is its
literal arithmetic double quotient. -/
namespace ArtinMatthews
open NumberField Matrix Topology MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

abbrev SourceKPAutomorphicCompactLevel :=
  Quotient (MulAction.orbitRel (SourceKPArchCompactRightGroup K hζ) (SourceKPAutomorphicLevel K hζ))

def sourceKPAutomorphicCompactMk (x : SourceKPAutomorphicLevel K hζ) :
    SourceKPAutomorphicCompactLevel K hζ := Quotient.mk _ x

theorem sourceKPAutomorphicCompactMk_isOpenQuotientMap :
    IsOpenQuotientMap (sourceKPAutomorphicCompactMk K hζ) :=
  MulAction.isOpenQuotientMap_quotientMk

def sourceKPAutomorphicCompactFiniteOrbit :
    SourceKPAutomorphicCompactLevel K hζ → SourceKPFiniteOrbit K hζ :=
  Quotient.lift (sourceKPAutomorphicFiniteOrbit K hζ) (by
    intro x y hxy
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp hxy
    rw [← hk]
    exact sourceKPAutomorphicFiniteOrbit_archRight K hζ k.val y)

theorem sourceKPAutomorphicCompactFiniteOrbit_continuous :
    Continuous (sourceKPAutomorphicCompactFiniteOrbit K hζ) :=
  (sourceKPAutomorphicFiniteOrbit_continuous K hζ).quotient_lift _

abbrev SourceKPArchComponentCompactQuotient (b : SourceKPFiniteLevelFiber K hζ) :=
  SourceLeftThenRightQuotient (sourceKPArchComponentSubgroup K hζ b)
    (sourceKPArchBaseCompactSubgroup K hζ)

def sourceKPArchCompactComponentMap (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArchComponentCompactQuotient K hζ b → SourceKPAutomorphicCompactLevel K hζ :=
  sourceOrbitMap (Γ := SourceKPArchCompactRightGroup K hζ) (sourceKPArchComponentEmbedding K hζ b)
    (fun k x => sourceKPArchComponentEmbedding_archRight K hζ b k.val x)

theorem sourceKPArchCompactComponentMap_isOpenEmbedding (b : SourceKPFiniteLevelFiber K hζ) :
    IsOpenEmbedding (sourceKPArchCompactComponentMap K hζ b) :=
  sourceOrbitMap_isOpenEmbedding (Γ := SourceKPArchCompactRightGroup K hζ) (sourceKPArchComponentEmbedding K hζ b)
    (fun k x => sourceKPArchComponentEmbedding_archRight K hζ b k.val x)
    (sourceKPArchComponentEmbedding_isOpenEmbedding K hζ b)

@[simp] theorem sourceKPArchCompactComponentMap_mk (b : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchCompactComponentMap K hζ b
      (sourceLeftThenRightMk (sourceKPArchComponentSubgroup K hζ b)
        (sourceKPArchBaseCompactSubgroup K hζ) a) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentPoint K hζ b a) := rfl

theorem sourceKPArchCompactComponentMap_finiteOrbit (b : SourceKPFiniteLevelFiber K hζ)
    (x : SourceKPArchComponentCompactQuotient K hζ b) :
    sourceKPAutomorphicCompactFiniteOrbit K hζ (sourceKPArchCompactComponentMap K hζ b x) =
      sourceKPFiniteOrbitMk K hζ b := by
  induction x using Quotient.inductionOn with
  | _ x =>
    induction x using Quotient.inductionOn with
    | _ x => rfl

theorem sourceKPArchCompactComponentMap_range (b : SourceKPFiniteLevelFiber K hζ) :
    Set.range (sourceKPArchCompactComponentMap K hζ b) =
      (sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹' {sourceKPFiniteOrbitMk K hζ b} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact sourceKPArchCompactComponentMap_finiteOrbit K hζ b y
  · intro hx
    induction x using Quotient.inductionOn with
    | _ x =>
      have he : x ∈ Set.range (sourceKPArchComponentPoint K hζ b) := by
        rw [sourceKPArchComponent_range]
        exact hx
      obtain ⟨a,rfl⟩ := he
      exact ⟨sourceLeftThenRightMk (sourceKPArchComponentSubgroup K hζ b)
        (sourceKPArchBaseCompactSubgroup K hζ) a,rfl⟩

theorem sourceKPArchCompactComponentMap_range_clopen (b : SourceKPFiniteLevelFiber K hζ) :
    IsClopen (Set.range (sourceKPArchCompactComponentMap K hζ b)) := by
  rw [sourceKPArchCompactComponentMap_range]
  exact (isClopen_discrete _).preimage (sourceKPAutomorphicCompactFiniteOrbit_continuous K hζ)

abbrev SourceKPArchDoubleQuotient (b : SourceKPFiniteLevelFiber K hζ) :=
  Quotient (DoubleCoset.setoid
    (sourceKPArchComponentSubgroup K hζ b : Set (PGL(2, InfiniteAdeleRing K)))
    (sourceKPArchBaseCompactSubgroup K hζ : Set (PGL(2, InfiniteAdeleRing K))))

abbrev SourceKPArithmeticSymmetricQuotient (b : SourceKPFiniteLevelFiber K hζ) :=
  Quotient (MulAction.orbitRel (sourceKPArchComponentSubgroup K hζ b)
    (SourceKPArchSymmetricSpace K hζ))

def sourceKPArchDoubleLeftHomeomorph (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArchDoubleQuotient K hζ b ≃ₜ SourceKPArchComponentCompactQuotient K hζ b :=
  sourceDoubleLeftThenRightHomeomorph (sourceKPArchComponentSubgroup K hζ b)
    (sourceKPArchBaseCompactSubgroup K hζ)

def sourceKPArchDoubleSymmetricHomeomorph (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArchDoubleQuotient K hζ b ≃ₜ SourceKPArithmeticSymmetricQuotient K hζ b :=
  sourceDoubleRightThenLeftHomeomorph (sourceKPArchComponentSubgroup K hζ b)
    (sourceKPArchBaseCompactSubgroup K hζ)

def sourceKPArchDoubleComponentMap (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArchDoubleQuotient K hζ b → SourceKPAutomorphicCompactLevel K hζ :=
  sourceKPArchCompactComponentMap K hζ b ∘ sourceKPArchDoubleLeftHomeomorph K hζ b

theorem sourceKPArchDoubleComponentMap_isOpenEmbedding (b : SourceKPFiniteLevelFiber K hζ) :
    IsOpenEmbedding (sourceKPArchDoubleComponentMap K hζ b) :=
  (sourceKPArchCompactComponentMap_isOpenEmbedding K hζ b).comp
    (sourceKPArchDoubleLeftHomeomorph K hζ b).isOpenEmbedding

@[simp] theorem sourceKPArchDoubleComponentMap_mk (b : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchDoubleComponentMap K hζ b (Quotient.mk _ a) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentPoint K hζ b a) := rfl

theorem sourceKPArchDoubleComponentMap_range (b : SourceKPFiniteLevelFiber K hζ) :
    Set.range (sourceKPArchDoubleComponentMap K hζ b) =
      (sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹' {sourceKPFiniteOrbitMk K hζ b} := by
  rw [← sourceKPArchCompactComponentMap_range]
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨sourceKPArchDoubleLeftHomeomorph K hζ b x,rfl⟩
  · rintro ⟨x,rfl⟩
    obtain ⟨x,rfl⟩ := (sourceKPArchDoubleLeftHomeomorph K hζ b).surjective x
    exact ⟨x,rfl⟩


theorem sourceKPArchDoubleComponentMap_range_clopen (b : SourceKPFiniteLevelFiber K hζ) :
    IsClopen (Set.range (sourceKPArchDoubleComponentMap K hζ b)) := by
  rw [sourceKPArchDoubleComponentMap_range]
  exact (isClopen_discrete _).preimage (sourceKPAutomorphicCompactFiniteOrbit_continuous K hζ)

def sourceKPArchDoubleComponentHomeomorph (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArchDoubleQuotient K hζ b ≃ₜ
      (sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹' {sourceKPFiniteOrbitMk K hζ b} :=
  (sourceKPArchDoubleComponentMap_isOpenEmbedding K hζ b).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (sourceKPArchDoubleComponentMap_range K hζ b))


@[simp] theorem sourceKPArchDoubleComponentHomeomorph_val
    (b : SourceKPFiniteLevelFiber K hζ) (x : SourceKPArchDoubleQuotient K hζ b) :
    (sourceKPArchDoubleComponentHomeomorph K hζ b x : SourceKPAutomorphicCompactLevel K hζ) =
      sourceKPArchDoubleComponentMap K hζ b x := rfl

def sourceKPArithmeticSymmetricComponentHomeomorph (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArithmeticSymmetricQuotient K hζ b ≃ₜ
      (sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹' {sourceKPFiniteOrbitMk K hζ b} :=
  (sourceKPArchDoubleSymmetricHomeomorph K hζ b).symm.trans
    (sourceKPArchDoubleComponentHomeomorph K hζ b)


@[simp] theorem sourceKPArithmeticSymmetricComponentHomeomorph_mk
    (b : SourceKPFiniteLevelFiber K hζ) (a : PGL(2, InfiniteAdeleRing K)) :
    (sourceKPArithmeticSymmetricComponentHomeomorph K hζ b
      (Quotient.mk _ (QuotientGroup.mk a)) : SourceKPAutomorphicCompactLevel K hζ) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentPoint K hζ b a) := by
  change (sourceKPArchDoubleComponentHomeomorph K hζ b
    ((sourceKPArchDoubleSymmetricHomeomorph K hζ b).symm
      (sourceKPArchDoubleSymmetricHomeomorph K hζ b (Quotient.mk _ a))) :
        SourceKPAutomorphicCompactLevel K hζ) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

end
end ArtinMatthews
