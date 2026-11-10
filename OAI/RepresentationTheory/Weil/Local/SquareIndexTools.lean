module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup
public import Mathlib.GroupTheory.Index
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
public import Mathlib.Tactic.Basify
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
public import OAI.RepresentationTheory.Weil.Local.CompactGroupIndex
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! # Square Index Tools -/

namespace OAI.RepresentationTheory.Weil.Local.SquareIndexTools.Construction

noncomputable section

/-! Power-kernel and index comparison tools for the LocalWeil quadratic norm computation. -/

variable {G : Type*} [CommGroup G]

theorem square_map_subgroupOf (H : Subgroup G) :
    (H.map (powMonoidHom 2 : G →* G)).subgroupOf H = QuadraticNormSubgroup.Construction.squareUnitsSubgroup H := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact he
  · rintro ⟨y, he⟩
    exact ⟨y.val, y.property, congrArg Subtype.val he⟩

theorem square_index_eq_kernel_mul_local_index
    (H : Subgroup G) (hH : H.index ≠ 0)
    (hker : ∀ x : G, x ∈ H → x ^ 2 = 1 → x = 1) :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup G).index =
      Nat.card (powMonoidHom 2 : G →* G).ker * (QuadraticNormSubgroup.Construction.squareUnitsSubgroup H).index := by
  have hh := CompactGroupIndex.Construction.square_index_of_finite_index_subgroup H hH hker
  change (QuadraticNormSubgroup.Construction.squareUnitsSubgroup G).index =
    Nat.card (powMonoidHom 2 : G →* G).ker *
      ((H.map (powMonoidHom 2 : G →* G)).subgroupOf H).index at hh
  rwa [square_map_subgroupOf] at hh

theorem square_kernel_card_two (ε : G) (hε : ε ≠ 1)
    (h : ∀ x : G, x ^ 2 = 1 ↔ x = 1 ∨ x = ε) :
    Nat.card (powMonoidHom 2 : G →* G).ker = 2 := by
  let z : (powMonoidHom 2 : G →* G).ker := ⟨ε, (h ε).mpr (Or.inr rfl)⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨1, z, ?_, ?_⟩
  · intro he
    exact hε (congrArg Subtype.val he).symm
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hx : x.val ^ 2 = 1 := x.property
    rcases (h x.val).mp hx with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)

theorem square_index_eq_of_local_indices
    {G₁ G₂ : Type*} [CommGroup G₁] [CommGroup G₂]
    (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) (hH₁ : H₁.index ≠ 0) (hH₂ : H₂.index ≠ 0)
    (hk₁ : ∀ x : G₁, x ∈ H₁ → x ^ 2 = 1 → x = 1)
    (hk₂ : ∀ x : G₂, x ∈ H₂ → x ^ 2 = 1 → x = 1)
    (hc : Nat.card (powMonoidHom 2 : G₁ →* G₁).ker = Nat.card (powMonoidHom 2 : G₂ →* G₂).ker)
    (hi : (QuadraticNormSubgroup.Construction.squareUnitsSubgroup H₁).index = (QuadraticNormSubgroup.Construction.squareUnitsSubgroup H₂).index) :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup G₁).index = (QuadraticNormSubgroup.Construction.squareUnitsSubgroup G₂).index := by
  rw [square_index_eq_kernel_mul_local_index H₁ hH₁ hk₁,
    square_index_eq_kernel_mul_local_index H₂ hH₂ hk₂, hc, hi]

theorem square_index_mulEquiv {G₁ G₂ : Type*} [CommGroup G₁] [CommGroup G₂]
    (e : G₁ ≃* G₂) : (QuadraticNormSubgroup.Construction.squareUnitsSubgroup G₁).index = (QuadraticNormSubgroup.Construction.squareUnitsSubgroup G₂).index := by
  have hm : (QuadraticNormSubgroup.Construction.squareUnitsSubgroup G₁).map e.toMonoidHom = QuadraticNormSubgroup.Construction.squareUnitsSubgroup G₂ := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨e z, (map_pow e z 2).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.symm z ^ 2, ⟨e.symm z, rfl⟩, by simp⟩
  rw [← hm]
  exact (Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective _).symm

end

end OAI.RepresentationTheory.Weil.Local.SquareIndexTools.Construction
