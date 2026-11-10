module

public import ArtinMatthews.SourceAlgebraicInduction
public import ArtinMatthews.SourceKPLocalCompactGroup
public import ArtinMatthews.SourceKPLocalCompactCosets
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

/-! Compact restriction of the actual algebraic local principal series.
The compact coset space is finite and the restriction is injective by
the genuine covering Iwasawa decomposition. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
    {V : Type*} [AddCommGroup V] [Module ℂ V]

local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P
local notation "C" => sourceKPLocalCompactCover K hζ P
local notation "J" => sourceKPLocalCompactDeep K hζ P

def sourceKPLocalCompactFixedSpace (ρ : Representation ℂ B V) :
    Submodule ℂ (sourceAlgebraicInducedSpace _ ρ) where
  carrier := {f | ∀ (g : G) (j : J), f.val (g*j.val.val) = f.val g}
  zero_mem' _ _ := rfl
  add_mem' := by
    intro f f' hf hf' g j
    change f.val (g*j.val.val) + f'.val (g*j.val.val) = f.val g + f'.val g
    rw [hf g j, hf' g j]
  smul_mem' := by
    intro a f hf g j
    change a • f.val (g*j.val.val) = a • f.val g
    rw [hf g j]

theorem sourceKPLocalCompactFixedSpace_right (ρ : Representation ℂ B V)
    (f : sourceKPLocalCompactFixedSpace K hζ P ρ) (g : G) (j : J) :
    f.val.val (g*j.val.val) = f.val.val g := f.property g j

def sourceKPLocalCompactRestriction (ρ : Representation ℂ B V) :
    sourceKPLocalCompactFixedSpace K hζ P ρ →ₗ[ℂ] ((C ⧸ J) → V) where
  toFun f := Quotient.lift (fun k : C => f.val.val k.val) (by
    intro a b hab
    let j : J := ⟨a⁻¹*b, QuotientGroup.leftRel_apply.mp hab⟩
    have he : a.val*j.val.val = b.val := congrArg Subtype.val (mul_inv_cancel_left a b)
    rw [← he, sourceKPLocalCompactFixedSpace_right K hζ P ρ f])
  map_add' f g := by
    funext q
    refine QuotientGroup.induction_on q ?_
    intro k
    rfl
  map_smul' a f := by
    funext q
    refine QuotientGroup.induction_on q ?_
    intro k
    rfl

theorem sourceKPLocalCompactRestriction_apply (ρ : Representation ℂ B V)
    (f : sourceKPLocalCompactFixedSpace K hζ P ρ) (k : C) :
    sourceKPLocalCompactRestriction K hζ P ρ f (QuotientGroup.mk k) = f.val.val k.val := rfl

theorem sourceKPLocalCompactRestriction_injective (ρ : Representation ℂ B V) :
    Function.Injective (sourceKPLocalCompactRestriction K hζ P ρ) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨b,k,hx⟩ := sourceKPLocalCompactCover_Iwasawa K hζ P x
  rw [hx, sourceAlgebraicInducedSpace_covariant _ ρ f.val b,
    sourceAlgebraicInducedSpace_covariant _ ρ g.val b]
  exact congrArg (ρ b) (congrFun h (QuotientGroup.mk k))

theorem sourceKPLocalCompactRestriction_covariant (ρ : Representation ℂ B V)
    (f : sourceKPLocalCompactFixedSpace K hζ P ρ) (b : B) (hb : b.val ∈ C) (k : C) :
    sourceKPLocalCompactRestriction K hζ P ρ f (QuotientGroup.mk ((⟨b.val,hb⟩ : C)*k)) =
      ρ b (sourceKPLocalCompactRestriction K hζ P ρ f (QuotientGroup.mk k)) :=
  sourceAlgebraicInducedSpace_covariant _ ρ f.val b k.val

theorem sourceKPLocalCompactFixedSpace_finiteDimensional [FiniteDimensional ℂ V]
    (ρ : Representation ℂ B V) :
    FiniteDimensional ℂ (sourceKPLocalCompactFixedSpace K hζ P ρ) := by
  let : Finite (C ⧸ J) := sourceKPLocalCompactCosets_finite K hζ P
  exact FiniteDimensional.of_injective (sourceKPLocalCompactRestriction K hζ P ρ)
    (sourceKPLocalCompactRestriction_injective K hζ P ρ)

theorem sourceKPLocalCompactFixedSpace_finrank_le [FiniteDimensional ℂ V]
    (ρ : Representation ℂ B V) :
    Module.finrank ℂ (sourceKPLocalCompactFixedSpace K hζ P ρ) ≤
      Nat.card (C ⧸ J) * Module.finrank ℂ V := by
  let : Finite (C ⧸ J) := sourceKPLocalCompactCosets_finite K hζ P
  let : Fintype (C ⧸ J) := Fintype.ofFinite _
  calc
    _ ≤ Module.finrank ℂ ((C ⧸ J) → V) :=
      LinearMap.finrank_le_finrank_of_injective (sourceKPLocalCompactRestriction_injective K hζ P ρ)
    _ = _ := by rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card] <;> rfl

end
end ArtinMatthews
