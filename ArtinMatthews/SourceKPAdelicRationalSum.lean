module

public import ArtinMatthews.SourceKPRationalBruhat
public import ArtinMatthews.SourceKPAdelicWeyl
public import ArtinMatthews.SourceKPAdelicExceptionalCharacter
public import ArtinMatthews.SourceKPOptionSum
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

/-! The Eisenstein sum over the actual rational upper-Borel quotient
inside the constructed cubic adelic cover. Summability and its transport
are stated explicitly. The open-cell formula uses the exact rational
splitting, including its finite adelic cocycle. -/

namespace ArtinMatthews
open Matrix NumberField
open scoped MatrixGroups NumberField BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "G" => SourceKPAdelicProjective K hζ
local notation "r" => sourceKPAdelicProjectiveRationalLift K hζ
local notation "B" => sourceKPRationalBorel K
local notation "X" => SourceKPRationalBorelCoset K

/-- The rational covariance used in the genuine Eisenstein summation. -/
def SourceKPRationalBorelFunction :=
  {f : G → ℂ // ∀ b ∈ B, ∀ g : G, f (r b * g) = f g}

def sourceKPRationalCosetTranslate (γ : PGL(2, K)) : X ≃ X where
  toFun := Quotient.map' (fun a => a * γ) (by
    intro a b h
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
      QuotientGroup.rightRel_apply.mp h)
  invFun := Quotient.map' (fun a => a * γ⁻¹) (by
    intro a b h
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [_root_.mul_inv_rev, mul_assoc, inv_inv, inv_mul_cancel_left] using
      QuotientGroup.rightRel_apply.mp h)
  left_inv q := by
    induction q using Quotient.inductionOn
    exact congrArg (sourceKPRationalBorelCosetMk K) (mul_inv_cancel_right _ _)
  right_inv q := by
    induction q using Quotient.inductionOn
    exact congrArg (sourceKPRationalBorelCosetMk K) (inv_mul_cancel_right _ _)

def sourceKPAdelicRationalSummand (f : SourceKPRationalBorelFunction K hζ) (g : G) : X → ℂ :=
  Quotient.lift (fun a => f.val (r a * g)) (by
    intro a b h
    have hb : b * a⁻¹ ∈ B := QuotientGroup.rightRel_apply.mp h
    have hf := f.property (b * a⁻¹) hb (r a * g)
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using hf.symm)

theorem sourceKPAdelicRationalSummand_mk (f : SourceKPRationalBorelFunction K hζ)
    (g : G) (a : PGL(2, K)) :
    sourceKPAdelicRationalSummand K hζ f g (sourceKPRationalBorelCosetMk K a) =
      f.val (r a * g) := rfl

def sourceKPAdelicRationalSum (f : SourceKPRationalBorelFunction K hζ) (g : G) : ℂ :=
  ∑' q : X, sourceKPAdelicRationalSummand K hζ f g q

theorem sourceKPAdelicRationalSummand_translate (f : SourceKPRationalBorelFunction K hζ)
    (γ : PGL(2, K)) (g : G) (q : X) :
    sourceKPAdelicRationalSummand K hζ f (r γ * g) q =
      sourceKPAdelicRationalSummand K hζ f g (sourceKPRationalCosetTranslate K γ q) := by
  induction q using Quotient.inductionOn
  change f.val (r _ * (r γ * g)) = f.val (r (_ * γ) * g)
  rw [map_mul, mul_assoc]

theorem sourceKPAdelicRationalSummand_summable_iff (f : SourceKPRationalBorelFunction K hζ)
    (γ : PGL(2, K)) (g : G) :
    Summable (sourceKPAdelicRationalSummand K hζ f (r γ * g)) ↔
      Summable (sourceKPAdelicRationalSummand K hζ f g) := by
  change Summable (fun q => sourceKPAdelicRationalSummand K hζ f (r γ * g) q) ↔ _
  simp_rw [sourceKPAdelicRationalSummand_translate]
  exact (sourceKPRationalCosetTranslate K γ).summable_iff

/-- Reindexing is on the actual rational Borel quotient. -/
theorem sourceKPAdelicRationalSum_automorphy (f : SourceKPRationalBorelFunction K hζ)
    (γ : PGL(2, K)) (g : G) :
    sourceKPAdelicRationalSum K hζ f (r γ * g) = sourceKPAdelicRationalSum K hζ f g := by
  unfold sourceKPAdelicRationalSum
  simp_rw [sourceKPAdelicRationalSummand_translate]
  exact (sourceKPRationalCosetTranslate K γ).tsum_eq _

theorem sourceKPAdelicRationalSum_hasSum_translate (f : SourceKPRationalBorelFunction K hζ)
    (γ : PGL(2, K)) (g : G) {c : ℂ}
    (h : HasSum (sourceKPAdelicRationalSummand K hζ f g) c) :
    HasSum (sourceKPAdelicRationalSummand K hζ f (r γ * g)) c := by
  change HasSum (fun q => sourceKPAdelicRationalSummand K hζ f (r γ * g) q) c
  simp_rw [sourceKPAdelicRationalSummand_translate]
  exact (sourceKPRationalCosetTranslate K γ).hasSum_iff.mpr h

theorem sourceKPAdelicRationalSum_weyl (f : SourceKPRationalBorelFunction K hζ) (g : G) :
    sourceKPAdelicRationalSum K hζ f (sourceKPAdelicProjectiveWeyl K hζ * g) =
      sourceKPAdelicRationalSum K hζ f g :=
  sourceKPAdelicRationalSum_automorphy K hζ f (ProjGenLinGroup.mk (sourceKPWeylMatrix K)) g

/-- The closed cell and the open rational cell, with the cocycle-correct
rational lifts retained on both cells. -/
theorem sourceKPAdelicRationalSum_bruhat (f : SourceKPRationalBorelFunction K hζ) (g : G)
    (hs : Summable (sourceKPAdelicRationalSummand K hζ f g)) :
    sourceKPAdelicRationalSum K hζ f g =
      f.val g + ∑' x : K, f.val
        (sourceKPAdelicProjectiveWeyl K hζ * r (sourcePGL2Upper x) * g) := by
  rw [sourceKPAdelicRationalSum, ← (sourceKPRationalBorelCosetEquiv K).tsum_eq]
  let u := fun t : Option K =>
    sourceKPAdelicRationalSummand K hζ f g (sourceKPRationalBorelCosetEquiv K t)
  have hu : Summable u := (sourceKPRationalBorelCosetEquiv K).summable_iff.mpr hs
  rw [sourceKPOptionSum u hu]
  change f.val (r (ProjGenLinGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 2) K)) * g) +
    (∑' x : K, f.val (r (ProjGenLinGroup.mk (sourceGL2Weyl * sourceGL2Upper x)) * g)) = _
  rw [map_one, map_one, one_mul]
  congr 1
  apply tsum_congr
  intro x
  rw [map_mul, map_mul]
  rw [sourceKPAdelicProjectiveWeyl, sourceKPWeylMatrix_field]

theorem sourceKPAdelicRationalSum_genuine (f : SourceKPRationalBorelFunction K hζ)
    (hf : ∀ (z : rootsOfUnity 3 K) (g : G),
      f.val (sourceKPAdelicProjectiveCenter K hζ z * g) =
        (sourceKPAdelicCentralComplex K hζ z : ℂ) * f.val g)
    (z : rootsOfUnity 3 K) (g : G) :
    sourceKPAdelicRationalSum K hζ f (sourceKPAdelicProjectiveCenter K hζ z * g) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) * sourceKPAdelicRationalSum K hζ f g := by
  unfold sourceKPAdelicRationalSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  induction q using Quotient.inductionOn with
  | _ a =>
    simp only [sourceKPAdelicRationalSummand, Quotient.lift_mk]
    rw [← mul_assoc, (sourceKPAdelicProjectiveCenter_commute K hζ z (r a)).eq.symm,
      mul_assoc, hf]

end
end ArtinMatthews
