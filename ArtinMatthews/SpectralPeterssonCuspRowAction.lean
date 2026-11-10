module

public import ArtinMatthews.SpectralPeterssonCuspRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Right translation of the actual correspondence acts bijectively
on its bottom rows, with the exact normalized real chart factor. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0PeterssonRightMatrix (N : ℕ) (b b' a : SL(2, ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) (M : gamma0CuspCorrespondence N b a) :
    gamma0CuspCorrespondence N b' a :=
  ⟨M.val*(b*γ.val*(b')⁻¹), by
    have h : a⁻¹*M.val*b ∈ CongruenceSubgroup.Gamma0 N := M.property
    change a⁻¹*(M.val*(b*γ.val*(b')⁻¹))*b' ∈ CongruenceSubgroup.Gamma0 N
    rw [show a⁻¹*(M.val*(b*γ.val*(b')⁻¹))*b' = (a⁻¹*M.val*b)*γ.val by group]
    exact (CongruenceSubgroup.Gamma0 N).mul_mem h γ.property⟩

theorem gamma0PeterssonRightMatrix_row (N : ℕ) (b b' a : SL(2, ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) (M : gamma0CuspCorrespondence N b a) :
    (fun i => (gamma0PeterssonRightMatrix N b b' a γ M).val 1 i) =
      (fun i => M.val 1 i) ᵥ* (b*γ.val*(b')⁻¹ : SL(2, ℤ)).val := rfl

def gamma0PeterssonSignedRowRight (N : ℕ) (b b' a : SL(2, ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) (p : Gamma0PeterssonSignedRow N b a) :
    Gamma0PeterssonSignedRow N b' a :=
  ⟨p.val ᵥ* (b*γ.val*(b')⁻¹ : SL(2, ℤ)).val, by
    obtain ⟨M,hM⟩ := p.property
    exact ⟨gamma0PeterssonRightMatrix N b b' a γ M,
      (gamma0PeterssonRightMatrix_row N b b' a γ M).trans (by rw [hM])⟩⟩

private theorem gamma0Petersson_vecMul_inv (p : Fin 2 → ℤ)
    (g h : SL(2, ℤ)) (he : g*h = 1) : (p ᵥ* g.val) ᵥ* h.val = p := by
  have hh : g.val*h.val = (1 : Matrix (Fin 2) (Fin 2) ℤ) :=
    congrArg (fun M : SL(2, ℤ) => M.val) he
  rw [vecMul_vecMul,hh,vecMul_one]

def gamma0PeterssonSignedRowRightEquiv (N : ℕ) (b b' a : SL(2, ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) :
    Gamma0PeterssonSignedRow N b a ≃ Gamma0PeterssonSignedRow N b' a where
  toFun := gamma0PeterssonSignedRowRight N b b' a γ
  invFun := gamma0PeterssonSignedRowRight N b' b a γ⁻¹
  left_inv p := by
    apply Subtype.ext
    change (p.val ᵥ* (b*γ.val*(b')⁻¹ : SL(2, ℤ)).val) ᵥ*
      (b'*(γ.val)⁻¹*b⁻¹ : SL(2, ℤ)).val = p.val
    exact gamma0Petersson_vecMul_inv p.val _ _ (by group)
  right_inv p := by
    apply Subtype.ext
    change (p.val ᵥ* (b'*(γ.val)⁻¹*b⁻¹ : SL(2, ℤ)).val) ᵥ*
      (b*γ.val*(b')⁻¹ : SL(2, ℤ)).val = p.val
    exact gamma0Petersson_vecMul_inv p.val _ _ (by group)

theorem gamma0Petersson_normalized_rightChange (N : ℕ) [NeZero N]
    (b b' a M g : SL(2, ℤ)) :
    gamma0TrueWidthMatrix N b' a (M*(b*g*(b')⁻¹)) =
      gamma0TrueWidthMatrix N b a M*
        ((gamma0TrueCuspScaling N b)⁻¹*atkinRealMap g*gamma0TrueCuspScaling N b') := by
  unfold gamma0TrueWidthMatrix gamma0TrueCuspScaling
  simp only [map_mul,map_inv]
  group

end ArtinMatthews
