module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Nat.Prime.Defs
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

/-! The original natural-number band and its prime subtype have the
same draws. The equivalence preserves each numerical prime exactly. -/
namespace ArtinMatthews
noncomputable section

def giantSignedTypedPrimeBandEmbedding (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ↥P ↪ Nat.Primes where
  toFun p := ⟨p.val,hP p.val p.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun p : Nat.Primes => p.val) h)

def giantSignedTypedPrimeBand (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : Finset Nat.Primes :=
  P.attach.map (giantSignedTypedPrimeBandEmbedding P hP)

def giantSignedTypedPrimeBandEquiv (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ↥P ≃ ↥(giantSignedTypedPrimeBand P hP) :=
  Equiv.ofBijective (fun p => ⟨giantSignedTypedPrimeBandEmbedding P hP p, by
    change _ ∈ P.attach.map (giantSignedTypedPrimeBandEmbedding P hP)
    exact Finset.mem_map.mpr ⟨p,Finset.mem_attach _ _,rfl⟩⟩) (by
      constructor
      · intro p q h
        exact Subtype.ext (congrArg (fun a : ↥(giantSignedTypedPrimeBand P hP) => a.val.val) h)
      · intro p
        have hp := p.property
        change p.val ∈ P.attach.map (giantSignedTypedPrimeBandEmbedding P hP) at hp
        obtain ⟨q,_,hq⟩ := Finset.mem_map.mp hp
        exact ⟨q,Subtype.ext hq⟩)

theorem giantSignedTypedPrimeBandEquiv_value (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (p : P) :
    (giantSignedTypedPrimeBandEquiv P hP p).val = ⟨p.val,hP p.val p.property⟩ :=
  rfl

end
end ArtinMatthews
