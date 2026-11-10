module

public import ArtinMatthews.VaryingKummerAnalyticRayCharacter
public import ArtinMatthews.VaryingKummerAnalyticMixedLattice
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

/-! Actual integral ideal coordinates inside the arbitrary-signature
canonical fractional-ideal lattice. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)

def integralIdealToFractional : I ≃ₗ[ℤ] (integralIdealFractionalUnit I hI).val :=
  LinearEquiv.ofBijective
    { toFun := fun a => ⟨(a.val : K),FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ a.property⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp } ⟨by
        intro a b h
        apply Subtype.ext
        apply NumberField.RingOfIntegers.coe_injective
        exact congrArg (fun c : (integralIdealFractionalUnit I hI).val => c.val) h,
      by
        intro a
        obtain ⟨b,hb,hba⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property
        exact ⟨⟨b,hb⟩,Subtype.ext hba⟩⟩

@[simp] theorem integralIdealToFractional_coe (a : I) :
    ((integralIdealToFractional K I hI a).val : K) = (a.val : K) := rfl

def mixedIntegralIdealBasis : Basis (MixedIdealIndex K (integralIdealFractionalUnit I hI)) ℤ I :=
  (fractionalIdealBasis K (integralIdealFractionalUnit I hI).val).map
    (integralIdealToFractional K I hI).symm

def mixedIntegralRingIndexEquiv :
    MixedIdealIndex K (integralIdealFractionalUnit I hI) ≃ Free.ChooseBasisIndex ℤ (𝓞 K) :=
  Fintype.equivOfCardEq ((mixedIdealIndex_card K _).trans (Module.finrank_eq_card_basis
    (NumberField.integralBasis K)))

def mixedIntegralRingBasis :
    Basis (MixedIdealIndex K (integralIdealFractionalUnit I hI)) ℤ (𝓞 K) :=
  (Module.Free.chooseBasis ℤ (𝓞 K)).reindex (mixedIntegralRingIndexEquiv K I hI).symm

end
end ArtinMatthews.VaryingKummerAnalytic
