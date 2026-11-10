module

public import ArtinMatthews.ArtinRayIdealResidueRealization
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Multiplication of actual ideal ray characters at the product modulus.
The residue character is realized from the proved principal congruence law;
the full ideal homomorphism is the literal product. -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Ideal (𝓞 K)}

theorem principalKernel (ψ : EvenIdealRayCharacter K M) :
    PrincipalIdealRay.KernelLaw ψ.idealHom M := by
  intro a ha hcong
  have hq : Ideal.Quotient.mk M a = 1 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hcong
    simpa only [map_sub, map_one, sub_eq_zero] using h
  have hc : IsCoprime (Ideal.span {a}) M :=
    (quotient_isUnit_iff_span_coprime M a).mp (hq ▸ isUnit_one)
  apply Units.ext
  change (ψ.idealHom (integralIdealFractionalUnit (Ideal.span {a}) _) : ℂ) = 1
  rw [ψ.principalLaw a ha hc, hq, map_one]

theorem productKernel (ψ : EvenIdealRayCharacter K M) (φ : EvenIdealRayCharacter K N) :
    PrincipalIdealRay.KernelLaw (ψ.idealHom * φ.idealHom) (M*N) := by
  intro a ha hcong
  change ψ.idealHom _ * φ.idealHom _ = 1
  rw [show ψ.idealHom _ = 1 from ψ.principalKernel a ha (Ideal.mul_le_left hcong),
    show φ.idealHom _ = 1 from φ.principalKernel a ha (Ideal.mul_le_right hcong),
    one_mul]

theorem productFiniteOrder (ψ : EvenIdealRayCharacter K M) (φ : EvenIdealRayCharacter K N) :
    ∃ e : ℕ, 0 < e ∧ ∀ I, (ψ.idealHom * φ.idealHom) I ^ e = 1 := by
  obtain ⟨e,he,hψ⟩ := ψ.finiteOrder
  obtain ⟨f,hf,hφ⟩ := φ.finiteOrder
  refine ⟨e*f,Nat.mul_pos he hf,fun I => ?_⟩
  have h₁ : ψ.idealHom I ^ (e*f) = 1 := by rw [pow_mul,hψ,one_pow]
  have h₂ : φ.idealHom I ^ (e*f) = 1 := by rw [Nat.mul_comm,pow_mul,hφ,one_pow]
  simp only [MonoidHom.mul_apply,mul_pow,h₁,h₂,one_mul]

def multiplyAtProduct (ψ : EvenIdealRayCharacter K M) (φ : EvenIdealRayCharacter K N)
    (hM : M ≠ ⊥) (hN : N ≠ ⊥) : EvenIdealRayCharacter K (M*N) :=
  PrincipalIdealRay.realize (ψ.idealHom * φ.idealHom) (M*N) (mul_ne_zero hM hN)
    (ψ.productKernel φ) (ψ.productFiniteOrder φ)

theorem multiplyAtProduct_idealHom (ψ : EvenIdealRayCharacter K M)
    (φ : EvenIdealRayCharacter K N) (hM : M ≠ ⊥) (hN : N ≠ ⊥)
    (I : FractionalIdealGroup K) :
    (ψ.multiplyAtProduct φ hM hN).idealHom I = ψ.idealHom I * φ.idealHom I := rfl

def twistInverseAtProduct (η : EvenIdealRayCharacter K M) (ψ : EvenIdealRayCharacter K N)
    (hM : M ≠ ⊥) (hN : N ≠ ⊥) : EvenIdealRayCharacter K (M*N) :=
  η.multiplyAtProduct ψ.inverse hM hN

theorem twistInverseAtProduct_idealHom (η : EvenIdealRayCharacter K M)
    (ψ : EvenIdealRayCharacter K N) (hM : M ≠ ⊥) (hN : N ≠ ⊥)
    (I : FractionalIdealGroup K) :
    (η.twistInverseAtProduct ψ hM hN).idealHom I = η.idealHom I * (ψ.idealHom I)⁻¹ := rfl

end
end ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
