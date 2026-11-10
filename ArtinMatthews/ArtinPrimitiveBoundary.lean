module

public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.ArtinAbelianZeroDescent
public import ArtinMatthews.VaryingKummerAnalyticRayIdealConjugation
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveContinuationTransfer
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveNonprincipal
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

/-! Boundary nonvanishing for the genuine primitive descendants of an
actual abelian Frobenius character family. The input is the proved Artin
factorization at the nonzero Dedekind residues, not a nonvanishing assertion
for arbitrary ideal characters. -/
namespace ArtinMatthews.AbelianLocal
open ArtinMatthews.VaryingKummerAnalytic NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical ComplexConjugate
noncomputable section
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]
variable {N : ℕ} [NeZero N]
variable (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N)
variable (hψ : ∀ χ, (ψ χ).idealHom = GaloisIdealCharacter.idealHom F E χ)
variable (hD : (NumberField.discr E).natAbs ∣ N)
variable (hnp : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
variable (χ : Gal(E/F) →* ℂˣ) (hχ : χ ≠ 1)
variable (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
variable (hMf : rationalModulusIdeal (𝓞 F) N ≤ f) (Ψ : EvenIdealRayCharacter F f)
variable (hprim : IsPrimitiveOnIdeals Ψ.residue)
variable (hagree : ∀ I : primeToModulusIdeals (rationalIdealRayModulus F N),
  Ψ.idealHom (I:FractionalIdealGroup F) = (ψ χ).idealHom (I:FractionalIdealGroup F))
include hψ hD hnp hχ hMf hagree

theorem artinRay_primitiveContinued_one_ne_zero :
    Ψ.primitiveContinued hf hprim 1 ≠ 0 := by
  intro hzero
  apply artinRay_nonprincipalContinued_one_ne_zero F E ψ hψ hD hnp χ hχ
  exact ((ψ χ).nonprincipalContinued_zero_iff_primitive f hf hMf Ψ hprim hagree
    (hnp χ hχ) (s := 1) (by norm_num)).mpr hzero

theorem artinRay_inverse_primitiveContinued_one_ne_zero :
    Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  have he := Ψ.primitiveContinued_inverse_conj hf hprim hΨ (1:ℂ)
  rw [map_one] at he
  rw [he]
  exact fun hz => artinRay_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ
    f hf hMf Ψ hprim hagree ((map_eq_zero_iff _ (starRingEnd ℂ).injective).mp hz)

omit hMf hagree in
/-- The actual primitive presentation exists, retains all prime-to Frobenius
ideal values and the conductor norm bound, and is nonzero at one along with
its genuine inverse. -/
theorem artinRay_exists_primitive_boundary_nonzero :
    ∃ (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 F) N ≤ f) (Ψ : EvenIdealRayCharacter F f)
      (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧ f.absNorm ≤ (rationalModulusIdeal (𝓞 F) N).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus F N),
        Ψ.idealHom (I:FractionalIdealGroup F) = (ψ χ).idealHom (I:FractionalIdealGroup F)) ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
      Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,_hmask,hagree⟩ :=
    (ψ χ).exists_primitive_nonprincipal_idealCharacter (hnp χ hχ)
  exact ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,
    artinRay_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree,
    artinRay_inverse_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree⟩

end
end ArtinMatthews.AbelianLocal
