module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnifiedPair
public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.KummerTowerDiscriminantModulus
public import ArtinMatthews.ArtinPrimitiveCompletedUnifiedBoundary
public import ArtinMatthews.ArtinRaySmallModulus
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

/-! The boundary values of the actual inverse-character product for an
abelian Frobenius family. The constructor retains its conductor and every
prime-to-modulus Frobenius ideal value. -/
namespace ArtinMatthews.AbelianLocal
open ArtinMatthews.VaryingKummerAnalytic NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical
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
include hψ hD hnp hχ hMf hprim hagree

theorem artinRay_primitiveCompletedUnifiedPair_zero_ne_zero :
    Ψ.primitiveCompletedUnifiedPair hf 0 ≠ 0 :=
  mul_ne_zero
    (artinRay_primitiveCompletedUnified_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree)
    (artinRay_inverse_primitiveCompletedUnified_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree)

theorem artinRay_primitiveCompletedUnifiedPair_one_ne_zero :
    Ψ.primitiveCompletedUnifiedPair hf 1 ≠ 0 :=
  mul_ne_zero
    (artinRay_primitiveCompletedUnified_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree)
    (artinRay_inverse_primitiveCompletedUnified_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree)

omit hMf hprim hagree in
theorem artinRay_exists_primitiveCompletedUnifiedPair_boundary_nonzero :
    ∃ (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 F) N ≤ f) (Ψ : EvenIdealRayCharacter F f)
      (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧ f.absNorm ≤ (rationalModulusIdeal (𝓞 F) N).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus F N),
        Ψ.idealHom (I:FractionalIdealGroup F) = (ψ χ).idealHom (I:FractionalIdealGroup F)) ∧
      Ψ.primitiveCompletedUnifiedPair hf 0 ≠ 0 ∧ Ψ.primitiveCompletedUnifiedPair hf 1 ≠ 0 ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
      Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,h0,h1,hi0,hi1,hL,hLi⟩ :=
    artinRay_exists_primitiveCompletedUnified_boundary_nonzero F E ψ hψ hD hnp χ hχ
  exact ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,mul_ne_zero h0 hi0,mul_ne_zero h1 hi1,hL,hLi⟩

end
end ArtinMatthews.AbelianLocal

namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical
noncomputable section
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]
local instance unifiedPairBoundaryModulusNeZero : NeZero (discriminantDegreeModulus K L) :=
  ⟨(discriminantDegreeModulus_pos K L).ne'⟩

theorem discriminantDegree_exists_primitiveCompletedUnifiedPair_boundary_nonzero
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L) ≤ f)
      (Ψ : EvenIdealRayCharacter K f) (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
        Ψ.idealHom (I:FractionalIdealGroup K) =
          GaloisIdealCharacter.idealHom K L χ (I:FractionalIdealGroup K)) ∧
      Ψ.primitiveCompletedUnifiedPair hf 0 ≠ 0 ∧ Ψ.primitiveCompletedUnifiedPair hf 1 ≠ 0 ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
      Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  simpa only [discriminantDegreeRayCharacter_idealHom] using
    AbelianLocal.artinRay_exists_primitiveCompletedUnifiedPair_boundary_nonzero K L
      (fun χ => discriminantDegreeRayCharacter (K := K) (L := L) χ)
      (fun _ => rfl) (discr_dvd_discriminantDegreeModulus K L)
      (fun χ hχ => discriminantDegreeRayCharacter_isNonprincipal χ hχ) χ hχ

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
