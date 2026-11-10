module

public import ArtinMatthews.VaryingKummerAnalyticMixedClassCompletionFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Contractible
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The unit-conductor branch for the actual ideal-ray character. The
class character is constructed from its ideal values, and the completion
is identified with the genuine continued Dirichlet series. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Filter Set Topology
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

def conductorOneClassCharacter (hM : M = ⊤) : ClassGroup (𝓞 K) →* ℂ :=
  (ψ.conductorOneRay hM).classCharacter rfl

theorem conductorOneClassCharacter_ne_one (hM : M = ⊤) (hψ : ψ.IsNonprincipal) :
    ψ.conductorOneClassCharacter hM ≠ 1 :=
  (ψ.conductorOneRay hM).classCharacter_ne_one_of_nonprincipal rfl
    (ψ.conductorOneRay_isNonprincipal hM hψ)

theorem inverse_conductorOneClassCharacter (hM : M = ⊤) :
    ψ.inverse.conductorOneClassCharacter hM =
      inverseClassCharacter K (ψ.conductorOneClassCharacter hM) := by
  ext c
  rw [inverseClassCharacter_apply, map_inv]
  change ((ψ.idealHom _)⁻¹ : ℂˣ).val = (ψ.idealHom _ : ℂ)⁻¹
  simp only [Units.val_inv_eq_inv_val]

theorem conductorOneContinued_eq_class (hM : M = ⊤) (s : ℂ) :
    ψ.conductorOneContinued hM s =
      mixedIdealClassContinued K (ψ.conductorOneClassCharacter hM) s := by
  have hb : EvenRayCharacter.badEulerCorrection
      ((ψ.conductorOneRay hM).classUnitCharacter rfl) 1 s = 1 := by
    unfold EvenRayCharacter.badEulerCorrection EvenRayCharacter.badPrimes
    rw [Nat.primeFactors_one,
      show Finset.subtype Nat.Prime ∅ = ∅ from Finset.subtype_eq_empty.mpr (by simp)]
    exact Finset.prod_empty
  change mixedIdealClassContinued K (ψ.conductorOneClassCharacter hM) s *
    EvenRayCharacter.badEulerCorrection ((ψ.conductorOneRay hM).classUnitCharacter rfl) 1 s = _
  rw [hb, mul_one]

/-- Entire completed function, using the actual unramified ideal-class
character rather than a new character parameter. -/
def conductorOneCompleted (hM : M = ⊤) : ℂ → ℂ :=
  mixedCompletedIdealClass K (ψ.conductorOneClassCharacter hM)

theorem conductorOneCompleted_entire (hM : M = ⊤) :
    Differentiable ℂ (ψ.conductorOneCompleted hM) :=
  mixedCompletedIdealClass_entire K _

theorem conductorOneCompleted_functional_equation (hM : M = ⊤)
    (hψ : ψ.IsNonprincipal) (s : ℂ) :
    ψ.conductorOneCompleted hM s =
      mixedClassRootNumber K (ψ.conductorOneClassCharacter hM) *
        ψ.inverse.conductorOneCompleted hM (1-s) := by
  simpa only [conductorOneCompleted, inverse_conductorOneClassCharacter] using
    mixedCompletedIdealClass_functional_equation K (ψ.conductorOneClassCharacter hM)
      (ψ.conductorOneClassCharacter_ne_one hM hψ) s

theorem conductorOneCompleted_rootNumber_norm (hM : M = ⊤) :
    ‖mixedClassRootNumber K (ψ.conductorOneClassCharacter hM)‖ = 1 :=
  mixedClassRootNumber_norm K _

theorem primitiveContinued_eq_conductorOne (hMtop : M = ⊤) (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hψ : ψ.IsNonprincipal) :
    ψ.primitiveContinued hM hprim = ψ.conductorOneContinued hMtop := by
  apply ((ψ.primitiveContinued_entire hM hprim).differentiableOn.analyticOnNhd
    isOpen_univ).eq_of_eventuallyEq
    ((ψ.conductorOneContinued_entire hMtop).differentiableOn.analyticOnNhd isOpen_univ)
    (z₀ := (2:ℂ))
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show 1 < (2:ℂ).re by norm_num)] with s hs
  rw [ψ.primitiveContinued_eq_dirichlet hM hprim hψ hs,
    ψ.conductorOneContinued_eq_dirichlet hMtop hψ hs]

/-- A global identity binds the constructed entire completion to the
actual primitive continuation, including the zeros of inverse Gamma. -/
theorem primitiveContinued_eq_conductorOneCompletion (hMtop : M = ⊤) (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hψ : ψ.IsNonprincipal) (s : ℂ) :
    ψ.primitiveContinued hM hprim s = (mixedXiNormalization K : ℂ)⁻¹ *
      mixedInverseGammaFactor K s *
        mixedEntireIdealClassCompletion K (ψ.conductorOneClassCharacter hMtop) s := by
  rw [ψ.primitiveContinued_eq_conductorOne hMtop hM hprim hψ,
    ψ.conductorOneContinued_eq_class]
  rfl

/-- The constructed completion equals the conventional completed
primitive series throughout its convergent half-plane. -/
theorem conductorOneCompleted_eq_primitiveContinued (hMtop : M = ⊤) (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hψ : ψ.IsNonprincipal) {s : ℂ} (hs : 1 < s.re) :
    ψ.conductorOneCompleted hMtop s = (mixedDiscriminantScale K : ℂ)^s *
      (mixedXiNormalization K : ℂ) * mixedGammaFactor K s *
        ψ.primitiveContinued hM hprim s := by
  have hc := ψ.conductorOneClassCharacter_ne_one hMtop hψ
  have he : idealClassDirichlet K (ψ.conductorOneClassCharacter hMtop) s = ψ.dirichlet s := by
    rw [← mixedIdealClassContinued_eq K _ hc hs, ← ψ.conductorOneContinued_eq_class,
      ψ.conductorOneContinued_eq_dirichlet hMtop hψ hs]
  rw [conductorOneCompleted, mixedCompletedIdealClass_eq_dirichlet K _ hc hs, he,
    ψ.primitiveContinued_eq_dirichlet hM hprim hψ hs]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
