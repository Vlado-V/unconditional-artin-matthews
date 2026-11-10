module

public import ArtinMatthews.VaryingKummerAnalyticHeckeConductorSieveClasses
public import ArtinMatthews.VaryingKummerAnalyticRayIdealCharacterMultiplicity
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

/-! The conductor sieve for actual distinct Hecke coefficient functions.
The finite class-group multiplicity is proved at the genuine ideal modulus.
Every raw finite family is reduced to its exact coefficient image by a
constructed representative subfamily; no residue-injectivity premise remains. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem actualHecke_conductor_sieve_of_distinct_coefficients
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (hsep : ∀ M ∈ T, Set.InjOn (fun ψ : EvenIdealRayCharacter K M.val => ψ.coefficient) (A M))
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    (∑ M ∈ T, ∑ ψ ∈ A M, ‖ψ.classGroupHeckePolynomial B v‖^2) ≤
      ((NumberField.classNumber K:ℝ) * heckeConductorClassConstant K * (X+U^2)) *
        ∑ c : ClassGroup (𝓞 K), ∑ J ∈ B c, ‖v c J‖^2 := by
  apply actualHecke_conductor_sieve_of_fiber_bound K hU hX T hT A hA
    (NumberField.classNumber K) _ B hB v
  intro M hM χ _
  exact EvenIdealRayCharacter.residue_fiber_card_le_classNumber M.property
    (fun ψ : EvenIdealRayCharacter K M.val => ψ) (A M)
    (EvenIdealRayCharacter.coprimeSeparatedOn_of_coefficient_injective _ _ (hsep M hM)) χ

theorem exists_coefficient_separated_subfamily {M : Ideal (𝓞 K)}
    (A : Finset (EvenIdealRayCharacter K M)) :
    ∃ A' : Finset (EvenIdealRayCharacter K M), A' ⊆ A ∧
      Set.InjOn (fun ψ : EvenIdealRayCharacter K M => ψ.coefficient) A' ∧
      A'.image (fun ψ => ψ.coefficient) = A.image (fun ψ => ψ.coefficient) := by
  have hs : Set.SurjOn (fun ψ : EvenIdealRayCharacter K M => ψ.coefficient)
      (↑A) (↑(A.image fun ψ => ψ.coefficient)) := by
    intro a ha
    obtain ⟨ψ,hψ,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨ψ,hψ,rfl⟩
  obtain ⟨A',hsub,hinj,heq⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn
      (f := fun ψ : EvenIdealRayCharacter K M => ψ.coefficient)
      (A : Set (EvenIdealRayCharacter K M)) (A.image fun ψ => ψ.coefficient) hs
  exact ⟨A',fun _ h => hsub h,hinj,heq⟩

def coefficientClassPolynomial (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K), ∑ J ∈ B c, v c J * a ⟨J.val,J.property.1⟩

theorem coefficientClassPolynomial_eq_actual {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    coefficientClassPolynomial K ψ.coefficient B v = ψ.classGroupHeckePolynomial B v := rfl

/-- A conductor large sieve over the actual coefficient image of any finite
primitive Hecke family. All duplicate auxiliary presentations are removed by
construction, and the class-number loss is proved rather than assumed. -/
theorem actualHecke_coefficientFamily_conductor_sieve
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    (∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
      ‖coefficientClassPolynomial K a B v‖^2) ≤
      ((NumberField.classNumber K:ℝ) * heckeConductorClassConstant K * (X+U^2)) *
        ∑ c : ClassGroup (𝓞 K), ∑ J ∈ B c, ‖v c J‖^2 := by
  choose A' hsub hinj heq using fun M : IdealConductorModulus K =>
    exists_coefficient_separated_subfamily K (A M)
  have hp : ∀ M ∈ T, ∀ ψ ∈ A' M, IsPrimitiveOnIdeals ψ.residue :=
    fun M hM ψ hψ => hA M hM ψ (hsub M hψ)
  have H := actualHecke_conductor_sieve_of_distinct_coefficients K hU hX T hT A' hp
    (fun M _ => hinj M) B hB v
  convert H using 1
  apply Finset.sum_congr rfl
  intro M _
  rw [← heq M,Finset.sum_image (hinj M)]
  rfl

end
end ArtinMatthews.VaryingKummerAnalytic
