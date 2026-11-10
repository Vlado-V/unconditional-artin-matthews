module

public import ArtinMatthews.VaryingKummerAnalyticRayCharacterMultiplicityAlgebra
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine fixed-modulus residue-fiber multiplicity. Actual coprime-ideal
characters, rather than auxiliary structure values at bad primes, determine
the separated family. The class-number bound follows from linear
independence of complex class-group characters. -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenRayCharacter
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem agreesOnCoprimeIdeals_iff_coefficient_eq (ψ φ : EvenRayCharacter K N) :
    AgreesOnCoprimeIdeals ψ φ ↔ ψ.coefficient = φ.coefficient := by
  constructor
  · intro h
    ext J
    unfold coefficient
    by_cases hc : IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
    · rw [ite_eq_left hc, ite_eq_left hc]
      have H := h (underlyingIdeal J) (underlyingIdeal_ne_bot J) hc
      rw [underlyingIdeal_unit] at H
      exact congrArg (fun z : ℂˣ => (z : ℂ)) H
    · rw [ite_eq_right hc, ite_eq_right hc]
  · intro h I hI hc
    have H := congrFun h
      (⟨integralIdealFractionalUnit I hI, FractionalIdeal.coeIdeal_le_one⟩ : integralFractionalIdeals K)
    simp only [coefficient, underlyingIdeal_integralUnit, ite_eq_left hc] at H
    exact Units.ext H

def CoprimeSeparatedOn {ι : Type*} (F : ι → EvenRayCharacter K N) (A : Finset ι) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, AgreesOnCoprimeIdeals (F i) (F j) → i = j

omit [NeZero N] in
theorem coprimeSeparatedOn_of_coefficient_injective {ι : Type*}
    (F : ι → EvenRayCharacter K N) (A : Finset ι)
    (hF : Set.InjOn (fun i => (F i).coefficient) A) : CoprimeSeparatedOn F A := by
  intro i hi j hj h
  exact hF hi hj ((agreesOnCoprimeIdeals_iff_coefficient_eq _ _).mp h)

omit [NeZero N] in
theorem coprimeSeparatedOn_of_witness {ι : Type*}
    (F : ι → EvenRayCharacter K N) (A : Finset ι)
    (hF : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥),
      IsCoprime I (rationalModulusIdeal (𝓞 K) N) ∧
        (F i).idealHom (integralIdealFractionalUnit I hI) ≠
          (F j).idealHom (integralIdealFractionalUnit I hI)) : CoprimeSeparatedOn F A := by
  intro i hi j hj h
  by_contra hij
  obtain ⟨I, hI, hc, hn⟩ := hF i hi j hj hij
  exact hn (h I hI hc)

/-- A residue fiber of an actual coprime-character separated finite family
has cardinality at most the genuine ideal class number. -/
theorem residue_fiber_card_le_classNumber {ι : Type*}
    (F : ι → EvenRayCharacter K N) (A : Finset ι) (hF : CoprimeSeparatedOn F A)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) :
    (A.filter fun i => (F i).residue = χ).card ≤ NumberField.classNumber K := by
  classical
  let B := A.filter fun i => (F i).residue = χ
  change B.card ≤ _
  by_cases hB : B.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hB
    have hr (i : {i // i ∈ B}) : (F i.val).residue = (F i₀).residue :=
      (Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp hi₀).2.symm
    let C : {i // i ∈ B} → (ClassGroup (𝓞 K) →* ℂ) :=
      fun i => sameResidueClassCharacter (F i.val) (F i₀) (hr i)
    have hC : Function.Injective C := by
      intro i j hij
      apply Subtype.ext
      apply hF i.val (Finset.mem_filter.mp i.property).1 j.val (Finset.mem_filter.mp j.property).1
      exact (sameResidueClassCharacter_eq_iff_agrees (F i.val) (F j.val) (F i₀) (hr i) (hr j)).mp hij
    have hlin := (linearIndependent_monoidHom (ClassGroup (𝓞 K)) ℂ).comp C hC
    have hc := hlin.fintype_card_le_finrank
    simpa only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card, NumberField.classNumber] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    exact Nat.zero_le _

/-- Residue-fiber multiplicity can be applied to any nonnegative row
energy, with the explicit class-number loss and no structure-level count. -/
theorem sum_residue_rows_le_classNumber {ι : Type*}
    (F : ι → EvenRayCharacter K N) (A : Finset ι) (hF : CoprimeSeparatedOn F A)
    (w : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ → ℝ) (hw : ∀ χ, 0 ≤ w χ) :
    (∑ i ∈ A, w (F i).residue) ≤
      (NumberField.classNumber K : ℝ) * ∑ χ ∈ A.image (fun i => (F i).residue), w χ := by
  classical
  have hs := Finset.sum_fiberwise_of_maps_to'
    (s := A) (t := A.image (fun i => (F i).residue)) (g := fun i => (F i).residue)
    (fun i hi => Finset.mem_image_of_mem _ hi) w
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  rw [← hs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro χ _
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast residue_fiber_card_le_classNumber F A hF χ) (hw χ)

end
end ArtinMatthews.VaryingKummerAnalytic.EvenRayCharacter
