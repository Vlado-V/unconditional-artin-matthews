module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# The cubic inversion argument behind the abelian intersection

If conjugation sends an element of exponent three to its inverse, that element
is itself a commutator. Consequently every homomorphism to an abelian group
kills it. Via restriction homomorphisms and the Galois correspondence, this
shows that an abelian field can meet a cubic inversion extension only in its
specified fixed field.

The final theorems use actual intermediate fields and automorphism groups.
For the manuscript's specific radical field, construction of that field and
proof of its exponent-three and conjugation properties are still required;
they are explicit hypotheses here, not asserted Kummer-theory facts.
-/

open scoped commutatorElement

namespace ArtinMatthews

/-- In an exponent-three subgroup inverted by conjugation, each element is
already a commutator with the conjugating element. The conjugating element
need not itself be assumed to be an involution for this implication. -/
theorem commutator_eq_self_of_cube_eq_one_of_inversion
    {G : Type*} [Group G] {σ h : G}
    (hthree : h ^ 3 = 1) (hinv : σ * h * σ⁻¹ = h⁻¹) :
    ⁅σ, h⁆ = h := by
  calc
    ⁅σ, h⁆ = (σ * h * σ⁻¹) * h⁻¹ := rfl
    _ = h⁻¹ * h⁻¹ := by rw [hinv]
    _ = (h ^ 3)⁻¹ * h := by group
    _ = h := by rw [hthree]; simp

/-- Every homomorphism to a commutative group kills a cubic element inverted
by an inner conjugation. Commutativity is stated directly for the target's
existing group operation. -/
theorem hom_eq_one_of_cube_eq_one_of_inversion
    {G A : Type*} [Group G] [Group A] (f : G →* A)
    (hcomm : ∀ a b : A, a * b = b * a) {σ h : G}
    (hthree : h ^ 3 = 1) (hinv : σ * h * σ⁻¹ = h⁻¹) :
    f h = 1 := by
  rw [← commutator_eq_self_of_cube_eq_one_of_inversion hthree hinv,
    map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)

/-- An exponent-three subgroup inverted by an inner conjugation maps trivially
to every abelian group. This applies in particular to an abelian normal
subgroup and a conjugating involution, but those extra assumptions are not
needed once the inversion identity is known. -/
theorem cubicSubgroup_le_ker_of_inversion
    {G A : Type*} [Group G] [Group A] (H : Subgroup G) (σ : G)
    (f : G →* A) (hcomm : ∀ a b : A, a * b = b * a)
    (hthree : ∀ h ∈ H, h ^ 3 = 1)
    (hinv : ∀ h ∈ H, σ * h * σ⁻¹ = h⁻¹) :
    H ≤ f.ker := by
  intro h hh
  exact hom_eq_one_of_cube_eq_one_of_inversion f hcomm (hthree h hh) (hinv h hh)

/-- The subgroup occurring in the cubic inversion argument lies in the full
commutator subgroup. -/
theorem cubicSubgroup_le_commutator_of_inversion
    {G : Type*} [Group G] (H : Subgroup G) (σ : G)
    (hthree : ∀ h ∈ H, h ^ 3 = 1)
    (hinv : ∀ h ∈ H, σ * h * σ⁻¹ = h⁻¹) :
    H ≤ commutator G := by
  intro h hh
  rw [← commutator_eq_self_of_cube_eq_one_of_inversion (hthree h hh) (hinv h hh)]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top h)

/-- Every abelian Galois intermediate field lies in the fixed field selected by
the cubic inversion subgroup. The proof uses the actual restriction map on
Galois automorphisms and its kernel. -/
theorem abelian_intermediateField_le_of_cubic_inversion
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (F E : IntermediateField k K) [IsAbelianGalois k E]
    (σ : Gal(K/k))
    (hthree : ∀ h ∈ F.fixingSubgroup, h ^ 3 = 1)
    (hinv : ∀ h ∈ F.fixingSubgroup, σ * h * σ⁻¹ = h⁻¹) :
    E ≤ F := by
  have hker : F.fixingSubgroup ≤ (AlgEquiv.restrictNormalHom E).ker :=
    cubicSubgroup_le_ker_of_inversion F.fixingSubgroup σ
      (AlgEquiv.restrictNormalHom E) (fun a b => mul_comm' a b) hthree hinv
  rw [E.restrictNormalHom_ker] at hker
  have hle : E ≤ IntermediateField.fixedField F.fixingSubgroup :=
    (IntermediateField.le_iff_le F.fixingSubgroup E).mpr hker
  rwa [IsGalois.fixedField_fixingSubgroup] at hle

/-- If the specified fixed field is itself contained in an abelian Galois
intermediate field, then they are equal. -/
theorem abelian_intermediateField_eq_of_cubic_inversion
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (F E : IntermediateField k K) [IsAbelianGalois k E]
    (hFE : F ≤ E) (σ : Gal(K/k))
    (hthree : ∀ h ∈ F.fixingSubgroup, h ^ 3 = 1)
    (hinv : ∀ h ∈ F.fixingSubgroup, σ * h * σ⁻¹ = h⁻¹) :
    E = F :=
  le_antisymm (abelian_intermediateField_le_of_cubic_inversion F E σ hthree hinv) hFE

/-- The intersection statement in a common overfield: an abelian Galois field
meets a finite cubic inversion extension in exactly the specified fixed field,
provided that field lies in both extensions. -/
theorem abelian_intersection_eq_of_cubic_inversion
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K F L : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [IsAbelianGalois k L]
    (hFK : F ≤ K) (hFL : F ≤ L) (σ : Gal(K/k))
    (hthree : ∀ h ∈ (F.comap K.val).fixingSubgroup, h ^ 3 = 1)
    (hinv : ∀ h ∈ (F.comap K.val).fixingSubgroup, σ * h * σ⁻¹ = h⁻¹) :
    K ⊓ L = F := by
  let E : IntermediateField k K := L.comap K.val
  let eL : E →ₐ[k] L :=
    { toFun := fun x => ⟨((x : K) : Ω), x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have : IsAbelianGalois k E := IsAbelianGalois.of_algHom eL
  have hle : E ≤ F.comap K.val :=
    abelian_intermediateField_le_of_cubic_inversion (F.comap K.val) E σ hthree hinv
  apply le_antisymm
  · intro x hx
    exact hle (show (⟨x, hx.1⟩ : K) ∈ E from hx.2)
  · exact le_inf hFK hFL

/-- Cyclotomic fields are abelian by Mathlib's cyclotomic Galois theorem, so
there is no further group-theoretic compatibility factor in their intersection.
For equation (9.1), take `k = ℚ`, the manuscript's radical field for `K`,
`F = ℚ(ζ₃)`, and `L = ℚ(ζ_M)`; the two containment and cubic-action hypotheses
must still be established for those concrete fields. -/
theorem cyclotomic_intersection_eq_of_cubic_inversion
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K F L : IntermediateField k Ω) (M : ℕ)
    [FiniteDimensional k K] [IsGalois k K] [IsCyclotomicExtension {M} k L]
    (hFK : F ≤ K) (hFL : F ≤ L) (σ : Gal(K/k))
    (hthree : ∀ h ∈ (F.comap K.val).fixingSubgroup, h ^ 3 = 1)
    (hinv : ∀ h ∈ (F.comap K.val).fixingSubgroup, σ * h * σ⁻¹ = h⁻¹) :
    K ⊓ L = F := by
  have : IsAbelianGalois k L := IsCyclotomicExtension.isAbelianGalois {M} k L
  exact abelian_intersection_eq_of_cubic_inversion K F L hFK hFL σ hthree hinv

attribute [-instance] DivisionRing.toRatAlgebra in
/-- Equation (9.1) over `ℚ`, conditional only on the actual radical field's
finite-Galois and cubic-inversion properties and on its containing `ℚ(ζ₃)`.
The containment `ℚ(ζ₃) ≤ ℚ(ζ_M)` is proved from `3 ∣ M`, rather than assumed.
`F` and `L` are genuine cyclotomic intermediate fields of the same overfield. -/
theorem cubic_cyclotomic_intersection_eq
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (K F L : IntermediateField ℚ Ω) (M : ℕ) [NeZero M]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    [IsCyclotomicExtension {3} ℚ F] [IsCyclotomicExtension {M} ℚ L]
    (hFK : F ≤ K) (hM : 3 ∣ M) (σ : Gal(K/ℚ))
    (hthree : ∀ h ∈ (F.comap K.val).fixingSubgroup, h ^ 3 = 1)
    (hinv : ∀ h ∈ (F.comap K.val).fixingSubgroup, σ * h * σ⁻¹ = h⁻¹) :
    K ⊓ L = F := by
  have hFL : F ≤ L := IntermediateField.isCyclotomicExtension_le_of_dvd ℚ Ω 3 M F L hM
  exact cyclotomic_intersection_eq_of_cubic_inversion K F L M hFK hFL σ hthree hinv

end ArtinMatthews
