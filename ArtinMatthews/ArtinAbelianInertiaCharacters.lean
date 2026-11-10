module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed


set_option backward.privateInPublic true
@[expose] public section

/-! Characters of the actual inertia quotient correspond exactly to global
abelian characters trivial on inertia. Their remaining local factors are one. -/

noncomputable section
namespace ArtinMatthews.AbelianLocal
open scoped Classical BigOperators

variable {G : Type*} [CommGroup G] [Finite G]

/-- The actual quotient universal property gives the inertia-trivial character family. -/
def inertiaCharacterEquiv (I : Subgroup G) :
    ((G ⧸ I) →* ℂˣ) ≃ {χ : G →* ℂˣ // I ≤ χ.ker} where
  toFun χ := ⟨χ.comp (QuotientGroup.mk' I), fun x hx => by
    change χ (QuotientGroup.mk x) = 1
    rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]⟩
  invFun χ := QuotientGroup.lift I χ.val χ.property
  left_inv χ := by
    ext x
    rfl
  right_inv χ := by
    apply Subtype.ext
    ext x
    rfl

omit [Finite G] in
@[simp] theorem inertiaCharacterEquiv_apply (I : Subgroup G)
    (χ : (G ⧸ I) →* ℂˣ) (σ : G) :
    (inertiaCharacterEquiv I χ).val σ = χ (QuotientGroup.mk σ) := rfl

/-- Full global-character product with its precise ramified one-dimensional
local factors equals the quotient-character Euler product. -/
theorem prod_all_characters_inertia_factor (I : Subgroup G) (σ : G) (T : ℂ) :
    letI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
    letI : Fintype ((G ⧸ I) →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : G →* ℂˣ, if I ≤ χ.ker then (1 - (χ σ : ℂ) * T)⁻¹ else 1) =
      ∏ χ : (G ⧸ I) →* ℂˣ, (1 - (χ (QuotientGroup.mk σ) : ℂ) * T)⁻¹ := by
  let : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  let : Fintype ((G ⧸ I) →* ℂˣ) := Fintype.ofFinite _
  let : Fintype {χ : G →* ℂˣ // I ≤ χ.ker} := Fintype.ofFinite _
  calc
    _ = ∏ χ : {χ : G →* ℂˣ // I ≤ χ.ker}, (1 - (χ.val σ : ℂ) * T)⁻¹ := by
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      exact Finset.prod_subtype _ (by simp) _
    _ = _ := (Fintype.prod_equiv (inertiaCharacterEquiv I)
      (fun χ => (1 - (χ (QuotientGroup.mk σ) : ℂ) * T)⁻¹)
      (fun χ => (1 - (χ.val σ : ℂ) * T)⁻¹) (fun _ => rfl)).symm

end ArtinMatthews.AbelianLocal
