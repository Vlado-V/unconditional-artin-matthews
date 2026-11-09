module

public import ArtinMatthews.PrincipalAngularPrimitiveMellin
public import ArtinMatthews.PrincipalAngularDedekindMellin
public import ArtinMatthews.KummerNonvanishingSplitting


set_option backward.privateInPublic true
@[expose] public section

/-! The exact remaining source06 infinity bounds on the actual cyclotomic
fields. Only those bounds are packaged below: no zero-free or splitting
assumption is part of the package. Constants and onsets may vary with q,
the primitive character and the selected finite bad set. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Filter Asymptotics
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical Topology
noncomputable section

def twelfthAngularRoot (q : ℕ) [NeZero q] : twelfthCyclotomicField q :=
  ⟨primeCyclotomicRoot 12,
    twelveCyclotomicField_le_twelfthCyclotomicField q (primeCyclotomicRoot_mem 12)⟩

theorem twelfthAngularRoot_isPrimitiveRoot (q : ℕ) [NeZero q] :
    IsPrimitiveRoot (twelfthAngularRoot q) 12 :=
  IsPrimitiveRoot.of_map_of_injective (f := (twelfthCyclotomicField q).val)
    (primeCyclotomicRoot_isPrimitiveRoot (by decide : 0 < 12)) Subtype.val_injective

/-- The remaining physical-source infinity estimates, with their exact
fixed exponent, on the fields needed for a given q. -/
structure TwelfthAngularSourceBounds (q : ℕ) [NeZero q] : Prop where
  principal : ∃ S : Finset (ArtinMatthews.ProbePrime (twelfthCyclotomicField q)),
    principalAngularCutoff (twelfthCyclotomicField q) (⊤ : Ideal (𝓞 (twelfthCyclotomicField q))) ⊆ S ∧
      principalAngularGaussianSignal (twelfthAngularRoot_isPrimitiveRoot q)
        (principalAngularTrivialRay (twelfthCyclotomicField q)) S =O[atTop]
          (fun x : ℝ => x ^ (7 / 15 - 1 / 20000 : ℝ))
  primitive : ∀ (f : Ideal (𝓞 (twelfthCyclotomicField q))) (_hf : f ≠ ⊥)
    (ψ : EvenIdealRayCharacter (twelfthCyclotomicField q) f)
    (_hprim : IsPrimitiveOnIdeals ψ.residue), ψ.IsNonprincipal →
    ψ.coefficient ≠ ψ.inverse.coefficient →
    Real.log (f.absNorm : ℝ) ≤ (12 * q : ℝ) * ((72 * (q : ℝ) ^ 2 + 2) * Real.log (12 * q)) →
    ∃ S : Finset (ArtinMatthews.ProbePrime (twelfthCyclotomicField q)),
      principalAngularCutoff (twelfthCyclotomicField q) f ⊆ S ∧
        principalAngularGaussianSignal (twelfthAngularRoot_isPrimitiveRoot q) ψ S =O[atTop]
          (fun x : ℝ => x ^ (7 / 15 - 1 / 20000 : ℝ))

theorem TwelfthAngularSourceBounds.principal_nonzero {q : ℕ} [NeZero q]
    (h : TwelfthAngularSourceBounds q) {s : ℂ} (hs : 1 - 1 / 1000000 < s.re) :
    mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s ≠ 0 := by
  obtain ⟨S, hS, hbound⟩ := h.principal
  exact mixedRegularizedDedekindZeta_ne_zero_of_angularSignal_source06_bound
    (twelfthAngularRoot_isPrimitiveRoot q) S hS hbound hs

theorem TwelfthAngularSourceBounds.primitive_nonzero {q : ℕ} [NeZero q]
    (h : TwelfthAngularSourceBounds q)
    (f : Ideal (𝓞 (twelfthCyclotomicField q))) (hf : f ≠ ⊥)
    (ψ : EvenIdealRayCharacter (twelfthCyclotomicField q) f)
    (hprim : IsPrimitiveOnIdeals ψ.residue) (hnp : ψ.IsNonprincipal)
    (hnonreal : ψ.coefficient ≠ ψ.inverse.coefficient)
    (hcond : Real.log (f.absNorm : ℝ) ≤
      (12 * q : ℝ) * ((72 * (q : ℝ) ^ 2 + 2) * Real.log (12 * q)))
    {s : ℂ} (hs : 1 - 1 / 1000000 < s.re) : ψ.primitiveContinued hf hprim s ≠ 0 := by
  obtain ⟨S, hS, hbound⟩ := h.primitive f hf ψ hprim hnp hnonreal hcond
  exact primitiveContinued_ne_zero_of_angularSignal_source06_bound
    (twelfthAngularRoot_isPrimitiveRoot q) ψ hf hprim hnp S hS hbound hs

/-- Actual q-radical zero transfer, with both principal and primitive
alternatives discharged by their corrected source bounds. -/
theorem primeKummer_zero_region_of_angular_source_bounds
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hprime : q.Prime) (hq : 2 < q) (haq : a.natAbs ≤ q)
    (h : TwelfthAngularSourceBounds q) :
    ∀ s : ℂ, mixedCompletedDedekindXi (primeKummerField q a) s = 0 →
      s.re ≤ 1 - 1 / 1000000 := by
  apply primeKummer_zero_region_of_source_nonvanishing q a hprime hq haq
    (1 - 1 / 1000000) (by norm_num)
  · intro s hs
    exact h.principal_nonzero hs
  · intro f hf ψ hprim hnp hnonreal hcond s hs
    exact h.primitive_nonzero f hf ψ hprim hnp hnonreal hcond hs

end
end ArtinMatthews.VaryingKummerAnalytic
