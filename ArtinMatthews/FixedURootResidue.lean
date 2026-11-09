module

public import ArtinMatthews.FixedURootCount
public import ArtinMatthews.FixedURootEnvelope
public import ArtinMatthews.FixedURootDensity


set_option backward.privateInPublic true
@[expose] public section

/-!
# The fixed-u root-residue count

This is the literal fixed-first-coordinate step in PD, section 3. The modulus
is squarefree, the prescribed matrix has determinant one, and the pair set is
the three displayed integer congruences. The error constant is independent of
all moduli, residues, and rectangle endpoints.
-/

namespace ArtinMatthews
open scoped BigOperators

/-- The actual fixed-`u` congruence count with its Euler main term and the
uniform `u^0.99 S^2` rectangle discrepancy. -/
theorem fixedURootResidue_count : ∃ C : ℝ, 0 < C ∧
    ∀ (u S : ℕ) (c₀ v₀ d₀ : ℤ) (x₀ x₁ y₀ y₁ : ℝ)
      (lcI rcI lcJ rcJ : Bool),
      0 < u → Squarefree S →
      Int.ModEq (S : ℤ) ((u : ℤ) * d₀ - c₀ * v₀) 1 →
      x₀ ≤ x₁ → x₁-x₀ ≤ u → y₀ ≤ y₁ →
      |((fixedURootPairs u S c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ).card : ℝ) -
        (x₁-x₀)*(y₁-y₀)/((u : ℝ)*(S : ℝ)^2) *
          (∏ p ∈ u.primeFactors.filter (fun p => ¬ p ∣ S), (1-(p : ℝ)⁻¹))| ≤
        C * (u : ℝ)^(99/100 : ℝ) * (S : ℝ)^2 * (2+(y₁-y₀)/u) := by
  obtain ⟨C,hC,herr⟩ := fixedURootRectangleError_bound
  refine ⟨C,hC,?_⟩
  intro u S c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ hu hS hdet hx hlen hy
  obtain ⟨hg,hq,hdiv,hcop,heq⟩ := fixedURoot_squarefree_split u S hu hS
  have hdet' : Int.ModEq
      ((Nat.gcd S u * (S / Nat.gcd S u) : ℕ) : ℤ)
      ((u : ℤ)*d₀-c₀*v₀) 1 := by simpa only [heq] using hdet
  have hc := fixedURootPairs_count_error u (Nat.gcd S u) (S / Nat.gcd S u)
    hu hg hq hdiv hcop c₀ v₀ d₀ hdet' x₀ x₁ y₀ y₁ hx hy lcI rcI lcJ rcJ
  have heuler := fixedURootDensity_eq_product_modulus hu hg hdiv
    (hcop.of_dvd_right (dvd_mul_right u (Nat.gcd S u)))
  unfold fixedURootDensity at heuler
  rw [heuler,heq] at hc
  refine hc.trans ?_
  simpa only [heq] using herr u (Nat.gcd S u) (S / Nat.gcd S u)
    (x₁-x₀) (y₁-y₀) hu hg hq (sub_nonneg.mpr hx) hlen (sub_nonneg.mpr hy)

end ArtinMatthews
