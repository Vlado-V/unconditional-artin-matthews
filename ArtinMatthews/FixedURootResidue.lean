module

public import ArtinMatthews.FixedURootCount
public import ArtinMatthews.FixedURootDensity
public import ArtinMatthews.FixedURootEnvelope
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
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
