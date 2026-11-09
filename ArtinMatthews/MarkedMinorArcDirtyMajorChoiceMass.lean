module

public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceFiber
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedFactors


set_option backward.privateInPublic true
@[expose] public section

/-! Exact prime integration and finite partition into the genuine major
choice fibers. These keep the actual old index multiplicities. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyMajorChoiceFiber_prime_mass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) (store : J → Bool)
    (indices : MarkedRawPromotionTuple s.2.2 I) (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1))
    (choice : MarkedDirtyFixedEdgeChoice hZ s I)
    (hc : choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh) :
    markedRawEdgeChoicePrimeMass ν V hZ s choice.1=
      finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh*(∏ j ∈ I, (V j)⁻¹) := by
  have hf := congrArg (fun labels => labels.2.2) (Finset.mem_filter.mp hc).2
  rw [markedDirtyFixedEdgeChoice_prime_mass,hf]

theorem markedDirtyMajorChoice_fiberwise_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (f : MarkedDirtyFixedEdgeChoice hZ s I → ℝ) :
    (∑ choice : MarkedDirtyFixedEdgeChoice hZ s I, f choice)=
      ∑ store : J → Bool, ∑ indices : MarkedRawPromotionTuple s.2.2 I,
        ∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
          ∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh, f choice := by
  classical
  have hh := Finset.sum_fiberwise (Finset.univ : Finset (MarkedDirtyFixedEdgeChoice hZ s I))
    (fun choice => (markedDirtyFixedEdgeChoiceCode hZ s I choice).2) f
  simpa only [Fintype.sum_prod_type,markedDirtyMajorChoiceFiber] using hh.symm

end ArtinMatthews
