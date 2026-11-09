module

public import ArtinMatthews.MarkedMinorArcRawEdgeChoices
public import ArtinMatthews.MarkedMinorArcRawCleanKernel
public import ArtinMatthews.MarkedMinorArcBanRawEntry


set_option backward.privateInPublic true
@[expose] public section

/-! The literal full raw store/promote edge operation. Geometric cutoffs,
old and remaining hit damping, promotion V^-1, fresh tilted draws, physical
endpoint tests, and the full cross-edge ban are all retained. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators

/-- Actual prime integration/promotion factor: a promoted old prime pays
V_i^-1 and introduces no fresh-prime summation or measure factor. -/
noncomputable def markedRawEdgeChoicePrimeMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : ℝ :=
  ∏ j, match h : choice.promotions j with
    | none => ν j (by simpa only [h] using choice.fresh j)
    | some _ => (V j)⁻¹

/-- The literal full raw edge coefficient before fresh-prime integration. -/
noncomputable def markedRawEdgeChoiceCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) : ℂ := by
  classical
  let target := markedRawEdgeTargetState hZ s choice
  let lastSource := ((markedRawActiveSplit pads) s.2.1).2
  let lastTarget := markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh
  let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
  let t := markedMinorIntegerDet s.1.1 target.1.1/(D : ℤ)
  exact if d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀ then
    if (D : ℤ) ∣ markedMinorIntegerDet s.1.1 target.1.1 then
      if MarkedRawFullCrossBan s.2.1 lastTarget then 0 else
        ((d₀/(D : ℝ) : ℝ) : ℂ)*
          ((ρ^(markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2)) : ℝ) : ℂ)*
          markedRawEndpointFactor hZ 1 χ s*
          η ((markedRawLastProduct lastSource : ℝ)/Y)*η ((markedRawLastProduct lastTarget : ℝ)/Y)*
          ψ ((t : ℝ)/Y)*
          (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
            fourier (t-(markedRawLastProduct lastSource : ℤ)+(markedRawLastProduct lastTarget : ℤ)) θ
              ∂AddCircle.haarAddCircle)*
          ((ρ^(markedRawPendingHits target.2.2 target.1.1 (hZ _ target.1.2)) : ℝ) : ℂ)*
          markedRawEndpointFactor hZ 1 χ target
    else 0 else 0

/-- The literal full row operation sums every actual eligible old-index
choice, source-store subset and target position, with precisely the fresh
prime factors specified by the source measure. -/
noncomputable def markedRawEdgeApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ choice : MarkedRawEdgeChoice hZ s,
    (markedRawEdgeChoicePrimeMass ν V hZ s choice : ℂ)*
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice*
      f (markedRawEdgeTargetState hZ s choice)

/-- Physical endpoint tests times literal old-hit damping are exactly the
already proved endpoint factor; this identity also holds at rho=0. -/
theorem markedRawEndpointFactor_damping {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ρ : ℝ) (χ : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) :
    ((ρ^(markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2)) : ℝ) : ℂ)*
      markedRawEndpointFactor hZ 1 χ s=markedRawEndpointFactor hZ ρ χ s := by
  classical
  unfold markedRawEndpointFactor
  split_ifs <;> simp only [one_pow,Complex.ofReal_one,one_mul,mul_zero]

/-- The clean choice pays exactly the actual product of fresh tilted atoms. -/
theorem markedRawCleanEdgeChoice_prime_mass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (target : Z) (fresh : (j : J) → ↥(P j)) :
    markedRawEdgeChoicePrimeMass ν V hZ s (markedRawCleanEdgeChoice hZ s target fresh)=
      markedRawLastMass ν fresh := rfl

end ArtinMatthews
