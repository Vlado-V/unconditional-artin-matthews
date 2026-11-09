module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedRow


set_option backward.privateInPublic true
@[expose] public section

/-! Exact positive charged row/action identity for the coupled transpose.
No state mass or prime atom is divided. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgeChoiceCharge_ofReal {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (δ γ : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCharge (fun j => (δ j:ℂ)) (fun j => (γ j:ℂ)) hZ s c =
      ((∏ j,δ j^(if (c.promotions j).isSome then 1 else 0)*γ j^(if c.store j then 1 else 0):ℝ):ℂ) := by
  simp only [markedRawEdgeChoiceCharge,Complex.ofReal_prod,Complex.ofReal_mul,Complex.ofReal_pow]

/-- A positive charged absolute row is precisely the charged absolute
action on the true target Schur weight, divided only by the source weight. -/
theorem markedRawEdgeChargedWeightedAbsRow_mul_weight_eq_apply
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hδ : ∀ j,0 ≤ δ j) (hγ : ∀ j,0 ≤ γ j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    {v₀ : ℝ} (hv₀ : 0 < v₀) (s : MarkedRawState P (pads+1) B Z) :
    (markedRawEdgeChargedWeightedAbsRow ν (fun j => (δ j:ℂ)) (fun j => (γ j:ℂ))
      hZ K v₀ s (fun _ => 1):ℂ)*(markedRawMemorySchurWeight v₀ s.2.2:ℂ) =
      markedRawEdgeChargedApply ν (fun j => (δ j:ℂ)) (fun j => (γ j:ℂ)) hZ
        (fun s t => (‖K s t‖:ℂ)) (fun t => (markedRawMemorySchurWeight v₀ t.2.2:ℂ)) s := by
  classical
  have hs := (markedRawMemorySchurWeight_pos hv₀ s.2.2).ne'
  unfold markedRawEdgeChargedWeightedAbsRow markedRawEdgeChargedApply
  rw [← Complex.ofReal_mul,Finset.sum_mul,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro c _
  let R : ℝ := ∏ j,δ j^(if (c.promotions j).isSome then 1 else 0)*γ j^(if c.store j then 1 else 0)
  have hR : 0 ≤ R := Finset.prod_nonneg (fun j _ =>
    mul_nonneg (pow_nonneg (hδ j) _) (pow_nonneg (hγ j) _))
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν (fun _ => 1) hν
    (fun _ => by norm_num) hZ s c
  have hc : markedRawEdgeChoiceCharge (fun j => (δ j:ℂ)) (fun j => (γ j:ℂ)) hZ s c = (R:ℂ) :=
    markedRawEdgeChoiceCharge_ofReal δ γ hZ s c
  simp only [mul_one]
  rw [mul_assoc,div_mul_cancel₀ _ hs]
  simp only [hc,markedRawEdgeChoiceFreshMass,norm_mul,Complex.norm_real,Real.norm_of_nonneg hR,Real.norm_of_nonneg hm,
    Complex.ofReal_mul]
  rfl

end
end ArtinMatthews
