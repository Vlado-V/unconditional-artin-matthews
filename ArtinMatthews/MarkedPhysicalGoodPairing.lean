module

public import ArtinMatthews.MarkedPhysicalBadRootEnergy
public import ArtinMatthews.MarkedMinorArcRawEdgeJointCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! Exact one-edge physical endpoint pairing and its source-first bad
split. No small-projection or root-replacement estimate is assumed. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalEdgeCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) : ℂ :=
  let u := markedPhysicalStateToRaw P hP (pads+1) Z s
  let v := markedPhysicalStateToRaw P hP (pads+1) Z t
  ((markedPhysicalMass V (pads+1) * ∏ j,(V j)⁻¹ : ℝ):ℂ) *
    (if ((markedRawActiveSplit pads) u.2.1).1 = ((markedRawActiveSplit pads) v.2.1).1 then
      (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ) *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) u v *
        (markedPhysicalEndpointDamping P (pads+1) q t.1.1.1:ℂ)
    else 0)

def markedPhysicalEdgePairing {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) : ℂ :=
  ∑ s,∑ t,markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t * star (f s) * g t

def markedPhysicalGoodVector {Ω : Type*} (G : Ω → Prop) (f : Ω → ℂ) : Ω → ℂ :=
  fun s => if G s then f s else 0

def markedPhysicalBadVector {Ω : Type*} (G : Ω → Prop) (f : Ω → ℂ) : Ω → ℂ :=
  fun s => if G s then 0 else f s

theorem markedPhysicalEdgePairing_good_bad {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector G f) (markedPhysicalGoodVector G g) +
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalBadVector G f) g +
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector G f) (markedPhysicalBadVector G g) := by
  unfold markedPhysicalEdgePairing
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hs : G s <;> by_cases ht : G t <;>
    simp [markedPhysicalGoodVector,markedPhysicalBadVector,hs,ht]

theorem markedComplexEdgePairing_cauchy {Ω : Type*} [Fintype Ω]
    (K : Ω × Ω → ℂ) (f g : Ω → ℂ) :
    ‖∑ z : Ω × Ω,K z * star (f z.1) * g z.2‖^2 ≤
      (∑ z : Ω × Ω,‖K z‖*‖f z.1‖^2) * (∑ z : Ω × Ω,‖K z‖*‖g z.2‖^2) := by
  have hn : ‖∑ z : Ω × Ω,K z * star (f z.1) * g z.2‖ ≤
      ∑ z : Ω × Ω,‖K z‖*‖f z.1‖*‖g z.2‖ := by
    simpa only [norm_mul,norm_star] using norm_sum_le Finset.univ (fun z : Ω × Ω => K z * star (f z.1) * g z.2)
  apply (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro z _
    exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
  · intro z _
    exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
  · intro z _
    exact le_of_eq (by ring)

theorem markedPhysicalEdgePairing_cauchy {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    ‖markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g‖^2 ≤
      (∑ s,∑ t,‖markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t‖*‖f s‖^2) *
      (∑ s,∑ t,‖markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t‖*‖g t‖^2) := by
  simpa only [Fintype.sum_prod_type,markedPhysicalEdgePairing] using
    markedComplexEdgePairing_cauchy
      (fun z : MarkedPhysicalState P (pads+1) Z × MarkedPhysicalState P (pads+1) Z =>
        markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q z.1 z.2) f g

theorem markedPhysicalEdgeCoefficient_damping_absorbed
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) (α β : ℕ → ℂ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t *
      star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) *
      markedPhysicalEndpointVector P (pads+1) α β t.1.1.1 =
    markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q 1 s t *
      star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) *
      markedPhysicalEndpointVector P (pads+1) α β t.1.1.1 := by
  have hs : star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) *
      (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ) =
      star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) := by
    simpa only [star_mul,Complex.star_def,Complex.conj_ofReal] using
      congrArg star (markedPhysicalEndpointVector_damped P (pads+1) q α β s.1.1.1)
  have ht := markedPhysicalEndpointVector_damped P (pads+1) q α β t.1.1.1
  have hd1 (z : ℤ × ℤ) : markedPhysicalEndpointDamping P (pads+1) 1 z = 1 := by
    simp [markedPhysicalEndpointDamping]
  unfold markedPhysicalEdgeCoefficient
  dsimp only
  split_ifs
  · simp only [hd1,Complex.ofReal_one,mul_one,one_mul]
    let c : ℂ := (markedPhysicalMass V (pads+1) * ∏ j,(V j)⁻¹:ℝ)
    let k := markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1)
      (markedPhysicalStateToRaw P hP (pads+1) Z s) (markedPhysicalStateToRaw P hP (pads+1) Z t)
    calc
      _ = c * k *
          (star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) *
            (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ)) *
          ((markedPhysicalEndpointDamping P (pads+1) q t.1.1.1:ℂ) *
            markedPhysicalEndpointVector P (pads+1) α β t.1.1.1) := by ring
      _ = _ := by rw [hs,ht]
  · simp

end
end ArtinMatthews
