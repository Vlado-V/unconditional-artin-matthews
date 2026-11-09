module

public import ArtinMatthews.MarkedMinorArcRawEdgeJointReverse


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugating and reversing the physical geometric multiplier is
different from taking the adjoint of the whole memory edge. These lemmas
identify the geometric reversal while leaving all memory charges alone. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeAdjointCutoff (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
    (markedRawEdgeReflectedCutoff ψ)

@[simp] theorem markedRawEdgeAdjointCutoff_apply (ψ : SchwartzMap ℝ ℂ) (u : ℝ) :
    markedRawEdgeAdjointCutoff ψ u = star (ψ (-u)) := rfl

theorem markedRawEdgeAdjointCutoff_bounds (ψ : SchwartzMap ℝ ℂ) {A W : ℝ}
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    (∀ u, ‖markedRawEdgeAdjointCutoff ψ u‖ ≤ W) ∧
      Function.support (markedRawEdgeAdjointCutoff ψ) ⊆ Set.Icc (-A) A := by
  constructor
  · intro u
    simpa only [markedRawEdgeAdjointCutoff_apply, norm_star] using hψ (-u)
  · intro u hu
    have hn : ψ (-u) ≠ 0 := fun h => hu (by simp only [markedRawEdgeAdjointCutoff_apply, h, star_zero])
    have hh := hsupp hn
    constructor <;> linarith [hh.1, hh.2]

theorem markedRawEndpointFactor_star
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEndpointFactor hZ ρ (fun s => star (χ s)) s = star (markedRawEndpointFactor hZ ρ χ s) := by
  unfold markedRawEndpointFactor
  split_ifs <;> simp only [star_mul, Complex.star_def, Complex.conj_ofReal, map_zero, mul_comm]

theorem markedRawEdgeJointCoefficient_geometric_adjoint
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (copied : MarkedRawActive P pads) (x y : Z)
    (a b : (j : J) → ↥(P j)) (m n : MarkedRawMemory P B) :
    markedRawEdgeJointCoefficient hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
      d₀ Y Q ρ (fun s => star (χ s))
      (y, ((markedRawActiveSplit pads).symm (copied,b),n))
      (x, ((markedRawActiveSplit pads).symm (copied,a),m)) =
      star (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ
        (x, ((markedRawActiveSplit pads).symm (copied,a),m))
        (y, ((markedRawActiveSplit pads).symm (copied,b),n))) := by
  let s : MarkedRawState P (pads+1) B Z :=
    (x, ((markedRawActiveSplit pads).symm (copied,a),m))
  let t : MarkedRawState P (pads+1) B Z :=
    (y, ((markedRawActiveSplit pads).symm (copied,b),n))
  change markedRawEdgeJointCoefficient hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
    d₀ Y Q ρ (fun s => star (χ s)) t s = star (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t)
  rw [markedRawEdgeJointCoefficient_factor, markedRawEdgeJointCoefficient_factor]
  have hs := Equiv.apply_symm_apply (markedRawActiveSplit (P := P) pads) (copied,a)
  have ht := Equiv.apply_symm_apply (markedRawActiveSplit (P := P) pads) (copied,b)
  dsimp only [s,t]
  rw [hs,ht]
  dsimp only
  have hdet : markedMinorIntegerDet y.1 x.1 = -markedMinorIntegerDet x.1 y.1 := by
    unfold markedMinorIntegerDet
    ring
  rw [hdet]
  simp only [dvd_neg, markedRawEndpointFactor_star]
  by_cases hsrc : markedRawEndpointFactor hZ ρ χ s = 0
  · split_ifs <;> simp only [s] at hsrc ⊢ <;> simp [hsrc]
  by_cases htgt : markedRawEndpointFactor hZ ρ χ t = 0
  · split_ifs <;> simp only [t] at htgt ⊢ <;> simp [htgt]
  have hban : MarkedRawFullCrossBan ((markedRawActiveSplit pads).symm (copied,a)) b ↔
      MarkedRawFullCrossBan ((markedRawActiveSplit pads).symm (copied,b)) a :=
    markedRawFullCrossBan_symmetric hdisj copied a b
      (markedRawEndpointFactor_ne_zero_distinct hZ ρ χ s hsrc)
      (markedRawEndpointFactor_ne_zero_distinct hZ ρ χ t htgt)
  simp only [hban]
  split_ifs with hdyad hdiv hbad <;> try simp only [star_zero]
  rw [Int.neg_ediv_of_dvd hdiv]
  have hcut : (markedRawEdgeAdjointCutoff ψ : ℝ → ℂ) = markedBanAdjointCutoff ψ := rfl
  rw [hcut, markedBanEdgeKernel_adjoint]
  simp only [map_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem markedRawEdgeJointCoefficient_target_geometric_adjoint
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeJointCoefficient hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
      d₀ Y Q ρ (fun s => star (χ s)) s (markedRawEdgeTargetState hZ s c) =
      star (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawEdgeTargetState hZ s c) s) := by
  let copied := ((markedRawActiveSplit pads) s.2.1).1
  let a := ((markedRawActiveSplit pads) s.2.1).2
  let b := markedRawEdgeTargetLast s.2.2 c.promotions c.fresh
  have hs : (s.1,((markedRawActiveSplit pads).symm (copied,a),s.2.2)) = s := by
    change (s.1,((markedRawActiveSplit pads).symm ((markedRawActiveSplit pads) s.2.1),s.2.2)) = s
    rw [Equiv.symm_apply_apply]
  have hh := markedRawEdgeJointCoefficient_geometric_adjoint hdisj hZ ψ η d₀ Y Q ρ χ
    copied c.target s.1 b a (markedRawEdgeTargetMemory hZ s c) s.2.2
  rw [hs] at hh
  exact hh

end ArtinMatthews
