module

public import ArtinMatthews.MarkedPhysicalSlopeCells
public import ArtinMatthews.MarkedPhysicalEdgeKernelFormula


set_option backward.privateInPublic true
@[expose] public section

/-! The literal physical kernel has bounded overlap in the actual slope
partition. Its cutoff supplies the determinant bound; no sparsity or
neighbor-overlap hypothesis is substituted for that calculation. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedFloor_distance_le (x y : ℝ) :
    |((⌊x⌋ : ℤ) : ℝ)-((⌊y⌋ : ℤ) : ℝ)| ≤ |x-y|+1 := by
  have hx₁ := Int.floor_le x
  have hx₂ := Int.lt_floor_add_one x
  have hy₁ := Int.floor_le y
  have hy₂ := Int.lt_floor_add_one y
  rw [abs_le]
  constructor <;> linarith [le_abs_self (x-y),neg_le_abs (x-y)]

theorem markedPhysicalSlopeCell_bandwidth (p q : ℤ × ℤ)
    (U H K : ℝ) (hU : 0 < U) (hH : 0 < H) (hK : 0 ≤ K)
    (hp : U ≤ (p.1 : ℝ)) (hq : U ≤ (q.1 : ℝ))
    (hdet : |(markedMinorIntegerDet p q : ℝ)| ≤ K*H) :
    |((markedPhysicalSlopeCell (H/U^2) q : ℤ) : ℝ)-
      ((markedPhysicalSlopeCell (H/U^2) p : ℤ) : ℝ)| ≤ K+1 := by
  have hp₀ : (0 : ℝ) < p.1 := hU.trans_le hp
  have hq₀ : (0 : ℝ) < q.1 := hU.trans_le hq
  have hpz : p.1 ≠ 0 := by exact_mod_cast hp₀.ne'
  have hqz : q.1 ≠ 0 := by exact_mod_cast hq₀.ne'
  have hden : U^2 ≤ (p.1 : ℝ)*(q.1 : ℝ) := by
    nlinarith [mul_le_mul hp hq hU.le hp₀.le]
  have hw : 0 < H/U^2 := div_pos hH (sq_pos_of_pos hU)
  have hdif : |markedPhysicalSlope q-markedPhysicalSlope p| ≤ K*(H/U^2) := by
    rw [markedPhysicalSlope_difference p q hpz hqz,abs_div,abs_mul,
      abs_of_pos hp₀,abs_of_pos hq₀]
    calc
      _ ≤ (K*H)/((p.1 : ℝ)*(q.1 : ℝ)) :=
        div_le_div_of_nonneg_right hdet (mul_pos hp₀ hq₀).le
      _ ≤ (K*H)/U^2 := div_le_div_of_nonneg_left (mul_nonneg hK hH.le)
        (sq_pos_of_pos hU) hden
      _ = _ := by ring
  have hscaled : |markedPhysicalSlope q/(H/U^2)-markedPhysicalSlope p/(H/U^2)| ≤ K := by
    rw [← sub_div,abs_div,abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr hdif
  exact (markedFloor_distance_le _ _).trans (by linarith)

theorem markedPhysicalSlopeCell_shift_mem (p q : ℤ × ℤ)
    (U H K : ℝ) (hU : 0 < U) (hH : 0 < H) (hK : 0 ≤ K)
    (hp : U ≤ (p.1 : ℝ)) (hq : U ≤ (q.1 : ℝ))
    (hdet : |(markedMinorIntegerDet p q : ℝ)| ≤ K*H) :
    markedPhysicalSlopeCell (H/U^2) q-markedPhysicalSlopeCell (H/U^2) p ∈
      Finset.Icc (-(⌈K+1⌉₊ : ℤ)) (⌈K+1⌉₊ : ℤ) := by
  have h := markedPhysicalSlopeCell_bandwidth p q U H K hU hH hK hp hq hdet
  have hn : K+1 ≤ (⌈K+1⌉₊ : ℝ) := Nat.le_ceil _
  have hbounds := abs_le.mp (h.trans hn)
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hbounds.1,by exact_mod_cast hbounds.2⟩

theorem markedRawJoint_ne_zero_cutoff {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z)
    (h : markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t ≠ 0) :
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
    (d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀) ∧
      (D : ℤ) ∣ markedMinorIntegerDet s.1.1 t.1.1 ∧
      ψ (((markedMinorIntegerDet s.1.1 t.1.1/(D : ℤ) : ℤ) : ℝ)/Y) ≠ 0 := by
  dsimp only
  unfold markedRawEdgeJointCoefficient at h
  dsimp only at h
  split_ifs at h with hd hdiv hban
  · exact False.elim (h rfl)
  · refine ⟨hd,hdiv,?_⟩
    intro hz
    apply h
    simp only [hz,mul_zero,zero_mul]
  · exact False.elim (h rfl)
  · exact False.elim (h rfl)

theorem markedPhysicalEdgeCoefficient_det_bound {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K : ℝ)
    (hd₀ : 0 < d₀) (hY : 0 < Y) (hK : 0 ≤ K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (s t : MarkedPhysicalState P (pads+1) Z)
    (h : markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t ≠ 0) :
    |(markedMinorIntegerDet s.1.1.1 t.1.1.1 : ℝ)| ≤ 2*K*(d₀*Y) := by
  let u := markedPhysicalStateToRaw P hP (pads+1) Z s
  let v := markedPhysicalStateToRaw P hP (pads+1) Z t
  have hj : markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) u v ≠ 0 := by
    intro hz
    apply h
    change markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1)
      (markedPhysicalStateToRaw P hP (pads+1) Z s)
      (markedPhysicalStateToRaw P hP (pads+1) Z t) = 0 at hz
    simp only [markedPhysicalEdgeCoefficient,hz,mul_zero,zero_mul,ite_self]
  obtain ⟨hdyad,hdiv,hcut⟩ := markedRawJoint_ne_zero_cutoff hZ ψ η d₀ Y Q 1 (fun _ => 1) u v hj
  let D := markedRawCopiedProduct ((markedRawActiveSplit pads) u.2.1).1
  have hD : (0 : ℝ) < D := hd₀.trans_le hdyad.1
  have he : (((markedMinorIntegerDet u.1.1 v.1.1/(D : ℤ) : ℤ) : ℝ)) =
      (markedMinorIntegerDet u.1.1 v.1.1 : ℝ)/(D : ℝ) := by
    apply (eq_div_iff hD.ne').mpr
    norm_cast
    exact Int.ediv_mul_cancel hdiv
  have ha : |(((markedMinorIntegerDet u.1.1 v.1.1/(D : ℤ) : ℤ) : ℝ)/Y)| ≤ K :=
    abs_le.mpr (hψ hcut)
  rw [he,div_div,abs_div,abs_of_pos (mul_pos hD hY)] at ha
  have hb := (div_le_iff₀ (mul_pos hD hY)).mp ha
  change |(markedMinorIntegerDet u.1.1 v.1.1 : ℝ)| ≤ _
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hdyad.2.le (mul_nonneg hK hY.le)])

theorem markedPhysicalEdgeCoefficient_cell_shift {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U : ℝ)
    (hd₀ : 0 < d₀) (hY : 0 < Y) (hK : 0 ≤ K) (hU : 0 < U)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (hfirst : ∀ z ∈ Z, U ≤ (z.1 : ℝ))
    (s t : MarkedPhysicalState P (pads+1) Z)
    (h : markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t ≠ 0) :
    markedPhysicalSlopeCell ((d₀*Y)/U^2) t.1.1.1 -
      markedPhysicalSlopeCell ((d₀*Y)/U^2) s.1.1.1 ∈
        Finset.Icc (-(⌈2*K+1⌉₊ : ℤ)) (⌈2*K+1⌉₊ : ℤ) := by
  apply markedPhysicalSlopeCell_shift_mem _ _ U (d₀*Y) (2*K) hU
    (mul_pos hd₀ hY) (by positivity) (hfirst _ s.1.1.2) (hfirst _ t.1.1.2)
  exact markedPhysicalEdgeCoefficient_det_bound P hP V pads Z hZ ψ η d₀ Y Q q K
    hd₀ hY hK hψ s t h

end
end ArtinMatthews
