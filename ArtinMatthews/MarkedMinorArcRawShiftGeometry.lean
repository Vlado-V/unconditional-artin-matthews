module

public import ArtinMatthews.MarkedMinorArcRawCleanShifts
public import ArtinMatthews.MarkedMinorArcActualCleanBlocks


set_option backward.privateInPublic true
@[expose] public section

/-! Literal first-good-state projection and the actual shared-line union of
two shifted position cells satisfy all geometry of the proved clean bound. -/
namespace ArtinMatthews
open Matrix

/-- The actual first-good-state endpoint projection, retaining all other
literal physical endpoint multipliers. -/
noncomputable def markedRawFirstGoodCutoff {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (χ : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) : ℂ := by
  classical
  exact if MarkedRawFirstGood r d₀ Y w s then χ s else 0

theorem markedRawFirstGoodCutoff_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (χ : MarkedRawState P M B Z → ℂ)
    (hχ : ∀ s, ‖χ s‖ ≤ 1) (s : MarkedRawState P M B Z) :
    ‖markedRawFirstGoodCutoff r d₀ Y w χ s‖ ≤ 1 := by
  classical
  unfold markedRawFirstGoodCutoff
  split_ifs
  · exact hχ s
  · simp

theorem markedRawFirstGoodCutoff_ne_zero {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (χ : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) (hs : markedRawFirstGoodCutoff r d₀ Y w χ s ≠ 0) :
    MarkedRawFirstGood r d₀ Y w s := by
  classical
  by_contra hn
  exact hs (by simp only [markedRawFirstGoodCutoff,ite_eq_right hn])

/-- The actual union of a source cell and its shifted target cell, in the
same literal projective line tuple. -/
noncomputable def markedRawShiftPositionSet {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (D : ℕ) (root : Z)
    (shift : ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact Z.filter fun v => ∃ hv : v ∈ Z,
    markedRawPositionLineTuple D root.1 (hZ _ root.2)=markedRawPositionLineTuple D v (hZ _ hv) ∧
      (markedMinorPositionCell r d₀ Y v=markedMinorPositionCell r d₀ Y root.1 ∨
        markedMinorPositionCell r d₀ Y v-markedMinorPositionCell r d₀ Y root.1=shift)

/-- Every actual point of the two-cell union lies on the required shared
prime lines, with no congruence assumption added to the block estimate. -/
theorem markedRawShiftPositionSet_lines {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (D : ℕ) (root : Z) (shift : ℤ)
    (v : ℤ × ℤ) (hv : v ∈ markedRawShiftPositionSet hZ r d₀ Y D root shift) :
    ∀ p ∈ D.primeFactors, MarkedMinorSamePrimeLine p root.1 v := by
  classical
  obtain ⟨_,hv',hline,_⟩ := Finset.mem_filter.mp hv
  intro p hp
  let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact (markedPrimePositionLine_eq_iff_same p _ _ (hZ _ root.2) (hZ _ hv')).mp (congrFun hline ⟨p,hp⟩)

/-- Every actual point of the shifted union lies within a constant multiple
of D*Y from the actual source root in the exact source ratio coordinate. -/
theorem markedRawShiftPositionSet_width {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r : ℝ) {d₀ Y : ℝ}
    (hd₀ : 0 < d₀) (hY : 0 < Y) (D : ℕ) (hdD : d₀ ≤ D) (root : Z) (shift : ℤ)
    (v : ℤ × ℤ) (hv : v ∈ markedRawShiftPositionSet hZ r d₀ Y D root shift) :
    |(v.2 : ℝ)/markedMinorIntegerTau r v-(root.1.2 : ℝ)/markedMinorIntegerTau r root.1| ≤
      (((|shift| : ℤ) : ℝ)+1)*D*Y := by
  classical
  obtain ⟨_,_,_,hc⟩ := Finset.mem_filter.mp hv
  have habs : (0 : ℝ) ≤ ((|shift| : ℤ) : ℝ) := by positivity
  rcases hc with hc|hc
  · have hh := markedMinorPositionCell_distance_of_shift r hd₀ hY root.1 v 0 (by omega)
    simp only [abs_zero,Int.cast_zero,zero_mul,zero_add] at hh
    calc
      _ ≤ d₀*Y := hh
      _ ≤ (D : ℝ)*Y := mul_le_mul_of_nonneg_right hdD hY.le
      _ ≤ (((|shift| : ℤ) : ℝ)+1)*D*Y := by
        nlinarith [mul_nonneg habs (mul_nonneg (Nat.cast_nonneg D) hY.le)]
  · have hh := markedMinorPositionCell_distance_of_shift r hd₀ hY root.1 v shift hc
    calc
      _ ≤ ((|shift| : ℤ) : ℝ)*(d₀*Y)+d₀*Y := hh
      _ ≤ (((|shift| : ℤ) : ℝ)+1)*D*Y := by
        nlinarith [mul_le_mul_of_nonneg_left hdD (mul_nonneg (by linarith : 0 ≤ ((|shift| : ℤ) : ℝ)+1) hY.le)]

/-- Literal actual cell data, including the true copied product and all
numeric last-label products. -/
noncomputable def markedRawCleanShiftCellData {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (w : Z → ℤ × ℤ)
    (bg : MarkedRawBackground P pads B) (root : Z) (shift : ℤ) : MarkedMinorCleanCellData :=
  ⟨markedRawCopiedProduct bg.1,
    markedRawShiftPositionSet hZ r d₀ Y (markedRawCopiedProduct bg.1) root shift,
    markedRawProductSupport P,root.1,w root⟩

/-- Nonzero actual first-good raw sources supply every hypothesis of the
proved clean geometric estimate on their literal shifted position union. -/
theorem markedRawCleanShiftCellGeometry {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (r : ℝ) {d₀ Y c L : ℝ} (hd₀ : 0 < d₀) (hY : 0 < Y)
    (w : Z → ℤ × ℤ) (hw : ∀ z, markedMinorIntegerDet z.1 (w z)=1)
    (hτ : ∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ L)
    (Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z) (shift : ℤ)
    (h : markedRawCleanKernel hZ ψ η d₀ Y Q ρ (markedRawFirstGoodCutoff r d₀ Y w χ) bg u v ≠ 0) :
    MarkedMinorCleanCellGeometry r Y c L (((|shift| : ℤ) : ℝ)+1)
      (markedRawCleanShiftCellData hZ r d₀ Y w bg u.1 shift) := by
  classical
  have hs := markedRawCleanKernel_ne_zero_support hZ ψ η d₀ Y Q ρ _ bg u v h
  have he := (markedRawCleanKernel_ne_zero_endpoint_factors hZ ψ η d₀ Y Q ρ _ bg u v h).1
  have hg := markedRawFirstGoodCutoff_ne_zero r d₀ Y w χ _
    (markedRawEndpointFactor_ne_zero_test hZ ρ _ _ he)
  have heactive : (markedRawActiveSplit pads)
      (((markedRawStateSplit pads B Z).symm (bg,u)).2.1)=(bg.1,u.2) := by
    change (markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm (bg.1,u.2))=_
    exact Equiv.apply_symm_apply _ _
  have hpad : d₀ ≤ (markedRawCopiedProduct
      ((markedRawActiveSplit pads) (((markedRawStateSplit pads B Z).symm (bg,u)).2.1)).1 : ℝ) ∧
      (markedRawCopiedProduct ((markedRawActiveSplit pads)
        (((markedRawStateSplit pads B Z).symm (bg,u)).2.1)).1 : ℝ) < 2*d₀ := by
    simpa only [heactive] using hs.1
  have hgood := markedRawFirstGood_clean_shear r d₀ Y w _ hg hpad
  rw [heactive] at hgood
  refine ⟨markedRawCopiedProduct_pos _,
    markedRawCleanKernel_ne_zero_squarefree hP hZ ψ η d₀ Y Q ρ _ bg u v h,
    hw u.1,hgood,(hτ _ u.1.2).1,(hτ _ u.1.2).2,?_,?_,?_⟩
  · intro z hz
    exact hτ z (Finset.mem_filter.mp hz).1
  · exact markedRawShiftPositionSet_lines hZ r d₀ Y _ u.1 shift
  · exact markedRawShiftPositionSet_width hZ r hd₀ hY _ hs.1.1 u.1 shift

end ArtinMatthews
