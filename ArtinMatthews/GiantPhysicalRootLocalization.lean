module

public import ArtinMatthews.GiantTwoSidedPhysicalMellinPairing
public import ArtinMatthews.GiantTwoSidedRootMargin
public import ArtinMatthews.GiantRawPhysicalSquare
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.Interval.Finset.Box
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

/-! The actual cutoff pairing is local to the enlarged moment slice when
its root is in the dyad and every displacement fits inside the margin. -/

namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

variable {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell : ℕ} {Z W : Finset ℕ}

private theorem physical_cutoff_restrict (hW : W ⊆ Z)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (Ψ : ℝ → ℂ) (x : ℝ)
    (f g : ℕ → ℂ)
    (hf : ∀ r ∈ Z, r ∉ W → f r = 0)
    (ht : ∀ (c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell)
      (s t : GiantTwoSidedEndpointState P (k+ell) Z), t.val.1.val ∉ W →
      f s.val.1.val = 0 ∨ giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t = 0 ∨
        g t.val.1.val = 0) :
    giantTwoSidedPhysicalCutoffPairing (Z := Z) patterns C step q ζ K Ψ x f
        (fun t => g t.val.1.val) =
      giantTwoSidedPhysicalCutoffPairing (Z := W) patterns C step q ζ K Ψ x f
        (fun t => g t.val.1.val) := by
  classical
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let Small := GiantTwoSidedEndpointState P (k+ell) W
  let Choice := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell
  let e := giantTwoSidedEndpointInclusion (P := P) (M := k+ell) hW
  let v (c : Choice) (s t : State) : ℂ :=
    giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t *
      (Ψ ((s.val.1.val : ℝ) / (x * (giantTwoSidedPhysicalChoiceDilation c s : ℝ))) /
        (s.val.1.val : ℂ)) * star (f s.val.1.val) * g t.val.1.val
  have hleft (c : Choice) (s : State) (hs : s.val.1.val ∉ W) : (∑ t : State, v c s t) = 0 := by
    simp only [v, hf _ s.val.1.property hs, star_zero, mul_zero, zero_mul, Finset.sum_const_zero]
  have hright (c : Choice) (s t : State) (h : t.val.1.val ∉ W) : v c s t = 0 := by
    rcases ht c s t h with h | h | h
    · simp only [v, h, star_zero, mul_zero, zero_mul]
    · simp only [v, h, zero_mul]
    · simp only [v, h, mul_zero]
  unfold giantTwoSidedPhysicalCutoffPairing
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  change (∑ s : State, ∑ t : State, v c s t) = _
  calc
    _ = ∑ s : Small, ∑ t : State, v c (e s) t :=
      giantTwoSidedEndpoint_sum_of_position_support hW _ (hleft c)
    _ = ∑ s : Small, ∑ t : Small, v c (e s) (e t) := by
      apply Finset.sum_congr rfl
      intro s _
      exact giantTwoSidedEndpoint_sum_of_position_support hW _ (hright c (e s))
    _ = _ := rfl

/-- Both endpoint masks retain the original finite box when the moment slice
extends beyond it. The shift bound applies to each actual choice of slots and
auxiliary labels. -/
theorem giantTwoSidedPhysicalCutoffPairing_eq_rootSlice {X : ℝ} (hX : 0 < X)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (Ψ : ℝ → ℂ) (x : ℝ)
    (f g : ℕ → ℂ) (hf : ∀ r ∉ giantTwoSidedRootInterval X, f r = 0)
    (hshift : ∀ (c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell)
      (s : GiantTwoSidedEndpointState P (k+ell) Z),
      |(step : ℝ) * (giantTwoSidedPhysicalChoiceDilation c s : ℝ)| ≤ X/2) :
    giantTwoSidedPhysicalCutoffPairing (Z := Z) patterns C step q ζ K Ψ x f
        (fun t => g t.val.1.val) =
      giantTwoSidedPhysicalCutoffPairing (Z := giantTwoSidedRootSlice X) patterns C step q ζ K Ψ x
        (fun r => if r ∈ Z then f r else 0)
        (fun t => if t.val.1.val ∈ Z then g t.val.1.val else 0) := by
  classical
  let S := giantTwoSidedRootSlice X
  let W := Z ∩ S
  let fZ (r : ℕ) := if r ∈ Z then f r else 0
  let gZ (r : ℕ) := if r ∈ Z then g r else 0
  have hsource (r : ℕ) (hr : r ∈ giantTwoSidedRootInterval X) : r ∈ S := by
    have hzero : |((0 : ℤ) : ℝ)| ≤ X/2 := by simp only [Int.cast_zero, abs_zero]; positivity
    have h := (giantTwoSidedRootInterval_translate hX hr hzero).2
    simpa only [Int.add_zero, Int.toNat_natCast] using h
  calc
    _ = giantTwoSidedPhysicalCutoffPairing (Z := W) patterns C step q ζ K Ψ x f
        (fun t => g t.val.1.val) := by
      apply physical_cutoff_restrict (inter_subset_left : W ⊆ Z)
      · intro r hr hrW
        apply hf r
        intro hrR
        exact hrW (mem_inter.mpr ⟨hr, hsource r hrR⟩)
      · intro c s t htW
        by_cases hr : s.val.1.val ∈ giantTwoSidedRootInterval X
        · right
          left
          unfold giantTwoSidedPhysicalChoiceCoefficient giantTwoSidedPatternPhysicalCoefficient
          apply ite_eq_right
          intro hgate
          have hδ : |((step * (giantTwoSidedPhysicalChoiceDilation c s : ℤ) : ℤ) : ℝ)| ≤ X/2 := by
            simpa only [Int.cast_mul, Int.cast_natCast] using hshift c s
          have hm := (giantTwoSidedRootInterval_translate hX hr hδ).2
          have ht : (t.val.1.val : ℤ) = (s.val.1.val : ℤ) +
              step * (giantTwoSidedPhysicalChoiceDilation c s : ℤ) := hgate.2.1
          rw [← ht, Int.toNat_natCast] at hm
          exact htW (mem_inter.mpr ⟨t.val.1.property, hm⟩)
        · exact Or.inl (hf _ hr)
    _ = giantTwoSidedPhysicalCutoffPairing (Z := W) patterns C step q ζ K Ψ x fZ
        (fun t => gZ t.val.1.val) := by
      unfold giantTwoSidedPhysicalCutoffPairing
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      simp only [fZ, gZ, ite_eq_left (mem_inter.mp s.val.1.property).1,
        ite_eq_left (mem_inter.mp t.val.1.property).1]
    _ = _ := by
      symm
      change giantTwoSidedPhysicalCutoffPairing (Z := S) patterns C step q ζ K Ψ x fZ
          (fun t => gZ t.val.1.val) =
        giantTwoSidedPhysicalCutoffPairing (Z := W) patterns C step q ζ K Ψ x fZ
          (fun t => gZ t.val.1.val)
      refine physical_cutoff_restrict (inter_subset_right : W ⊆ S) patterns C step q ζ K Ψ x fZ gZ ?_ ?_
      · intro r hr hrW
        have h : r ∉ Z := fun hz => hrW (mem_inter.mpr ⟨hz, hr⟩)
        exact ite_eq_right h
      · intro c s t ht
        have h : t.val.1.val ∉ Z := fun hz => ht (mem_inter.mpr ⟨hz, t.val.1.property⟩)
        exact Or.inr (Or.inr (ite_eq_right h))

/-- For the actual selected groups, step one has the required displacement
bound uniformly in the choice of pattern, auxiliary labels and slots. -/
theorem giantCandidatePhysicalCutoffPairing_eventually_eq_rootSlice (k : ℕ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ x : ℝ in atTop, ∀ groups : Finset (GiantCandidateGroupIndex x),
      let P := fun j : ↥groups => giantCandidateGroup x j.val
      ∀ (I : Type u) (patterns : Finset I) (C : I → ↥groups → Finset (Fin k))
        (ell : ℕ) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
        (q ζ : ℝ) (Ψ : ℝ → ℂ) (Z : Finset ℕ) (X : ℝ), x^τ ≤ X →
      ∀ (f g : ℕ → ℂ), (∀ r ∉ giantTwoSidedRootInterval X, f r = 0) →
        giantTwoSidedPhysicalCutoffPairing (Z := Z) patterns C 1 q ζ K Ψ x f
          (fun t => g t.val.1.val) =
        giantTwoSidedPhysicalCutoffPairing (Z := giantTwoSidedRootSlice X) patterns C 1 q ζ K Ψ x
          (fun r => if r ∈ Z then f r else 0)
          (fun t => if t.val.1.val ∈ Z then g t.val.1.val else 0) := by
  filter_upwards [giantCandidatePatternDilation_subpower k (half_pos hτ),
    eventually_gt_atTop (0 : ℝ),
    (tendsto_rpow_atTop (half_pos hτ)).eventually_ge_atTop (2 : ℝ)] with x hD hx h2
  intro groups P I patterns C ell K q ζ Ψ Z X hX f g hf
  have hX0 : 0 < X := (Real.rpow_pos_of_pos hx τ).trans_le hX
  have hsquare : x^τ = (x^(τ/2))^2 := by
    rw [sq, ← Real.rpow_add hx]
    congr 1
    ring
  have hmargin : x^(τ/2) ≤ X/2 := by
    rw [hsquare] at hX
    nlinarith only [hX, mul_le_mul_of_nonneg_right h2 (zero_le_two.trans h2)]
  apply giantTwoSidedPhysicalCutoffPairing_eq_rootSlice hX0 patterns C 1 q ζ K Ψ x f g hf
  intro c s
  rw [Int.cast_one, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact (hD groups ell (C c.1.val) (giantTwoSidedEndpointPermute c.2.1 s).val.2 c.2.2.2).trans hmargin

end
end ArtinMatthews
