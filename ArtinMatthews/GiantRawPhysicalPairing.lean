module

public import ArtinMatthews.GiantRawPhysicalPattern
public import ArtinMatthews.GiantTwoSidedPhysicalPairing
public import ArtinMatthews.MarkedFiniteCells
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The raw edge sum, expressed on the actual two independently averaged slot lists. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Both slot permutations act before the root weight is evaluated. -/
def giantTwoSidedRawSlotEntry {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    {k m : ℕ} {Z Z' : Finset ℕ} (q ζ : ℝ) (χ : DirichletCharacter ℂ m) (R : ℕ → ℕ → ℂ)
    (s : GiantTwoSidedEndpointState P (k+1) Z) (t : GiantTwoSidedEndpointState P (k+1) Z') : ℂ :=
  (giantTwoSidedResidueSlotNormalization (J := J) (k+1) : ℂ) *
    ∑ π : J → Equiv.Perm (Fin (k+1)), ∑ τ : J → Equiv.Perm (Fin (k+1)),
      giantTwoSidedRawPatternEntry q ζ χ R (giantTwoSidedEndpointPermute π s)
        (giantTwoSidedEndpointPermute τ t)

private theorem sum_gated_eq_univ {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (f : ι → ℂ) (hf : ∀ i, ¬p i → f i = 0) :
    (∑ i : {i // p i}, f i.val) = ∑ i, f i := by
  calc
    _ = ∑ i ∈ Finset.univ.filter p, f i :=
      (Finset.sum_subtype _ (fun _ => Finset.mem_filter.trans (by simp)) f).symm
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : p i
      · exact ite_eq_left h
      · rw [ite_eq_right h, hf i h]

private theorem slot_normalization_complex (J : Type*) [Fintype J] [DecidableEq J] (M : ℕ) :
    (giantTwoSidedResidueSlotNormalization (J := J) M : ℂ) =
      ((Fintype.card (J → Equiv.Perm (Fin M)) : ℂ)^2)⁻¹ := by
  simp only [giantTwoSidedResidueSlotNormalization, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_natCast]

theorem giantTwoSidedRawPhysical_sum_eq_slots {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k m : ℕ} {Z Z' : Finset ℕ}
    (x q : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G L : ℕ → ℂ) :
    (∑ e : GiantTwoSidedRawPhysicalEdge P k Z Z',
      L e.val.1.val.1.val * giantTwoSidedRawPhysicalTerm x q Ψ χ F G e) =
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+1) : ℂ) *
        ∑ s : GiantTwoSidedEndpointState P (k+1) Z,
          ∑ t : GiantTwoSidedEndpointState P (k+1) Z',
            giantTwoSidedRawSlotEntry q 0 χ
                (fun n D => Ψ ((n : ℝ)/(x*(D : ℝ)))/(n : ℂ)) s t *
              star (giantTwoSidedRawPairLeft P k q F L s.val.1.val) *
              giantTwoSidedRawPairRight P k q χ G t.val.1.val := by
  classical
  let Left := GiantTwoSidedEndpointState P (k+1) Z
  let Right := GiantTwoSidedEndpointState P (k+1) Z'
  let Permutations := J → Equiv.Perm (Fin (k+1))
  let σ : ℂ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+1)
  let a : ℂ := giantTwoSidedResidueSlotNormalization (J := J) (k+1)
  let R (n D : ℕ) := Ψ ((n : ℝ)/(x*(D : ℝ)))/(n : ℂ)
  let f (s : Left) := giantTwoSidedRawPairLeft P k q F L s.val.1.val
  let g (t : Right) := giantTwoSidedRawPairRight P k q χ G t.val.1.val
  let W (e : GiantTwoSidedRawPhysicalEdge P k Z Z') :=
    L e.val.1.val.1.val * giantTwoSidedRawPhysicalTerm x q Ψ χ F G e
  let V (π τ : Permutations) (s : Left) (t : Right) :=
    giantTwoSidedRawPatternEntry q 0 χ R
      (giantTwoSidedEndpointPermute π s) (giantTwoSidedEndpointPermute τ t) * star (f s) * g t
  have hfixed (π τ : Permutations) :
      (∑ e : GiantTwoSidedRawPermutedEdge P k Z Z' π τ, W (giantTwoSidedRawPermutedEquiv π τ e)) =
        σ * ∑ s : Left, ∑ t : Right, V π τ s t := by
    let IsEdge (p : Left × Right) :=
      GiantTwoSidedRawPhysicalCondition (giantTwoSidedEndpointPermute π p.1)
        (giantTwoSidedEndpointPermute τ p.2)
    let v (p : Left × Right) := V π τ p.1 p.2
    have hv0 (p : Left × Right) (hp : ¬IsEdge p) : v p = 0 := by
      dsimp only [v, V]
      rw [giantTwoSidedRawPatternEntry_zero q 0 χ R _ _ hp, zero_mul, zero_mul]
    calc
      _ = σ * ∑ e : {p // IsEdge p}, v e.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        have h := giantTwoSidedRawPhysicalTerm_eq_pattern_pairing x q Ψ χ F G L
          (giantTwoSidedRawPermutedEquiv π τ e)
        change W (giantTwoSidedRawPermutedEquiv π τ e) =
          σ * giantTwoSidedRawPatternEntry q 0 χ R
            (giantTwoSidedEndpointPermute π e.val.1) (giantTwoSidedEndpointPermute τ e.val.2) *
            star (f e.val.1) * g e.val.2 at h
        change W (giantTwoSidedRawPermutedEquiv π τ e) = σ * V π τ e.val.1 e.val.2
        simpa only [V, mul_assoc] using h
      _ = _ := by
        rw [sum_gated_eq_univ IsEdge v hv0, Fintype.sum_prod_type]
  have hsum :
      (∑ π : Permutations, ∑ τ : Permutations, ∑ s : Left, ∑ t : Right, V π τ s t) =
        ∑ s : Left, ∑ t : Right, ∑ π : Permutations, ∑ τ : Permutations, V π τ s t := by
    calc
      _ = ∑ p : Permutations × Permutations, ∑ z : Left × Right, V p.1 p.2 z.1 z.2 := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ z : Left × Right, ∑ p : Permutations × Permutations, V p.1 p.2 z.1 z.2 :=
        Finset.sum_comm
      _ = _ := by simp only [Fintype.sum_prod_type]
  change (∑ e, W e) = σ * ∑ s : Left, ∑ t : Right,
    giantTwoSidedRawSlotEntry q 0 χ R s t * star (f s) * g t
  calc
    _ = giantTwoSidedRawPermutationAverage W := (giantTwoSidedRawPermutationAverage_eq W).symm
    _ = a * ∑ π : Permutations, ∑ τ : Permutations,
          ∑ e : GiantTwoSidedRawPermutedEdge P k Z Z' π τ, W (giantTwoSidedRawPermutedEquiv π τ e) := by
      rw [show a = _ from slot_normalization_complex J (k+1)]
      rfl
    _ = a * (σ * ∑ π : Permutations, ∑ τ : Permutations, ∑ s : Left, ∑ t : Right, V π τ s t) := by
      simp only [hfixed, Finset.mul_sum]
    _ = _ := by
      rw [hsum]
      simp only [giantTwoSidedRawSlotEntry, Finset.mul_sum, Finset.sum_mul, V]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro π _
      apply Finset.sum_congr rfl
      intro τ _
      ring

theorem giantTwoSidedRawPhysical_sum_eq_weightedPairing {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k m : ℕ} {Z : Finset ℕ}
    (x q : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G L : ℕ → ℂ) :
    (∑ e : GiantTwoSidedRawPhysicalEdge P k Z Z,
      L e.val.1.val.1.val * giantTwoSidedRawPhysicalTerm x q Ψ χ F G e) =
      giantTwoSidedPhysicalWeightedPairing (P := P) (M := k+1) (Z := Z)
        (Matrix.of (fun s t => giantTwoSidedRawSlotEntry q 0 χ
          (fun n D => Ψ ((n : ℝ)/(x*(D : ℝ)))/(n : ℂ)) s t))
        (fun s => giantTwoSidedRawPairLeft P k q F L s.val.1.val)
        (fun t => giantTwoSidedRawPairRight P k q χ G t.val.1.val) := by
  rw [giantTwoSidedRawPhysical_sum_eq_slots]
  unfold giantTwoSidedPhysicalWeightedPairing
  simp only [markedMatrixPairing_expansion, Matrix.of_apply]

end
end ArtinMatthews
