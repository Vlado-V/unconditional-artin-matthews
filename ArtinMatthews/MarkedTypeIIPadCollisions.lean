module

public import ArtinMatthews.MarkedEstimateVariance
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Collision probabilities for the ordered harmonic pads

These are finite product-law calculations for PD (pad-collisions). Equality
probabilities are derived from the actual independent product mass, and a
finite union bound controls repeated pads and forbidden labels.
-/

namespace ArtinMatthews

open scoped BigOperators

/-- The mass of an event under arbitrary finite real weights. -/
noncomputable def markedEventMass {X : Type*} [Fintype X]
    (w : X → ℝ) (E : X → Prop) : ℝ := by
  classical
  exact ∑ x, (if E x then (1 : ℝ) else 0) * w x

theorem markedEventMass_nonneg {X : Type*} [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (E : X → Prop) :
    0 ≤ markedEventMass w E := by
  classical
  apply Finset.sum_nonneg
  intro x _hx
  split_ifs <;> simp [hw x]

/-- A union bound for finite weighted events, with no probabilistic assumption. -/
theorem markedEventMass_exists_le {X I : Type*} [Fintype X] [Fintype I]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (E : I → X → Prop) :
    markedEventMass w (fun x => ∃ i, E i x) ≤
      ∑ i, markedEventMass w (E i) := by
  classical
  unfold markedEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _hx
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (hw x)
  by_cases h : ∃ i, E i x
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    calc
      (1 : ℝ) = if E i x then 1 else 0 := by simp [hi]
      _ ≤ ∑ j, if E j x then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j : I => if E j x then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

theorem markedEventMass_or_le {X : Type*} [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (E F : X → Prop) :
    markedEventMass w (fun x => E x ∨ F x) ≤ markedEventMass w E + markedEventMass w F := by
  classical
  unfold markedEventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _hx
  by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF, hw x]

theorem marked_iid_mass_nonneg {I Ω : Type*} [Fintype I]
    (μ : Ω → ℝ) (hμ : ∀ a, 0 ≤ μ a) (x : I → Ω) :
    0 ≤ finiteProductMass (fun _ : I => μ) x :=
  Finset.prod_nonneg (fun i _ => hμ (x i))

/-- The original atom is exactly the marginal probability of one iid pad. -/
theorem marked_iid_coordinate_atom {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ a, μ a = 1) (i : I) (a : Ω) :
    markedEventMass (finiteProductMass (fun _ : I => μ)) (fun x => x i = a) = μ a := by
  classical
  have h := finiteProduct_expectation_coordinate (fun _ : I => μ)
    (fun _ y => if y = a then (1 : ℝ) else 0) (fun _ => hμ) i
  simpa [markedEventMass] using h

/-- Exact factorization for two distinct iid coordinates. -/
theorem marked_iid_two_coordinates {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ a, μ a = 1)
    (f g : Ω → ℝ) {i j : I} (hij : i ≠ j) :
    (∑ x : I → Ω, (f (x i) * g (x j)) * finiteProductMass (fun _ : I => μ) x) =
      (∑ a, f a * μ a) * (∑ a, g a * μ a) := by
  classical
  let q : I → Ω → ℝ := fun k a =>
    (if k = i then f a else 1) * (if k = j then g a else 1)
  have hprod (x : I → Ω) : (∏ k, q k (x k)) = f (x i) * g (x j) := by
    dsimp only [q]
    rw [Finset.prod_mul_distrib]
    simp
  calc
    _ = ∑ x : I → Ω, (∏ k, q k (x k)) * finiteProductMass (fun _ : I => μ) x := by
      simp_rw [hprod]
    _ = ∏ k, ∑ a, q k a * μ a := finiteProduct_expectation_product _ _
    _ = ∏ k : I, (if k = i then (∑ a, f a * μ a) else 1) *
        (if k = j then (∑ a, g a * μ a) else 1) := by
      apply Finset.prod_congr rfl
      intro k _hk
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp_all [q]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- The equality event of two distinct iid pads has its exact second-moment mass. -/
theorem marked_iid_pair_equality {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ a, μ a = 1)
    {i j : I} (hij : i ≠ j) :
    markedEventMass (finiteProductMass (fun _ : I => μ)) (fun x => x i = x j) =
      ∑ a, μ a ^ 2 := by
  classical
  have hpoint (x : I → Ω) : (if x i = x j then (1 : ℝ) else 0) =
      ∑ a : Ω, (if x i = a then (1 : ℝ) else 0) *
        (if x j = a then (1 : ℝ) else 0) := by
    by_cases h : x i = x j <;> simp [mul_ite, h, eq_comm]
  unfold markedEventMass
  simp_rw [hpoint, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  have h := marked_iid_two_coordinates μ hμ
    (fun y => if y = a then (1 : ℝ) else 0)
    (fun y => if y = a then (1 : ℝ) else 0) hij
  simpa [pow_two] using h

theorem marked_iid_pair_equality_le {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (μ : Ω → ℝ) (hμ0 : ∀ a, 0 ≤ μ a) (hμ : ∑ a, μ a = 1)
    {δ : ℝ} (hδ : ∀ a, μ a ≤ δ) {i j : I} (hij : i ≠ j) :
    markedEventMass (finiteProductMass (fun _ : I => μ)) (fun x => x i = x j) ≤ δ := by
  rw [marked_iid_pair_equality μ hμ hij]
  calc
    (∑ a, μ a ^ 2) ≤ ∑ a, δ * μ a := by
      apply Finset.sum_le_sum
      intro a _ha
      simpa [pow_two] using mul_le_mul_of_nonneg_right (hδ a) (hμ0 a)
    _ = δ := by rw [← Finset.mul_sum, hμ, mul_one]

/-- The forbidden-label event has exactly the mass of the forbidden finite set. -/
theorem marked_iid_forbidden_mass {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [DecidableEq Ω] (μ : Ω → ℝ) (hμ : ∑ a, μ a = 1)
    (i : I) (F : Finset Ω) :
    markedEventMass (finiteProductMass (fun _ : I => μ)) (fun x => x i ∈ F) =
      ∑ a ∈ F, μ a := by
  classical
  have h := finiteProduct_expectation_coordinate (fun _ : I => μ)
    (fun _ y => if y ∈ F then (1 : ℝ) else 0) (fun _ => hμ) i
  simpa [markedEventMass, ite_mul] using h

/-- A bad ordered pad draw either repeats a label at distinct addresses or
hits one of the fixed forbidden labels. -/
def MarkedPadCollision {I Ω : Type*} (F : Finset Ω) (x : I → Ω) : Prop :=
  (∃ i j, i ≠ j ∧ x i = x j) ∨ ∃ i, x i ∈ F

/-- Finite iid pad-collision bound. The largest atom controls both a repeated
pair and a collision with any one forbidden label. -/
theorem marked_iid_pad_collision_bound {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (hμ0 : ∀ a, 0 ≤ μ a) (hμ : ∑ a, μ a = 1)
    (F : Finset Ω) {δ : ℝ} (hδ : ∀ a, μ a ≤ δ) :
    markedEventMass (finiteProductMass (fun _ : I => μ)) (MarkedPadCollision F) ≤
      ((Fintype.card I : ℝ) ^ 2 + (Fintype.card I : ℝ) * F.card) * δ := by
  classical
  have hne : Nonempty Ω := by
    by_contra h
    have : IsEmpty Ω := not_nonempty_iff.mp h
    simp at hμ
  obtain ⟨a₀⟩ := hne
  have hδ0 : 0 ≤ δ := (hμ0 a₀).trans (hδ a₀)
  let w : (I → Ω) → ℝ := finiteProductMass (fun _ : I => μ)
  have hw : ∀ x, 0 ≤ w x := marked_iid_mass_nonneg μ hμ0
  have hpair (i j : I) :
      markedEventMass w (fun x => i ≠ j ∧ x i = x j) ≤ δ := by
    by_cases hij : i = j
    · subst j
      simpa [markedEventMass] using hδ0
    · simpa [markedEventMass, w, hij] using
        (marked_iid_pair_equality_le μ hμ0 hμ hδ hij)
  have hpairs : markedEventMass w (fun x => ∃ i j, i ≠ j ∧ x i = x j) ≤
      (Fintype.card I : ℝ) ^ 2 * δ := by
    calc
      _ ≤ ∑ i : I, markedEventMass w (fun x => ∃ j, i ≠ j ∧ x i = x j) :=
        markedEventMass_exists_le w hw _
      _ ≤ ∑ i : I, ∑ j : I, markedEventMass w (fun x => i ≠ j ∧ x i = x j) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact markedEventMass_exists_le w hw _
      _ ≤ ∑ _i : I, ∑ _j : I, δ := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Finset.sum_le_sum (fun j _hj => hpair i j)
      _ = _ := by simp; ring
  have hforbidden (i : I) : markedEventMass w (fun x => x i ∈ F) ≤ (F.card : ℝ) * δ := by
    rw [marked_iid_forbidden_mass μ hμ i F]
    calc
      (∑ a ∈ F, μ a) ≤ ∑ _a ∈ F, δ := Finset.sum_le_sum (fun a _ha => hδ a)
      _ = _ := by simp
  have hforbiddenAll : markedEventMass w (fun x => ∃ i, x i ∈ F) ≤
      (Fintype.card I : ℝ) * F.card * δ := by
    calc
      _ ≤ ∑ i : I, markedEventMass w (fun x => x i ∈ F) :=
        markedEventMass_exists_le w hw _
      _ ≤ ∑ _i : I, (F.card : ℝ) * δ := Finset.sum_le_sum (fun i _hi => hforbidden i)
      _ = _ := by simp; ring
  calc
    _ ≤ markedEventMass w (fun x => ∃ i j, i ≠ j ∧ x i = x j) +
        markedEventMass w (fun x => ∃ i, x i ∈ F) :=
      markedEventMass_or_le w hw _ _
    _ ≤ (Fintype.card I : ℝ) ^ 2 * δ + (Fintype.card I : ℝ) * F.card * δ :=
      add_le_add hpairs hforbiddenAll
    _ = _ := by ring

/-- The concrete `M` ordered-pad version of the collision estimate. -/
theorem marked_fin_pad_collision_bound {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : ℕ) (μ : Ω → ℝ) (hμ0 : ∀ a, 0 ≤ μ a) (hμ : ∑ a, μ a = 1)
    (F : Finset Ω) {δ : ℝ} (hδ : ∀ a, μ a ≤ δ) :
    markedEventMass (finiteProductMass (fun _ : Fin M => μ)) (MarkedPadCollision F) ≤
      ((M : ℝ) ^ 2 + (M : ℝ) * F.card) * δ := by
  simpa using (marked_iid_pad_collision_bound (I := Fin M) μ hμ0 hμ F hδ)

/-- The actual harmonic atom of a finite prime band, using its reciprocal mass. -/
noncomputable def markedHarmonicAtom (P : Finset ℕ) (p : ↥P) : ℝ :=
  (1 / (p.1 : ℝ)) / bandReciprocalMass P

theorem markedHarmonicAtom_nonneg (P : Finset ℕ) {p : ↥P}
    (hV : 0 < bandReciprocalMass P) : 0 ≤ markedHarmonicAtom P p := by
  unfold markedHarmonicAtom
  positivity

/-- Harmonic atoms have exactly total mass one. -/
theorem markedHarmonicAtom_sum (P : Finset ℕ) (hV : 0 < bandReciprocalMass P) :
    ∑ p : ↥P, markedHarmonicAtom P p = 1 := by
  unfold markedHarmonicAtom
  rw [← Finset.sum_div]
  have hsum : (∑ p : ↥P, (1 / (p.1 : ℝ))) = bandReciprocalMass P := by
    exact Finset.sum_coe_sort P (fun p : ℕ => 1 / (p : ℝ))
  rw [hsum, div_self hV.ne']

/-- A lower bound for the labels gives the actual largest-atom bound. -/
theorem markedHarmonicAtom_le (P : Finset ℕ) (hV : 0 < bandReciprocalMass P)
    {y : ℝ} (hy : 0 < y) (hP : ∀ p ∈ P, y ≤ (p : ℝ)) (p : ↥P) :
    markedHarmonicAtom P p ≤ 1 / (y * bandReciprocalMass P) := by
  unfold markedHarmonicAtom
  rw [div_div]
  exact one_div_le_one_div_of_le (mul_pos hy hV)
    (mul_le_mul_of_nonneg_right (hP p.1 p.2) hV.le)

/-- Actual harmonic pad draws from a prime band satisfy the collision bound,
with the explicit `1 / (y V)` atom estimate. -/
theorem marked_harmonic_pad_collision_bound (P : Finset ℕ)
    (hV : 0 < bandReciprocalMass P) {y : ℝ} (hy : 0 < y)
    (hP : ∀ p ∈ P, y ≤ (p : ℝ)) (M : ℕ) (F : Finset ↥P) :
    markedEventMass (finiteProductMass (fun _ : Fin M => markedHarmonicAtom P))
        (MarkedPadCollision F) ≤
      ((M : ℝ) ^ 2 + (M : ℝ) * F.card) * (1 / (y * bandReciprocalMass P)) := by
  exact marked_fin_pad_collision_bound M (markedHarmonicAtom P)
    (fun _ => markedHarmonicAtom_nonneg P hV) (markedHarmonicAtom_sum P hV) F
    (markedHarmonicAtom_le P hV hy hP)

end ArtinMatthews
