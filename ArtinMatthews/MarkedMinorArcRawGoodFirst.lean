module

public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedMinorArcDirtyOmission
public import ArtinMatthews.MarkedMinorArcPositionOperator


set_option backward.privateInPublic true
@[expose] public section

/-! The exact physical full-list first-good test, restricted to the source
pad dyad, implies the actual shear condition in the copied-prefix block. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Numeric source slots, retaining the actual prime values. -/
def markedRawNumericActive {J : Type*} {P : J → Finset Nat.Primes} {M : ℕ}
    (a : MarkedRawActive P M) (j : J) (k : Fin M) : ℕ := (a j k).1

noncomputable def markedRawCopiedProduct {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads : ℕ} (copied : MarkedRawActive P pads) : ℕ := ∏ j, ∏ k, (copied j k).1

noncomputable def markedRawLastProduct {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (last : (j : J) → ↥(P j)) : ℕ := ∏ j, (last j).1

theorem markedRawLastProduct_pos {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (last : (j : J) → ↥(P j)) : 0 < markedRawLastProduct last := by
  exact Finset.prod_pos (fun j _ => (last j).1.2.pos)

theorem markedRawCopiedProduct_pos {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads : ℕ} (copied : MarkedRawActive P pads) : 0 < markedRawCopiedProduct copied := by
  exact Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (copied j k).1.2.pos))

/-- Full product equals copied prefix times actual last-slot product. -/
theorem markedRawFullProduct_split {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (pads : ℕ) (a : MarkedRawActive P (pads+1)) :
    markedSourceFullProduct (markedRawNumericActive a)=
      markedRawCopiedProduct ((markedRawActiveSplit pads) a).1 *
      markedRawLastProduct ((markedRawActiveSplit pads) a).2 := by
  unfold markedSourceFullProduct markedRawCopiedProduct markedRawLastProduct markedRawNumericActive
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact Fin.prod_univ_castSucc (fun k => ((a j k).1 : ℕ))

/-- The copied slots in the unsymmetrized source rule are literally the
all-but-last omission product in the physical first-good test. -/
theorem markedRawCopiedProduct_eq_source {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (pads : ℕ) (a : MarkedRawActive P (pads+1)) :
    markedRawCopiedProduct ((markedRawActiveSplit pads) a).1 =
      markedSourceCopiedProduct (markedRawNumericActive a) (fun _ => Fin.last pads) := by
  apply mul_right_cancel₀ (markedRawLastProduct_pos ((markedRawActiveSplit pads) a).2).ne'
  calc
    _ = markedSourceFullProduct (markedRawNumericActive a) := (markedRawFullProduct_split pads a).symm
    _ = _ := (markedSourceCopied_mul_omitted (markedRawNumericActive a) (fun _ => Fin.last pads)).symm

/-- Exactly the omission tuples whose copied product lies in the source dyad. -/
noncomputable def markedRawDyadicOmissions {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ : ℝ) :
    Finset (J → Fin M) := by
  classical
  exact Finset.univ.filter (fun choice => d₀ ≤ (markedSourceCopiedProduct (markedRawNumericActive a) choice : ℝ) ∧
    (markedSourceCopiedProduct (markedRawNumericActive a) choice : ℝ) < 2*d₀)

/-- The literal first-good physical test, with the actual copied-product
dyad restriction retained. The complement may be any actual det-one choice. -/
def MarkedRawFirstGood {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (s : MarkedRawState P M B Z) : Prop :=
  ((markedMinorIntegerTau r (w s.1)/markedMinorIntegerTau r s.1.1 : ℝ) : AddCircle (1:ℝ)) ∉
    markedFirstBadRoots
      (fun choice : markedRawDyadicOmissions s.2.1 d₀ =>
        markedSourceCopiedProduct (markedRawNumericActive s.2.1) choice.1)
      ⌊Y^(1/5 : ℝ)⌋₊ (Y^(-7/10 : ℝ))

/-- Every actual good physical source in the copied-prefix dyad supplies
exactly the first-good shear hypothesis of the checked clean block. -/
theorem markedRawFirstGood_clean_shear {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (s : MarkedRawState P (pads+1) B Z)
    (hg : MarkedRawFirstGood r d₀ Y w s)
    (hpad : d₀ ≤ (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1 : ℝ) ∧
      (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1 : ℝ) < 2*d₀) :
    MarkedMinorShearGood
      ((markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1 : ℝ)*
        markedMinorIntegerTau r (w s.1)/markedMinorIntegerTau r s.1.1) Y := by
  classical
  have hchoice : (fun _ : J => Fin.last pads) ∈ markedRawDyadicOmissions s.2.1 d₀ := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rwa [← markedRawCopiedProduct_eq_source pads s.2.1]
  have hh := markedMinorPosition_shearGood_of_firstGood
    (fun choice : markedRawDyadicOmissions s.2.1 d₀ =>
      markedSourceCopiedProduct (markedRawNumericActive s.2.1) choice.1)
    ⟨(fun _ : J => Fin.last pads),hchoice⟩ r Y s.1.1 (w s.1) hg
  rwa [← markedRawCopiedProduct_eq_source pads s.2.1] at hh

end ArtinMatthews
