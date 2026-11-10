module

public import ArtinMatthews.MarkedMinorArcRawShiftTransport
public import ArtinMatthews.MarkedMinorArcRawCleanShifts
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal row/column fibers of the actual root-line and position-cell key,
and their injections into the actual two-cell union. No operator norm is
postulated by the partition or the transport. -/
namespace ArtinMatthews

/-- Actual key translation for a fixed source-to-target cell shift. -/
def markedRawShiftKey {D : ℕ} (shift : ℤ) (key : MarkedRootLineTuple D × ℤ) :
    MarkedRootLineTuple D × ℤ := (key.1,key.2+shift)

theorem markedRawShiftKey_injective (D : ℕ) (shift : ℤ) :
    Function.Injective (markedRawShiftKey (D := D) shift) := by
  intro a b hab
  change (a.1,a.2+shift)=(b.1,b.2+shift) at hab
  have hh := Prod.mk.inj hab
  exact Prod.ext hh.1 (add_right_cancel hh.2)

/-- Actual finite raw fiber belonging to one projective line and position cell. -/
abbrev MarkedRawPositionClass {J : Type*} [Fintype J] (P : J → Finset Nat.Primes)
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (r d₀ Y : ℝ) (D : ℕ) (key : MarkedRootLineTuple D × ℤ) :=
  {u : MarkedRawCleanFiber P Z // markedRawPositionKey hZ r d₀ Y D u.1=key}

/-- Literal inclusion of a source class into its actual shifted-cell union. -/
noncomputable def markedRawClassRowIntoUnion {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (D : ℕ)
    (key : MarkedRootLineTuple D × ℤ) (root : MarkedRawPositionClass P hZ r d₀ Y D key) (shift : ℤ)
    (u : MarkedRawPositionClass P hZ r d₀ Y D key) :
    MarkedRawCleanFiber P (markedRawShiftPositionSet hZ r d₀ Y D root.1.1 shift) := by
  classical
  refine (⟨u.1.1.1,Finset.mem_filter.mpr ⟨u.1.1.2,⟨u.1.1.2,?_,Or.inl ?_⟩⟩⟩,u.1.2)
  · exact congrArg Prod.fst (root.2.trans u.2.symm)
  · exact congrArg Prod.snd (u.2.trans root.2.symm)

/-- Literal inclusion of the translated target class into the same actual
shifted-cell union, retaining every actual last prime. -/
noncomputable def markedRawClassColIntoUnion {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (D : ℕ)
    (key : MarkedRootLineTuple D × ℤ) (root : MarkedRawPositionClass P hZ r d₀ Y D key) (shift : ℤ)
    (v : MarkedRawPositionClass P hZ r d₀ Y D (markedRawShiftKey shift key)) :
    MarkedRawCleanFiber P (markedRawShiftPositionSet hZ r d₀ Y D root.1.1 shift) := by
  classical
  refine (⟨v.1.1.1,Finset.mem_filter.mpr ⟨v.1.1.2,⟨v.1.1.2,?_,Or.inr ?_⟩⟩⟩,v.1.2)
  · have hr := congrArg Prod.fst root.2
    have hv := congrArg Prod.fst v.2
    exact hr.trans hv.symm
  · have hr := congrArg Prod.snd root.2
    have hv := congrArg Prod.snd v.2
    change markedMinorPositionCell r d₀ Y v.1.1.1=key.2+shift at hv
    change markedMinorPositionCell r d₀ Y root.1.1.1=key.2 at hr
    omega

theorem markedRawClassRowIntoUnion_injective {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (D : ℕ)
    (key : MarkedRootLineTuple D × ℤ) (root : MarkedRawPositionClass P hZ r d₀ Y D key) (shift : ℤ) :
    Function.Injective (markedRawClassRowIntoUnion hZ r d₀ Y D key root shift) := by
  intro u v huv
  apply Subtype.ext
  have hh := congrArg (markedRawShiftFiberInclude hZ r d₀ Y D root.1.1 shift) huv
  exact hh

theorem markedRawClassColIntoUnion_injective {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (D : ℕ)
    (key : MarkedRootLineTuple D × ℤ) (root : MarkedRawPositionClass P hZ r d₀ Y D key) (shift : ℤ) :
    Function.Injective (markedRawClassColIntoUnion hZ r d₀ Y D key root shift) := by
  intro u v huv
  apply Subtype.ext
  have hh := congrArg (markedRawShiftFiberInclude hZ r d₀ Y D root.1.1 shift) huv
  exact hh

/-- The actual shifted kernel equals the actual unrestricted raw kernel on
every one of its literal rectangular class blocks. -/
theorem markedRawCleanShiftKernel_class_apply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (r d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (bg : MarkedRawBackground P pads B) (shift : ℤ)
    (key : MarkedRootLineTuple (markedRawCopiedProduct bg.1) × ℤ)
    (u : MarkedRawPositionClass P hZ r d₀ Y (markedRawCopiedProduct bg.1) key)
    (v : MarkedRawPositionClass P hZ r d₀ Y (markedRawCopiedProduct bg.1) (markedRawShiftKey shift key)) :
    markedRawCleanShiftKernel hZ ψ η r d₀ Y Q ρ χ bg shift u.1 v.1=
      markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg u.1 v.1 := by
  classical
  apply ite_eq_left
  constructor
  · exact (congrArg Prod.fst u.2).trans (congrArg Prod.fst v.2).symm
  · have hu := congrArg Prod.snd u.2
    have hv := congrArg Prod.snd v.2
    change markedMinorPositionCell r d₀ Y u.1.1.1=key.2 at hu
    change markedMinorPositionCell r d₀ Y v.1.1.1=key.2+shift at hv
    omega

/-- Genuine actual counting conjugate of one literal full-fiber cell shift. -/
noncomputable def markedRawCleanShiftCountingMatrix {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (ν : (j : J) → ↥(P j) → ℝ) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (bg : MarkedRawBackground P pads B) (shift : ℤ) :=
  markedWeightedCountingMatrix (fun u : MarkedRawCleanFiber P Z => markedRawLastMass ν u.2)
    (markedRawCleanShiftKernel hZ ψ η r d₀ Y Q ρ χ bg shift)

/-- Exact identification of an actual rectangular class block with the
corresponding restriction of the proved two-cell-union counting matrix. -/
theorem markedRawCleanShiftCountingMatrix_class_block {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (ν : (j : J) → ↥(P j) → ℝ) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (bg : MarkedRawBackground P pads B) (shift : ℤ)
    (key : MarkedRootLineTuple (markedRawCopiedProduct bg.1) × ℤ)
    (root : MarkedRawPositionClass P hZ r d₀ Y (markedRawCopiedProduct bg.1) key) :
    (markedRawCleanShiftCountingMatrix ν hZ ψ η r d₀ Y Q ρ χ bg shift).submatrix
      (fun u : MarkedRawPositionClass P hZ r d₀ Y (markedRawCopiedProduct bg.1) key => u.1)
      (fun v : MarkedRawPositionClass P hZ r d₀ Y (markedRawCopiedProduct bg.1) (markedRawShiftKey shift key) => v.1)=
    (markedRawShiftCountingMatrix ν hZ ψ η r d₀ Y Q ρ χ bg root.1.1 shift).submatrix
      (markedRawClassRowIntoUnion hZ r d₀ Y _ key root shift)
      (markedRawClassColIntoUnion hZ r d₀ Y _ key root shift) := by
  ext u v
  change (Real.sqrt (markedRawLastMass ν u.1.2) : ℂ)*
      markedRawCleanShiftKernel hZ ψ η r d₀ Y Q ρ χ bg shift u.1 v.1*
      (Real.sqrt (markedRawLastMass ν v.1.2) : ℂ)=_
  rw [markedRawCleanShiftKernel_class_apply]
  rfl

/-- The literal counting-conjugated shift has no off-translation entries. -/
theorem markedRawCleanShiftCountingMatrix_off_key {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (ν : (j : J) → ↥(P j) → ℝ) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (bg : MarkedRawBackground P pads B) (shift : ℤ)
    (u v : MarkedRawCleanFiber P Z)
    (hk : markedRawPositionKey hZ r d₀ Y (markedRawCopiedProduct bg.1) v.1 ≠
      markedRawShiftKey shift (markedRawPositionKey hZ r d₀ Y (markedRawCopiedProduct bg.1) u.1)) :
    markedRawCleanShiftCountingMatrix ν hZ ψ η r d₀ Y Q ρ χ bg shift u v=0 := by
  classical
  unfold markedRawCleanShiftCountingMatrix markedWeightedCountingMatrix markedRawCleanShiftKernel
  split_ifs with hh
  · exfalso
    apply hk
    apply Prod.ext
    · exact hh.1.symm
    · change markedMinorPositionCell r d₀ Y v.1.1=markedMinorPositionCell r d₀ Y u.1.1+shift
      omega
  · simp only [mul_zero,zero_mul]

end ArtinMatthews
