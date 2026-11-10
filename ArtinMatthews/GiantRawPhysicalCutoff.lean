module

public import ArtinMatthews.GiantTwoSidedPhysicalResidualExpansion
public import ArtinMatthews.GiantRawPhysicalPairing
public import ArtinMatthews.GiantRawPhysicalSquare
public import ArtinMatthews.MarkedFiniteCells
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

/-! The exact raw pairing is the empty member of the cutoff family. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem raw_empty_auxiliary_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k : ℕ}
    (f : GiantTwoSidedPatternAuxiliary P (giantTwoSidedRawEmptyPattern J k) → ℂ) :
    (∑ aux, f aux) = f (giantTwoSidedRawEmptyAuxiliary P k) := by
  apply Fintype.sum_eq_single (giantTwoSidedRawEmptyAuxiliary P k)
  intro aux haux
  exfalso
  apply haux
  funext j i
  exact (Finset.notMem_empty _ i.property).elim

private theorem raw_empty_dilation {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
    (a : MarkedPhysicalMarking P (k+1))
    (aux : GiantTwoSidedPatternAuxiliary P (giantTwoSidedRawEmptyPattern J k)) :
    giantTwoSidedPatternDilation (giantTwoSidedRawEmptyPattern J k) a aux =
      giantTwoSidedRawPrefixProduct a := by
  simp [giantTwoSidedPatternDilation, giantTwoSidedRaw_copiedProduct,
    giantTwoSidedPatternAuxiliaryProduct]

theorem giantTwoSidedRawSlotEntry_unit_eq_familyMatrix {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k m : ℕ} {Z : Finset ℕ} (q ζ : ℝ) (χ : DirichletCharacter ℂ m)
    (s t : GiantTwoSidedEndpointState P (k+1) Z) :
    giantTwoSidedRawSlotEntry q ζ χ (fun _ _ => 1) s t =
      giantTwoSidedPhysicalFamilyMatrix (P := P) (Z := Z) ({()} : Finset Unit)
        (fun _ => giantTwoSidedRawEmptyPattern J k) 1 q ζ
        (fun _ => giantTwoSidedRawPatternCoefficient χ) s t := by
  unfold giantTwoSidedRawSlotEntry giantTwoSidedPhysicalFamilyMatrix
  congr 1
  rw [Fintype.sum_sigma]
  let p : ↥({()} : Finset Unit) := ⟨(), Finset.mem_singleton_self ()⟩
  have hsingle (f : ↥({()} : Finset Unit) → ℂ) : (∑ i, f i) = f p :=
    Fintype.sum_eq_single p (fun i hi => (hi (Subtype.ext (Subsingleton.elim i.val p.val))).elim)
  rw [hsingle]
  simp only [Fintype.sum_prod_type, giantTwoSidedPhysicalChoiceCoefficient, raw_empty_auxiliary_sum,
    giantTwoSidedRawPatternEntry, one_mul]

theorem giantTwoSidedRawPhysical_sum_eq_patternCutoffPairing {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k m : ℕ} {Z Z' U : Finset ℕ} (hZ : Z ⊆ U) (hZ' : Z' ⊆ U)
    (x q : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G L : ℕ → ℂ) :
    (∑ e : GiantTwoSidedRawPhysicalEdge P k Z Z',
      L e.val.1.val.1.val * giantTwoSidedRawPhysicalTerm x q Ψ χ F G e) =
      giantTwoSidedPhysicalPatternCutoffPairing (P := P) (Z := U) (giantTwoSidedRawEmptyPattern J k)
        1 q 0 (giantTwoSidedRawPatternCoefficient χ) Ψ x
        (fun n => if n ∈ Z then giantTwoSidedRawPairLeft P k q F L n else 0)
        (fun t => if t.val.1.val ∈ Z' then giantTwoSidedRawPairRight P k q χ G t.val.1.val else 0) := by
  classical
  rw [giantTwoSidedRawPhysical_sum_eq_slicePairing hZ hZ']
  let State := GiantTwoSidedEndpointState P (k+1) U
  let Perms := J → Equiv.Perm (Fin (k+1))
  let σ : ℂ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+1)
  let a : ℂ := giantTwoSidedResidueSlotNormalization (J := J) (k+1)
  let R (n D : ℕ) := Ψ ((n : ℝ) / (x * (D : ℝ))) / (n : ℂ)
  let f (n : ℕ) := if n ∈ Z then giantTwoSidedRawPairLeft P k q F L n else 0
  let g (t : State) := if t.val.1.val ∈ Z' then giantTwoSidedRawPairRight P k q χ G t.val.1.val else 0
  let V (s t : State) (π τ : Perms) :=
    giantTwoSidedPatternPhysicalCoefficient 1 q 0 (giantTwoSidedRawPatternCoefficient χ)
      (giantTwoSidedEndpointPermute π s) (giantTwoSidedEndpointPermute τ t)
      (giantTwoSidedRawEmptyAuxiliary P k) *
      R s.val.1.val (giantTwoSidedRawPrefixProduct (giantTwoSidedEndpointPermute π s).val.2) *
      star (f s.val.1.val) * g t
  have hentry (s t : State) :
      giantTwoSidedRawSlotEntry q 0 χ R s t * star (f s.val.1.val) * g t =
        a * ∑ π : Perms, ∑ τ : Perms, V s t π τ := by
    simp only [giantTwoSidedRawSlotEntry, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro π _
    apply Finset.sum_congr rfl
    intro τ _
    dsimp only [V, giantTwoSidedRawPatternEntry]
    change (a * (R s.val.1.val _ * _)) * star (f s.val.1.val) * g t = _
    ring
  have hswap :
      (∑ s : State, ∑ t : State, ∑ π : Perms, ∑ τ : Perms, V s t π τ) =
        ∑ π : Perms, ∑ τ : Perms, ∑ s : State, ∑ t : State, V s t π τ := by
    calc
      _ = ∑ z : State × State, ∑ p : Perms × Perms, V z.1 z.2 p.1 p.2 := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ p : Perms × Perms, ∑ z : State × State, V z.1 z.2 p.1 p.2 := Finset.sum_comm
      _ = _ := by simp only [Fintype.sum_prod_type]
  calc
    _ = σ * (∑ s : State, ∑ t : State, a * ∑ π : Perms, ∑ τ : Perms, V s t π τ) := by
      change σ * markedMatrixPairing (Matrix.of (fun s t : State => giantTwoSidedRawSlotEntry q 0 χ R s t))
        (fun s => f s.val.1.val) g = _
      simp only [markedMatrixPairing_expansion, Matrix.of_apply, hentry]
    _ = σ * a * ∑ π : Perms, ∑ τ : Perms, ∑ s : State, ∑ t : State, V s t π τ := by
      rw [mul_assoc, ← hswap]
      simp only [Finset.mul_sum]
    _ = _ := by
      unfold giantTwoSidedPhysicalPatternCutoffPairing
      simp only [raw_empty_auxiliary_sum, raw_empty_dilation]
      rfl

private theorem dirichlet_one_mod_one (z : ZMod 1) : (1 : DirichletCharacter ℂ 1) z = 1 := by
  rw [Subsingleton.elim z (1 : ZMod 1), map_one]

private theorem raw_coefficient_mod_one {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k Q : ℕ) (h ξ : ℝ) :
    giantTwoSidedRawPatternCoefficient (P := P) (k := k) (1 : DirichletCharacter ℂ 1) =
      idealResidualCoefficient P (k := k) (ell := 1) Q h ξ none := by
  funext a b aux
  simp only [giantTwoSidedRawPatternCoefficient, idealResidualCoefficient, dirichlet_one_mod_one, map_one]

theorem giantTwoSidedRawPhysical_sum_modOne_eq_residualRawCutoff {J : Type*} [Fintype J]
    [DecidableEq J] {P : J → Finset ℕ} {k : ℕ} {Z Z' U : Finset ℕ} (hZ : Z ⊆ U) (hZ' : Z' ⊆ U)
    (x q : ℝ) (Ψ : ℝ → ℂ) (F G L : ℕ → ℂ) (Q : ℕ) (h ξ : ℝ) :
    (∑ e : GiantTwoSidedRawPhysicalEdge P k Z Z',
      L e.val.1.val.1.val * giantTwoSidedRawPhysicalTerm x q Ψ (1 : DirichletCharacter ℂ 1) F G e) =
      giantTwoSidedPhysicalPatternCutoffPairing (P := P) (Z := U) (k := k) (ell := 1)
        (idealResidualCopied (none : IdealResidualPattern J k))
        1 q 0 (idealResidualCoefficient P Q h ξ none) Ψ x
        (fun n => if n ∈ Z then giantTwoSidedRawPairLeft P k q F L n else 0)
        (fun t => if t.val.1.val ∈ Z' then
          G t.val.1.val * (giantTwoSidedEndpointDamping P (k+1) q t.val.1.val : ℂ) else 0) := by
  let C := giantTwoSidedRawEmptyPattern J k
  let State := GiantTwoSidedEndpointState P (k+1) U
  let f (n : ℕ) := if n ∈ Z then giantTwoSidedRawPairLeft P k q F L n else 0
  let g₀ (t : State) := if t.val.1.val ∈ Z' then
    giantTwoSidedRawPairRight P k q (1 : DirichletCharacter ℂ 1) G t.val.1.val else 0
  let g₁ (t : State) := if t.val.1.val ∈ Z' then
    G t.val.1.val * (giantTwoSidedEndpointDamping P (k+1) q t.val.1.val : ℂ) else 0
  have hg : g₀ = g₁ := by
    funext t
    simp only [g₀, g₁, giantTwoSidedRawPairRight, dirichlet_one_mod_one, one_mul]
  let cutoff (K : GiantTwoSidedPatternCoefficient P C 1) (g : State → ℂ) :=
    giantTwoSidedPhysicalPatternCutoffPairing (Z := U) C 1 q 0 K Ψ x f g
  change _ = cutoff (idealResidualCoefficient P Q h ξ none) g₁
  calc
    _ = cutoff (giantTwoSidedRawPatternCoefficient (1 : DirichletCharacter ℂ 1)) g₀ :=
      giantTwoSidedRawPhysical_sum_eq_patternCutoffPairing hZ hZ' x q Ψ (1 : DirichletCharacter ℂ 1) F G L
    _ = _ := congrArg₂ cutoff (raw_coefficient_mod_one P k Q h ξ) hg

end
end ArtinMatthews
