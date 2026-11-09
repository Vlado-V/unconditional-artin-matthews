module

public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.IdealCharacterCells


set_option backward.privateInPublic true
@[expose] public section

/-! The source residual family consists of the raw pattern and every
nonempty pair of freed probe sets. The first comparison reads target
labels and the second reads input labels. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev IdealResidualPattern (J : Type*) (k : ℕ) :=
  Option (Finset (J × Fin k) × Finset (J × Fin k))

def idealResidualPatterns {J : Type*} [DecidableEq J] {k : ℕ}
    (probes₁ probes₂ : Finset (J × Fin k)) : Finset (IdealResidualPattern J k) :=
  {none} ∪ ((probes₁.powerset.erase ∅ ×ˢ probes₂.powerset.erase ∅).image some)

theorem idealResidualPatterns_raw {J : Type*} [DecidableEq J] {k : ℕ}
    (probes₁ probes₂ : Finset (J × Fin k)) :
    none∈idealResidualPatterns probes₁ probes₂ := mem_union_left _ (mem_singleton_self _)

theorem idealResidualPatterns_comparison {J : Type*} [DecidableEq J] {k : ℕ}
    (probes₁ probes₂ A B : Finset (J × Fin k)) :
    some (A,B)∈idealResidualPatterns probes₁ probes₂ ↔
      A∈probes₁.powerset.erase ∅ ∧ B∈probes₂.powerset.erase ∅ := by
  simp [idealResidualPatterns]

def idealResidualFreeSlots {J : Type*} [DecidableEq J] {k : ℕ}
    (S : Finset (J × Fin k)) (j : J) : Finset (Fin k) :=
  univ.filter (fun i => (j,i)∈S)

theorem mem_idealResidualFreeSlots {J : Type*} [DecidableEq J] {k : ℕ}
    (S : Finset (J × Fin k)) (j : J) (i : Fin k) :
    i∈idealResidualFreeSlots S j ↔ (j,i)∈S := by
  simp [idealResidualFreeSlots]

def idealResidualCopied {J : Type*} [DecidableEq J] {k : ℕ}
    (ν : IdealResidualPattern J k) : J → Finset (Fin k) :=
  match ν with
  | none => fun _ => ∅
  | some (A,B) => idealResidualFreeSlots (A ∪ B)

def idealResidualBands {J : Type*} {k : ℕ} (P : J → Finset ℕ)
    (S : Finset (J × Fin k)) : ↥S → Finset ℕ :=
  fun v => P v.val.1

def idealResidualSelectedMarking {J : Type*} {P : J → Finset ℕ} {k ell : ℕ}
    (S : Finset (J × Fin k)) (a : MarkedPhysicalMarking P (k+ell)) :
    IdealSelectedLabels (idealResidualBands P S) :=
  fun v => a v.val.1 (Fin.castAdd ell v.val.2)

def idealResidualSelectedAuxiliary {J : Type*} {P : J → Finset ℕ} {k : ℕ}
    {C : J → Finset (Fin k)} (S : Finset (J × Fin k))
    (hS : ∀ v∈S,v.2∈C v.1) (aux : GiantTwoSidedPatternAuxiliary P C) :
    IdealSelectedLabels (idealResidualBands P S) :=
  fun v => aux v.val.1 ⟨v.val.2,hS v.val v.property⟩

def idealResidualCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {k ell : ℕ} (Q : ℕ) (h ξ : ℝ)
    (ν : IdealResidualPattern J k) : GiantTwoSidedPatternCoefficient P (idealResidualCopied ν) ell :=
  match ν with
  | none => fun _ _ _ => 1
  | some (A,B) => fun a b aux =>
      -(-1:ℂ)^(A.card+B.card)*
        idealCharacterCellKernel (idealResidualBands P A) Q h ξ
          (idealResidualSelectedAuxiliary A
            (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_left B hv)) aux)
          (idealResidualSelectedMarking A b)*
        idealCharacterCellKernel (idealResidualBands P B) Q h ξ
          (idealResidualSelectedAuxiliary B
            (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_right A hv)) aux)
          (idealResidualSelectedMarking B a)

def idealResidualOperator {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {k ell : ℕ} (probes₁ probes₂ : Finset (J × Fin k))
    (Q : ℕ) (h ξ Θ ζ : ℝ) (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    MarkedPhysicalMarking P (k+ell) → ℂ :=
  idealOperator (idealResidualPatterns probes₁ probes₂) idealResidualCopied Θ ζ
    (idealResidualCoefficient P Q h ξ) f

theorem idealResidualCoefficient_raw {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {k ell : ℕ} (Q : ℕ) (h ξ : ℝ)
    (a b : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualCopied (none : IdealResidualPattern J k))) :
    idealResidualCoefficient P Q h ξ none a b aux=1 := rfl

theorem idealResidualCoefficient_norm {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {k ell : ℕ} (Q : ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (ν : IdealResidualPattern J k) (a b : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualCopied ν)) :
    ‖idealResidualCoefficient P Q h ξ ν a b aux‖ ≤ 1+((Q:ℝ)^2/ξ)^2 := by
  cases ν with
  | none =>
    simp only [idealResidualCoefficient,norm_one]
    exact le_add_of_nonneg_right (sq_nonneg _)
  | some pair =>
    rcases pair with ⟨A,B⟩
    simp only [idealResidualCoefficient,norm_mul,norm_neg,norm_pow,norm_one,one_pow,one_mul]
    have hA := idealCharacterCellKernel_norm_le (idealResidualBands P A) Q h hξ
      (idealResidualSelectedAuxiliary A
        (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_left B hv)) aux)
      (idealResidualSelectedMarking A b)
    have hB := idealCharacterCellKernel_norm_le (idealResidualBands P B) Q h hξ
      (idealResidualSelectedAuxiliary B
        (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_right A hv)) aux)
      (idealResidualSelectedMarking B a)
    calc
      _ ≤ ((Q:ℝ)^2/ξ)*((Q:ℝ)^2/ξ) :=
        mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith

end
end ArtinMatthews
